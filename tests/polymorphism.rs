use std::{
    collections::HashSet,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

mod support;

use ash::{
    core::{
        EffectExprKind, EffectOperation, EffectOperationFamily, PureComputation, PureExprKind,
        ValidatedEffectProgram,
        dialect::CoreOperationFamily,
        transform::{fold_effect_literal_primitives, identity_effect_traversal},
        validate_effect_modules,
    },
    driver::PipelineFailure,
    elaborate::{EffectElaborator, check_module, link_modules},
    eval::{RuntimeFailure, TraceEvent, Value, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    module::{ModuleId, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
    source::{SourceFile, SourceId},
    types::{ComputationType, EffectRow, EffectRowVariable, Kind, Type, TypeVariableId},
};
use support::run_module;

static CORE_TEMP_IDS: AtomicU64 = AtomicU64::new(0);

#[test]
fn rank_one_schemes_retain_row_kind_binders_in_latent_computations() {
    let binder = TypeVariableId::new(77);
    let scheme = Type::Forall(
        Box::new([(binder, Kind::EffectRow)]),
        Box::new(Type::function_computation(
            Type::Unit,
            ComputationType::new(
                Type::Int,
                EffectRow::open(EffectRowVariable::rigid(binder), Box::new([])),
            ),
        )),
    );

    assert_eq!(scheme, scheme.clone());
    assert!(scheme.to_string().contains("EffectRow"));
    assert!(scheme.to_string().contains("<row-variable:generated:77>"));
}

fn run(text: &str) -> ash::driver::Observation {
    run_module("polymorphism.ash", text).expect("fixture should run")
}

#[test]
fn observation_parts_have_a_public_iterative_type_disposal_path() {
    let observation = run("main : Unit -> Int\nmain () = 42\n");
    let parts = observation.into_parts();

    assert_eq!(parts.value_display(), "42");
    assert_eq!(parts.type_display(), "Int");
    let (value, ty) = parts.into_pair();
    assert_eq!(value.to_string(), "42");
    assert_eq!(ty.to_string(), "Int");
    ash::types::discard_type_iteratively(ty);
}

fn reason(text: &str) -> String {
    let failure: PipelineFailure =
        run_module("polymorphism-rejection.ash", text).expect_err("fixture should be rejected");
    failure.reason_code()
}

struct EffectCore {
    program: ValidatedEffectProgram,
    sources: Vec<SourceFile>,
    module_sources: Vec<(ModuleId, SourceId)>,
    binders: Vec<(String, ash::resolved::BinderId)>,
    implementation_methods: Vec<ash::resolved::BinderId>,
}

fn elaborated_effect(text: &str) -> EffectCore {
    let directory = loop {
        let id = CORE_TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-polymorphic-core-{}-{id}", std::process::id()));
        match fs::create_dir(&path) {
            Ok(()) => break path,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("Core fixture directory should be creatable: {error}"),
        }
    };
    let entry_path: PathBuf = directory.join("polymorphic-core.ash");
    fs::write(&entry_path, text).expect("Core fixture should be writable");
    let graph = load_module_graph(&entry_path, &ModuleRoots::empty())
        .expect("Core fixture graph should load");
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let target = checked
                    .iter()
                    .find(|candidate| candidate.module() == edge.target())
                    .expect("dependency order should retain the target first");
                DependencyExports::new(edge, target.exports())
                    .expect("exact dependency exports should authenticate")
            })
            .collect::<Vec<_>>();
        let resolved =
            resolve_module(module, &dependencies).expect("source component should resolve");
        checked.push(check_module(resolved).expect("source component should check"));
    }
    let entry = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .unwrap();
    let binders = entry
        .schemes()
        .iter()
        .map(|scheme| (scheme.spelling.to_string(), scheme.binder))
        .collect();
    let implementation_methods = entry
        .implementation_facts()
        .iter()
        .flat_map(|implementation| implementation.methods.iter().map(|method| method.binder))
        .collect();
    let linked =
        link_modules(checked, graph.entry()).expect("complete source component should link");
    let linked = validate_interface_evidence(linked).expect("linked evidence should validate");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("Core namespace should fit");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("source should elaborate");
    let unchecked = elaborator.finish(typed.node).expect("Core should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source().clone())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let source_refs = sources.iter().collect::<Vec<_>>();
    let program = validate_effect_modules(unchecked, &source_refs, &module_sources)
        .expect("complete source Core should independently validate");
    let _ = fs::remove_dir_all(directory);
    EffectCore {
        program,
        sources,
        module_sources,
        binders,
        implementation_methods,
    }
}

fn runtime_class(program: &ValidatedEffectProgram, event: &TraceEvent) -> &'static str {
    let TraceEvent::Enter(id) = event;
    match &program
        .node(*id)
        .expect("an entered Core node should exist")
        .kind
    {
        EffectExprKind::Pure(kind) => match kind {
            PureExprKind::Value(ash::core::PureValue::String(_)) => "string",
            PureExprKind::Value(ash::core::PureValue::Intrinsic(_)) => "intrinsic",
            PureExprKind::Value(ash::core::PureValue::Integer(_)) => "integer",
            PureExprKind::Value(ash::core::PureValue::Boolean(_)) => "boolean",
            PureExprKind::Value(ash::core::PureValue::Unit(_)) => "unit",
            PureExprKind::Value(ash::core::PureValue::Function(_)) => "function",
            PureExprKind::Value(ash::core::PureValue::Constructor(_)) => "constructor",
            PureExprKind::Variable(_) => "variable-lookup",
            PureExprKind::Computation(PureComputation::Bind(_)) => "bind",
            PureExprKind::Computation(PureComputation::RecursiveBind(_)) => "recursive-bind",
            PureExprKind::Computation(PureComputation::Apply(_)) => "apply",
            PureExprKind::Computation(PureComputation::Primitive(_)) => "primitive",
            PureExprKind::Computation(PureComputation::Tuple(_)) => "tuple",
            PureExprKind::Computation(PureComputation::Match(_)) => "match",
            PureExprKind::Computation(PureComputation::NewtypeConversion(_)) => {
                "newtype-conversion-erasure"
            }
            PureExprKind::Computation(PureComputation::LocalNominalScope(_)) => {
                "local-nominal-scope-erasure"
            }
            PureExprKind::Computation(PureComputation::TypeAbstraction(_)) => {
                "type-abstraction-erasure"
            }
            PureExprKind::Computation(PureComputation::TypeApplication(_)) => {
                "type-application-erasure"
            }
        },
        EffectExprKind::Operation(EffectOperation::NativeInterpret(_)) => "native-interpret",
        EffectExprKind::Operation(EffectOperation::Cleanup(_)) => "cleanup",
        EffectExprKind::Operation(EffectOperation::Registration(_)) => "registration",
        EffectExprKind::Operation(EffectOperation::Resource(_)) => "resource",
        EffectExprKind::Operation(EffectOperation::Store(_)) => "store",
        EffectExprKind::Operation(EffectOperation::Continue(_)) => "continue",
        EffectExprKind::Operation(EffectOperation::RetainedRoot(_)) => "retained-root",
        EffectExprKind::Operation(EffectOperation::Retain(_)) => "retain",
        EffectExprKind::Operation(EffectOperation::Region(_)) => "region",
        EffectExprKind::Operation(EffectOperation::RegionAllocate(_)) => "region-allocate",
        EffectExprKind::Operation(EffectOperation::RegionValueRequest(_)) => "region-value-request",
        EffectExprKind::Operation(EffectOperation::RegionBuffer(_)) => "region-buffer",
        EffectExprKind::Operation(EffectOperation::RegionTuple(_)) => "region-tuple",
        EffectExprKind::Operation(EffectOperation::RegionClosure(_)) => "region-closure",
        EffectExprKind::Operation(EffectOperation::Request(_)) => "request",
        EffectExprKind::Operation(EffectOperation::Handler(_)) => "handler",
        EffectExprKind::Operation(EffectOperation::Resume(_)) => "resume",
        EffectExprKind::Operation(EffectOperation::Discard(_)) => "discard",
    }
}

fn runtime_value_class(value: &Value) -> &'static str {
    match value {
        Value::ResourceHandle(_) => "resource-handle",
        Value::RetainedKey(_) => "retained-key",
        Value::RegionRequest(_) => "region-request",
        Value::RegionStorage(_) => "region-storage",
        Value::RegionBackingFunction(_) => "region-backing-function",
        Value::RegionView(_) => "region-view",
        Value::RegionHostFunction { .. } => "region-host-function",
        Value::ConstructorTag(_) => "constructor-tag",
        Value::Bytes(_) => "bytes",
        Value::Address(_) => "address",
        Value::String(_) => "string",
        Value::Intrinsic(_) => "intrinsic",
        Value::Integer(_) | Value::SmallInteger(_) | Value::RegionInteger { .. } => "integer",
        Value::Boolean(_) => "boolean",
        Value::Unit => "unit",
        Value::Function(_) | Value::RegionFunction(_) => "function",
        Value::ClosureCode(_) => "private-closure-code",
        Value::Polymorphic { .. } => "function",
        Value::ConstructorFunction(_) => "constructor-function",
        Value::Location(_) => "location",
        Value::Data(_) => "data",
    }
}

const fn runtime_failure_class(failure: RuntimeFailure) -> &'static str {
    match failure {
        RuntimeFailure::Report(report) => report.primary.reason_code(),
        RuntimeFailure::MissingNode => "runtime.missing-node",
        RuntimeFailure::UnexpectedPrimitiveValue => "runtime.unexpected-primitive-value",
        RuntimeFailure::UnexpectedFunctionValue => "runtime.unexpected-function-value",
        RuntimeFailure::MissingBinding => "runtime.missing-binding",
        RuntimeFailure::UnexpectedRecursiveBinding => "runtime.unexpected-recursive-binding",
        RuntimeFailure::EnvironmentCapacity => "runtime.environment-capacity",
        RuntimeFailure::InvalidControlState => "runtime.invalid-control-state",
        RuntimeFailure::ForeignBinding => "runtime.foreign-binding",
        RuntimeFailure::HeapCapacity => "runtime.heap-capacity",
        RuntimeFailure::CapturedControlCapacity => "runtime.captured-control-capacity",
        RuntimeFailure::ResourceCapacity => "runtime.resource-capacity",
        RuntimeFailure::InvalidLocation => "runtime.invalid-location",
        RuntimeFailure::UninitializedLocation => "runtime.uninitialized-location",
        RuntimeFailure::AliasLoop => "runtime.alias-loop",
        RuntimeFailure::ImpossibleMatch => "runtime.impossible-match",
    }
}

fn assert_type_operations_enter_only_their_retained_child(
    program: &ValidatedEffectProgram,
    trace: &[TraceEvent],
    forwarded_adapter: Option<(ash::core::NodeId, ash::core::NodeId, ash::core::NodeId)>,
) {
    for pair in trace.windows(2) {
        let [TraceEvent::Enter(current), TraceEvent::Enter(next)] = pair else {
            unreachable!("the evaluator trace has one public event form")
        };
        let expected = match &program
            .node(*current)
            .expect("an entered type operation should exist")
            .kind
        {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
                operation,
            ))) => {
                if let Some((adapter, type_application, implementation_variable)) =
                    forwarded_adapter
                    && *current == adapter
                {
                    assert_eq!(operation.body(), type_application);
                    let EffectExprKind::Pure(PureExprKind::Computation(
                        PureComputation::TypeApplication(application),
                    )) = &program.node(type_application).unwrap().kind
                    else {
                        panic!(
                            "the known adapter should forward its exact concrete type application"
                        );
                    };
                    assert_eq!(application.function(), implementation_variable);
                    assert_eq!(
                        operation
                            .parameters()
                            .iter()
                            .map(|(_, kind)| kind.clone())
                            .collect::<Vec<_>>(),
                        vec![Kind::Type, Kind::Type]
                    );
                    assert_eq!(
                        application.arguments(),
                        &operation
                            .parameters()
                            .iter()
                            .map(|(id, _)| Type::Variable(*id))
                            .collect::<Vec<_>>()
                    );
                    assert!(application.row_arguments().is_empty());
                    Some(implementation_variable)
                } else {
                    Some(operation.body())
                }
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                operation,
            ))) => Some(operation.function()),
            EffectExprKind::Pure(PureExprKind::Computation(
                PureComputation::NewtypeConversion(operation),
            )) => Some(operation.child()),
            _ => None,
        };
        if let Some(expected) = expected {
            assert_eq!(*next, expected);
        }
    }
}

fn owned_core_nodes(
    program: &ValidatedEffectProgram,
    root: ash::core::NodeId,
) -> Vec<ash::core::NodeId> {
    let mut visited = HashSet::new();
    let mut pending = vec![root];
    let mut nodes = Vec::new();
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }
        let node = program
            .node(id)
            .expect("every reachable Core node should belong to the program");
        pending.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
        nodes.push(id);
    }
    nodes
}

#[test]
fn source_instantiation_is_explicit_in_validated_core() {
    let fixture = elaborated_effect(
        "id : A -> A\nid value = value\n\nmain : Unit -> Int\nmain () = id(42)\n",
    );
    let program = &fixture.program;
    let id_binder = fixture
        .binders
        .iter()
        .find(|(name, _)| name == "id")
        .unwrap()
        .1;
    let mut id_initializers = 0;
    let mut id_instantiations = 0;
    let mut work = vec![program.root()];
    let mut abstractions = 0;
    let mut applications = 0;
    while let Some(id) = work.pop() {
        let node = program.node(id).expect("validated node");
        match &node.kind {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
                operation,
            ))) => {
                abstractions += 1;
                work.push(operation.body());
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                operation,
            ))) => {
                if matches!(&program.node(operation.function()).unwrap().kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == id_binder)
                {
                    assert_eq!(operation.arguments(), &[Type::Int]);
                    assert!(operation.row_arguments().is_empty());
                    id_instantiations += 1;
                }
                applications += 1;
                work.push(operation.function());
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) => {
                for member in group
                    .members()
                    .iter()
                    .filter(|member| member.binder().id() == id_binder)
                {
                    let EffectExprKind::Pure(PureExprKind::Computation(
                        PureComputation::TypeAbstraction(abstraction),
                    )) = &program.node(member.initializer()).unwrap().kind
                    else {
                        panic!("the source id initializer should retain its type abstraction");
                    };
                    assert_eq!(abstraction.parameters().len(), 1);
                    assert_eq!(abstraction.parameters()[0].1, Kind::Type);
                    id_initializers += 1;
                }
                for index in 0..node.kind.child_count() {
                    work.push(node.kind.child_at(index).unwrap());
                }
            }
            kind => {
                for index in 0..kind.child_count() {
                    work.push(kind.child_at(index).expect("validated child"));
                }
            }
        }
    }
    assert_eq!(id_initializers, 1);
    assert_eq!(id_instantiations, 1);
    assert!(abstractions >= 1);
    assert!(applications >= 1);
}

#[test]
fn explicit_type_operations_survive_both_core_transforms_and_erasure() {
    let fixture = elaborated_effect(
        "id : A -> A\nid value = value\n\nmain : Unit -> Int\nmain () = id(40 + 2)\n",
    );
    let before = &fixture.program;
    for transformed in [
        identity_effect_traversal(before).expect("identity traversal"),
        fold_effect_literal_primitives(before).expect("literal folding"),
    ] {
        let transformed = validate_effect_modules(
            transformed,
            &fixture.sources.iter().collect::<Vec<_>>(),
            &fixture.module_sources,
        )
        .expect("transformed Core validates");
        assert_eq!(
            evaluate_effect(&transformed)
                .expect("transformed Core evaluates")
                .value
                .to_string(),
            "42"
        );
    }
}

#[test]
fn core_transforms_preserve_the_canonical_result_application_tree() {
    let fixture = elaborated_effect(concat!(
        "type Wrapped<A> =\nWrapped(A)\n\n",
        "main : Unit -> Wrapped<Int>\n",
        "main () = Wrapped(40 + 2)\n",
    ));
    let before = &fixture.program;
    let before_type = before
        .node(before.root())
        .expect("the validated root should exist")
        .ty
        .clone();
    assert!(matches!(before_type, ash::types::Type::Application(_, _)));

    for transformed in [
        identity_effect_traversal(before).expect("identity traversal"),
        fold_effect_literal_primitives(before).expect("literal folding"),
    ] {
        let transformed = validate_effect_modules(
            transformed,
            &fixture.sources.iter().collect::<Vec<_>>(),
            &fixture.module_sources,
        )
        .expect("transformed Core validates");
        assert!(ash::types::same_type(
            &transformed
                .node(transformed.root())
                .expect("the transformed root should exist")
                .ty,
            &before_type,
        ));
        assert_eq!(
            evaluate_effect(&transformed)
                .expect("transformed Core evaluates")
                .value
                .to_string(),
            "Wrapped(42)",
        );
    }
}

#[test]
fn implicitly_quantified_global_instantiates_at_unrelated_types() {
    let observation = run(
        "id : A -> A\nid value = value\n\nmain : Unit -> (Int, Bool)\nmain () = (id(42), id(true))\n",
    );

    assert_eq!(observation.value_display(), "(42, true)");
    assert_eq!(observation.type_display(), "(Int, Bool)");
}

#[test]
fn polymorphic_global_instantiates_freshly_inside_another_global() {
    let observation = run(
        "id : A -> A\nid value = value\n\nrelay : B -> B\nrelay value = id value\n\nmain : Unit -> Bool\nmain () = relay(true)\n",
    );

    assert_eq!(observation.value_display(), "true");
    assert_eq!(observation.type_display(), "Bool");
}

#[test]
fn higher_kinded_instantiation_preserves_fixed_kinds() {
    let source = concat!(
        "type Pair<A, B> = Pair(A, B)\n\n",
        "keep<F : Type -> Type, A> : F<A> -> F<A>\n",
        "keep value = value\n\n",
        "main : Unit -> Pair<Int, Bool>\n",
        "main () = keep(Pair(42, true))\n",
    );
    let fixture = elaborated_effect(source);
    let program = &fixture.program;
    let observation = run(source);
    assert_eq!(observation.value_display(), "Pair(42, true)");
    assert_eq!(observation.type_display(), "Pair<Int, Bool>");

    let keep_binder = fixture
        .binders
        .iter()
        .find(|(name, _)| name == "keep")
        .unwrap()
        .1;
    let pair_ids = program
        .registry()
        .nominals()
        .iter()
        .filter(|nominal| {
            nominal.spelling == "Pair" && nominal.id.module() == keep_binder.module().unwrap()
        })
        .map(|nominal| nominal.id)
        .collect::<Vec<_>>();
    let [pair_id] = pair_ids.as_slice() else {
        panic!("the entry should retain its unique Pair identity");
    };
    let mut work = vec![program.root()];
    let mut found_partial_constructor = false;
    while let Some(id) = work.pop() {
        let node = program.node(id).expect("validated node");
        if let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
            operation,
        ))) = &node.kind
        {
            if let EffectExprKind::Pure(PureExprKind::Variable(variable)) =
                &program.node(operation.function()).unwrap().kind
                && variable.binder() == keep_binder
            {
                assert_eq!(
                    operation.arguments(),
                    &[
                        Type::Application(Box::new(Type::Nominal(*pair_id)), Box::new(Type::Int)),
                        Type::Bool,
                    ]
                );
                assert!(operation.row_arguments().is_empty());
                let Type::Forall(parameters, _) = &program.node(operation.function()).unwrap().ty
                else {
                    panic!("the original keep callee should retain its quantified kinds");
                };
                assert_eq!(
                    parameters
                        .iter()
                        .map(|(_, kind)| kind.clone())
                        .collect::<Vec<_>>(),
                    vec![
                        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                        Kind::Type
                    ]
                );
                found_partial_constructor = true;
            }
            work.push(operation.function());
        } else {
            for index in 0..node.kind.child_count() {
                work.push(node.kind.child_at(index).expect("validated child"));
            }
        }
    }
    assert!(
        found_partial_constructor,
        "the higher-kinded argument should zonk to the partial Pair<Int> constructor"
    );
}

#[test]
fn higher_kinded_type_operations_add_only_existing_erasure_entries() {
    fn core_abstraction_count(program: &ValidatedEffectProgram) -> usize {
        let mut visited = std::collections::HashSet::new();
        let mut work = vec![program.root()];
        let mut count = 0;
        while let Some(id) = work.pop() {
            if !visited.insert(id) {
                continue;
            }
            let node = program
                .node(id)
                .expect("a reachable Core abstraction candidate should exist");
            count += usize::from(matches!(
                node.kind,
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
                    _
                )))
            ));
            work.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
        }
        count
    }

    let shared_declarations = "type Pair<A, B> = Pair(A, B)\n\n";
    let monomorphic_source = format!(
        "{shared_declarations}keep : Pair<Int, Bool> -> Pair<Int, Bool>\nkeep value = value\n\nmain : Unit -> Pair<Int, Bool>\nmain () = keep(Pair(42, true))\n",
    );
    let higher_kinded_source = format!(
        "{shared_declarations}keep<F : Type -> Type, A> : F<A> -> F<A>\nkeep value = value\n\nmain : Unit -> Pair<Int, Bool>\nmain () = keep(Pair(42, true))\n",
    );
    let monomorphic_fixture = elaborated_effect(&monomorphic_source);
    let monomorphic = monomorphic_fixture.program;
    let higher_kinded_fixture = elaborated_effect(&higher_kinded_source);
    let higher_kinded = higher_kinded_fixture.program;
    let monomorphic_evaluation =
        evaluate_effect(&monomorphic).expect("the monomorphic comparison Core should evaluate");
    let higher_kinded_evaluation =
        evaluate_effect(&higher_kinded).expect("the higher-kinded comparison Core should evaluate");

    assert_eq!(monomorphic_evaluation.value.to_string(), "Pair(42, true)");
    assert_eq!(
        higher_kinded_evaluation.value.to_string(),
        monomorphic_evaluation.value.to_string(),
    );
    assert_eq!(
        higher_kinded_evaluation.max_frame_depth, monomorphic_evaluation.max_frame_depth,
        "higher kinds must not increase this paired fixture’s frame high-water mark",
    );
    assert_type_operations_enter_only_their_retained_child(
        &higher_kinded,
        &higher_kinded_evaluation.trace,
        None,
    );

    let monomorphic_classes = monomorphic_evaluation
        .trace
        .iter()
        .map(|event| runtime_class(&monomorphic, event))
        .collect::<Vec<_>>();
    let higher_kinded_classes = higher_kinded_evaluation
        .trace
        .iter()
        .map(|event| runtime_class(&higher_kinded, event))
        .collect::<Vec<_>>();
    let retained_runtime = |classes: &[&'static str]| {
        classes
            .iter()
            .copied()
            .filter(|class| !class.ends_with("-erasure"))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        retained_runtime(&higher_kinded_classes),
        retained_runtime(&monomorphic_classes),
        "higher kinds add no value form, lookup, frame, or non-erasure transition",
    );
    assert_eq!(
        higher_kinded_classes
            .iter()
            .filter(|class| **class == "variable-lookup")
            .count(),
        monomorphic_classes
            .iter()
            .filter(|class| **class == "variable-lookup")
            .count(),
    );
    assert_eq!(
        higher_kinded_evaluation.trace.len(),
        monomorphic_evaluation.trace.len() + 2,
        "generic record creation enters its abstraction once and its call enters one type application",
    );
    assert_eq!(
        core_abstraction_count(&higher_kinded),
        core_abstraction_count(&monomorphic) + 1,
        "the higher-kinded global should retain one additional static abstraction",
    );
    assert_eq!(
        higher_kinded_classes
            .iter()
            .filter(|class| **class == "type-abstraction-erasure")
            .count(),
        monomorphic_classes
            .iter()
            .filter(|class| **class == "type-abstraction-erasure")
            .count()
            + 1,
        "the generic callable record is created once at abstraction evaluation",
    );
    assert_eq!(
        higher_kinded_classes
            .iter()
            .filter(|class| **class == "type-application-erasure")
            .count(),
        monomorphic_classes
            .iter()
            .filter(|class| **class == "type-application-erasure")
            .count()
            + 1,
    );
}

#[test]
fn polymorphic_method_evidence_uses_only_the_existing_runtime_inventory() {
    let source = concat!(
        "interface Functor<F : Type -> Type> {\n",
        "map<A, B> : (A -> B, F<A>) -> F<B>\n",
        "}\n\n",
        "type Box<A> = Box(A)\n\n",
        "impl Functor<Box> {\n",
        "map (function, Box(value)) = Box(function(value))\n",
        "}\n\n",
        "to_bool : Int -> Bool\n",
        "to_bool value = value == 42\n\n",
        "to_int : Bool -> Int\n",
        "to_int true = 42\n",
        "to_int false = 0\n\n",
        "map_pair<F : Type -> Type> : (F<Int>, F<Bool>) -> (F<Bool>, F<Int>) where Functor<F>\n",
        "map_pair (numbers, flags) = (map((to_bool, numbers)), map((to_int, flags)))\n\n",
        "main : Unit -> (Box<Bool>, Box<Int>)\n",
        "main () = map_pair((Box(42), Box(true)))\n",
    );
    let fixture = elaborated_effect(source);
    let program = &fixture.program;
    let [implementation_method] = fixture.implementation_methods.as_slice() else {
        panic!("the source should retain one concrete method binder");
    };
    let reachable = owned_core_nodes(program, program.root());
    let recursive_initializers = reachable
        .iter()
        .filter_map(|id| {
            let node = program.node(*id)?;
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) = &node.kind
            else {
                return None;
            };
            Some(
                group
                    .members()
                    .iter()
                    .map(|member| member.initializer())
                    .collect::<Vec<_>>(),
            )
        })
        .flatten()
        .collect::<HashSet<_>>();
    let adapters = reachable
        .iter()
        .copied()
        .filter(|id| {
            !recursive_initializers.contains(id)
                && matches!(
                    program.node(*id).map(|node| &node.kind),
                    Some(EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
                        abstraction
                    )))) if abstraction.parameters().len() == 2
                )
        })
        .collect::<Vec<_>>();
    let [adapter] = adapters.as_slice() else {
        panic!("one selected concrete method should produce one erased adapter");
    };
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
        adapter_abstraction,
    ))) = &program
        .node(*adapter)
        .expect("the adapter should remain reachable")
        .kind
    else {
        unreachable!("the selected adapter is a type abstraction");
    };
    let adapter_applications = owned_core_nodes(program, adapter_abstraction.body()).into_iter().filter(|id| {
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(application))) = &program.node(*id).unwrap().kind else { return false; };
        matches!(&program.node(application.function()).unwrap().kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == *implementation_method)
    }).collect::<Vec<_>>();
    let [adapter_type_application] = adapter_applications.as_slice() else {
        panic!("the adapter should retain one exact concrete method instantiation");
    };
    let adapter_type_application = *adapter_type_application;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
        adapter_application,
    ))) = &program.node(adapter_type_application).unwrap().kind
    else {
        unreachable!();
    };
    let implementation_variable = adapter_application.function();
    assert!(matches!(
        program.node(implementation_variable).map(|node| &node.kind),
        Some(EffectExprKind::Pure(PureExprKind::Variable(variable))) if variable.binder() == *implementation_method
    ));

    let map_pair = fixture
        .binders
        .iter()
        .find(|(name, _)| name == "map_pair")
        .unwrap()
        .1;
    let initializers = reachable
        .iter()
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) = &program.node(*id)?.kind
            else {
                return None;
            };
            group
                .members()
                .iter()
                .find(|member| member.binder().id() == map_pair)
                .map(|member| member.initializer())
        })
        .collect::<Vec<_>>();
    let [map_initializer] = initializers.as_slice() else {
        panic!("map_pair should retain one owned initializer");
    };
    let evidence_binders = owned_core_nodes(program, *map_initializer)
        .into_iter()
        .flat_map(|id| {
            let node = program.node(id).unwrap();
            let mut binders = Vec::new();
            EffectOperationFamily::visit_operation_binders(&node.kind, &mut |parameter| {
                if matches!(parameter.ty(), Type::Forall(parameters, _) if parameters.len() == 2) {
                    binders.push(parameter.id());
                }
            });
            binders
        })
        .collect::<Vec<_>>();
    let [evidence_binder] = evidence_binders.as_slice() else {
        panic!("the constrained global should own one ordinary polymorphic evidence binder");
    };
    let mut instantiations = Vec::new();
    for type_application in reachable.iter().copied() {
        let Some(node) = program.node(type_application) else {
            continue;
        };
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
            application,
        ))) = &node.kind
        else {
            continue;
        };
        let Some(function) = program.node(application.function()) else {
            continue;
        };
        let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &function.kind else {
            continue;
        };
        if variable.binder() != *evidence_binder {
            continue;
        }
        let strict_application = reachable
            .iter()
            .copied()
            .find(|candidate| {
                matches!(
                    program.node(*candidate).map(|node| &node.kind),
                    Some(EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))))
                        if application.function() == type_application
                )
            })
            .expect("each method instantiation should flow through ordinary strict application");
        instantiations.push((
            application.arguments().to_vec(),
            strict_application,
            type_application,
            application.function(),
        ));
    }
    instantiations.sort_by_key(|(arguments, _, _, _)| {
        usize::from(arguments.as_slice() == [ash::types::Type::Bool, ash::types::Type::Int])
    });
    let [int_to_bool, bool_to_int] = instantiations.as_slice() else {
        panic!("the method evidence binder should be instantiated exactly twice");
    };
    assert_eq!(
        int_to_bool.0,
        [ash::types::Type::Int, ash::types::Type::Bool]
    );
    assert_eq!(
        bool_to_int.0,
        [ash::types::Type::Bool, ash::types::Type::Int]
    );

    let main_binder = fixture
        .binders
        .iter()
        .find(|(name, _)| name == "main")
        .unwrap()
        .1;
    let main_initializers = reachable
        .iter()
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) = &program.node(*id)?.kind
            else {
                return None;
            };
            group
                .members()
                .iter()
                .find(|member| member.binder().id() == main_binder)
                .map(|member| member.initializer())
        })
        .collect::<Vec<_>>();
    let [main_initializer] = main_initializers.as_slice() else {
        panic!("main should retain one owned initializer");
    };
    let main_type = &program.node(*main_initializer).unwrap().ty;
    let main_closures = owned_core_nodes(program, *main_initializer)
        .into_iter()
        .filter(|id| {
            let node = program.node(*id).unwrap();
            node.ty == *main_type
                && matches!(
                    node.kind,
                    EffectExprKind::Operation(EffectOperation::RegionClosure(_))
                )
        })
        .collect::<Vec<_>>();
    let [main_closure] = main_closures.as_slice() else {
        panic!("main should own one fulltyped stored closure");
    };
    assert!(
        (0..program.node(*main_closure).unwrap().kind.child_count()).any(|index| program
            .node(*main_closure)
            .unwrap()
            .kind
            .child_at(index)
            == Some(implementation_variable))
    );
    let Type::Forall(_, evidence_type) = &program.node(*map_initializer).unwrap().ty else {
        panic!("map_pair should retain its outer scheme");
    };
    let source_type = evidence_type.function_view().unwrap().value();
    let source_closures = owned_core_nodes(program, *map_initializer)
        .into_iter()
        .filter(|id| {
            let node = program.node(*id).unwrap();
            node.ty == *source_type
                && matches!(
                    node.kind,
                    EffectExprKind::Operation(EffectOperation::RegionClosure(_))
                )
        })
        .collect::<Vec<_>>();
    let [source_closure] = source_closures.as_slice() else {
        panic!("map_pair should own one fulltyped inner source closure");
    };
    assert!(
        (0..program.node(*source_closure).unwrap().kind.child_count()).any(|index| program
            .node(*source_closure)
            .unwrap()
            .kind
            .child_at(index)
            == Some(int_to_bool.3))
    );

    let evaluation = evaluate_effect(program).expect("polymorphic method evidence should erase");
    assert_eq!(evaluation.value.to_string(), "(Box(true), Box(42))");
    assert_eq!(runtime_value_class(&evaluation.value), "data");
    // This Source program includes root handling, stored closures and strict captures.
    // The complete Effect depth is 24; 25% reserve rounded to 32 is a whole-run sanity bound.
    assert!(
        evaluation.max_frame_depth <= 32,
        "whole Effect evaluation should remain bounded: {}",
        evaluation.max_frame_depth
    );
    assert_type_operations_enter_only_their_retained_child(
        program,
        &evaluation.trace,
        Some((*adapter, adapter_type_application, implementation_variable)),
    );
    let evidence_nodes = [
        *adapter,
        adapter_type_application,
        implementation_variable,
        int_to_bool.1,
        int_to_bool.2,
        int_to_bool.3,
        bool_to_int.1,
        bool_to_int.2,
        bool_to_int.3,
    ];
    let entered_evidence = evaluation
        .trace
        .iter()
        .filter(|event| {
            let TraceEvent::Enter(node) = event;
            evidence_nodes.contains(node)
        })
        .collect::<Vec<_>>();
    // Keep all nine identities, including the metadata-only concrete type application.
    // Main captures its method before entry; the inner source function captures evidence
    // before its strict calls. The adapter forwards an immutable view without Enter(its body).
    assert_eq!(
        entered_evidence
            .iter()
            .map(|event| {
                let TraceEvent::Enter(id) = event;
                *id
            })
            .collect::<Vec<_>>(),
        [
            implementation_variable,
            *adapter,
            implementation_variable,
            int_to_bool.3,
            int_to_bool.1,
            int_to_bool.2,
            int_to_bool.3,
            bool_to_int.1,
            bool_to_int.2,
            bool_to_int.3
        ]
    );
    assert_eq!(
        entered_evidence
            .iter()
            .map(|event| runtime_class(program, event))
            .collect::<Vec<_>>(),
        [
            "variable-lookup",
            "type-abstraction-erasure",
            "variable-lookup",
            "variable-lookup",
            "apply",
            "type-application-erasure",
            "variable-lookup",
            "apply",
            "type-application-erasure",
            "variable-lookup",
        ],
        "the evidence trace should contain only existing erasure, lookup, and strict-application transitions",
    );

    let classes = evaluation
        .trace
        .iter()
        .map(|event| runtime_class(program, event))
        .collect::<Vec<_>>();
    assert!(classes.contains(&"recursive-bind"));
    let failures = [
        RuntimeFailure::MissingNode,
        RuntimeFailure::UnexpectedPrimitiveValue,
        RuntimeFailure::UnexpectedFunctionValue,
        RuntimeFailure::MissingBinding,
        RuntimeFailure::UnexpectedRecursiveBinding,
        RuntimeFailure::EnvironmentCapacity,
        RuntimeFailure::InvalidControlState,
        RuntimeFailure::ForeignBinding,
        RuntimeFailure::HeapCapacity,
        RuntimeFailure::CapturedControlCapacity,
        RuntimeFailure::InvalidLocation,
        RuntimeFailure::UninitializedLocation,
        RuntimeFailure::AliasLoop,
        RuntimeFailure::ImpossibleMatch,
    ];
    assert!(
        failures
            .iter()
            .all(|failure| runtime_failure_class(*failure) == failure.reason_code())
    );
}

#[test]
fn dependent_only_global_binder_lowers_complete_abstract_evidence() {
    let observation = run(concat!(
        "interface Iterator<I, Item> where I -> Item {\n",
        "measure : I -> Int\n",
        "}\n\n",
        "size<I, Item> : I -> Int where Iterator<I, Item>\n",
        "size value = measure value\n\n",
        "impl Iterator<Int, Bool> {\n",
        "measure value = value\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = size(42)\n",
    ));

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn eligible_local_relay_generalizes_higher_kinded_parameters() {
    fn assert_no_scheme_below_function(ty: &ash::types::Type) {
        enum Payload<'a> {
            Type(&'a ash::types::Type),
            Argument(&'a ash::types::KindedArgument),
            Row(&'a ash::types::EffectRow),
        }
        let mut work = vec![(Payload::Type(ty), false)];
        while let Some((payload, below_function)) = work.pop() {
            match payload {
                Payload::Argument(ash::types::KindedArgument::TypeArg(ty)) => {
                    work.push((Payload::Type(ty), below_function))
                }
                Payload::Argument(ash::types::KindedArgument::RowArg(row)) => {
                    work.push((Payload::Row(row), below_function))
                }
                Payload::Row(row) => {
                    for member in row
                        .known()
                        .iter()
                        .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
                    {
                        work.extend(
                            member
                                .arguments()
                                .iter()
                                .map(|argument| (Payload::Argument(argument), below_function)),
                        );
                    }
                }
                Payload::Type(ash::types::Type::Forall(_, body)) => {
                    assert!(
                        !below_function,
                        "a generalized scheme must not occur below a term-function arrow"
                    );
                    work.push((Payload::Type(body), below_function));
                }
                Payload::Type(ash::types::Type::Function(domain, codomain)) => {
                    work.push((Payload::Type(codomain), true));
                    work.push((Payload::Type(domain), true));
                }
                Payload::Type(ash::types::Type::EffectfulFunction(domain, codomain)) => {
                    work.push((Payload::Type(codomain.value()), true));
                    work.push((Payload::Type(domain), true));
                    work.push((Payload::Row(codomain.effects()), below_function));
                }
                Payload::Type(ash::types::Type::ResourceApply(_, arguments)) => work.extend(
                    arguments
                        .iter()
                        .map(|argument| (Payload::Argument(argument), below_function)),
                ),
                Payload::Type(ash::types::Type::Application(function, argument)) => {
                    work.push((Payload::Type(argument), below_function));
                    work.push((Payload::Type(function), below_function));
                }
                Payload::Type(ash::types::Type::Tuple(elements)) => work.extend(
                    elements
                        .iter()
                        .map(|element| (Payload::Type(element), below_function)),
                ),
                Payload::Type(
                    ash::types::Type::Bytes
                    | ash::types::Type::String
                    | ash::types::Type::Int
                    | ash::types::Type::Bool
                    | ash::types::Type::Unit
                    | ash::types::Type::Nominal(_)
                    | ash::types::Type::Variable(_)
                    | ash::types::Type::Inference(_),
                ) => {}
            }
        }
    }

    fn has_expected_kinds(parameters: &[(ash::types::TypeVariableId, ash::types::Kind)]) -> bool {
        matches!(
            parameters,
            [
                (
                    _,
                    ash::types::Kind::Arrow(function_domain, function_codomain),
                ),
                (_, ash::types::Kind::Type),
            ] if matches!(function_domain.as_ref(), ash::types::Kind::Type)
                && matches!(function_codomain.as_ref(), ash::types::Kind::Type)
        )
    }

    let source = concat!(
        "type Pair<A, B> = Pair(A, B)\n\n",
        "keep<F : Type -> Type, A> : F<A> -> F<A>\n",
        "keep value = value\n\n",
        "main : Unit -> Pair<Int, Bool>\n",
        "main () = {\n",
        "let relay = fn(value) {\n",
        "keep(value)\n",
        "}\n",
        "relay(Pair(42, true))\n",
        "}\n",
    );
    let fixture = elaborated_effect(source);
    let program = &fixture.program;
    let observation = run(source);
    assert_eq!(observation.value_display(), "Pair(42, true)");
    assert_eq!(observation.type_display(), "Pair<Int, Bool>");

    let mut work = vec![program.root()];
    let mut local_relay = None;
    let keep_binder = fixture
        .binders
        .iter()
        .find(|(name, _)| name == "keep")
        .unwrap()
        .1;
    let pair_ids = program
        .registry()
        .nominals()
        .iter()
        .filter(|nominal| {
            nominal.spelling == "Pair" && nominal.id.module() == keep_binder.module().unwrap()
        })
        .map(|nominal| nominal.id)
        .collect::<Vec<_>>();
    let [pair_id] = pair_ids.as_slice() else {
        panic!("the entry should retain one Pair identity");
    };
    let mut partial_pair_callees = Vec::new();
    while let Some(id) = work.pop() {
        let node = program.node(id).expect("validated node");
        assert_no_scheme_below_function(&node.ty);
        match &node.kind {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                let initializer = program
                    .node(binding.initializer())
                    .expect("the local initializer should be retained");
                if let EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::TypeAbstraction(abstraction),
                )) = &initializer.kind
                    && has_expected_kinds(abstraction.parameters())
                {
                    let ash::types::Type::Forall(initializer_parameters, initializer_body) =
                        &initializer.ty
                    else {
                        panic!("a type abstraction must expose one outer scheme");
                    };
                    let ash::types::Type::Forall(binder_parameters, binder_body) =
                        binding.binder().ty()
                    else {
                        panic!("the local binder must expose the same outer scheme");
                    };
                    assert_eq!(initializer_parameters.as_ref(), abstraction.parameters());
                    assert_eq!(binder_parameters.as_ref(), abstraction.parameters());
                    assert!(ash::types::same_type(initializer_body, binder_body));
                    assert!(initializer_body.function_view().is_some());
                    assert!(
                        local_relay.replace(binding.binder().id()).is_none(),
                        "the source should retain exactly one generalized local relay"
                    );
                }
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                application,
            ))) if application.arguments()
                == [
                    Type::Application(Box::new(Type::Nominal(*pair_id)), Box::new(Type::Int)),
                    Type::Bool,
                ] =>
            {
                assert!(application.row_arguments().is_empty());
                if let EffectExprKind::Pure(PureExprKind::Variable(variable)) =
                    &program.node(application.function()).unwrap().kind
                {
                    partial_pair_callees.push(variable.binder());
                }
            }
            _ => {}
        }
        for index in 0..node.kind.child_count() {
            work.push(node.kind.child_at(index).expect("validated child"));
        }
    }

    assert!(
        local_relay.is_some(),
        "the eligible local relay must be generalized"
    );
    assert!(
        partial_pair_callees.contains(&local_relay.unwrap()),
        "the local scheme should instantiate F with the partial Pair<Int> constructor"
    );
}

#[test]
fn parameterized_constructors_are_ordinary_polymorphic_values() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\napply : (A -> B, A) -> B\napply (function, value) = function value\n\nmain : Unit -> Option<Int>\nmain () = apply(Some, 42)\n",
    );

    assert_eq!(observation.value_display(), "Some(42)");
    assert_eq!(observation.type_display(), "Option<Int>");
}

#[test]
fn wide_nominal_application_remains_width_through_elaboration_and_core() {
    const WIDTH: usize = 256;
    // Task-6 fixed-kind authentication preserves the predecessor boundary:
    // 320_221 work before the final rewrite + 4_883 fused zonk cells + 512
    // per-occurrence Omega/cache lookups = 325_616, 2_064 below L.

    std::thread::Builder::new()
        .name("wide-canonical-application-pipeline".to_owned())
        .stack_size(320 * 1024)
        .spawn(|| {
            let parameters = (0..WIDTH)
                .map(|index| format!("A{index}"))
                .collect::<Vec<_>>()
                .join(", ");
            let arguments = std::iter::repeat_n("Int", WIDTH)
                .collect::<Vec<_>>()
                .join(", ");
            let source = format!(
                "type Wide<{parameters}> =\nWide\n\nmain : Unit -> Wide<{arguments}>\nmain () = Wide\n"
            );

            let observation = run(&source);
            let mut current = observation.ty();
            let mut application_cells = 0;
            while let ash::types::Type::Application(function, argument) = current {
                assert_eq!(argument.as_ref(), &ash::types::Type::Int);
                application_cells += 1;
                current = function;
            }
            assert_eq!(application_cells, WIDTH);
            assert!(matches!(current, ash::types::Type::Nominal(_)));
            assert_eq!(observation.value_display(), "Wide");
            drop(observation);
        })
        .expect("the wide pipeline thread should start")
        .join()
        .expect("the wide source, Core program, and observation should dispose on a small stack");
}

#[test]
fn solved_result_inference_is_zonked_before_public_observation() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\nmain : Unit -> Option<Int>\nmain () = {\nlet value = None\nlet _ : Option<Int> = value\nvalue\n}\n",
    );

    assert_eq!(observation.value_display(), "None");
    assert_eq!(observation.type_display(), "Option<Int>");
}

#[test]
fn anonymous_function_local_bindings_generalize() {
    let observation = run(
        "main : Unit -> (Int, Bool)\nmain () = {\nlet id = fn(value) {\nvalue\n}\n(id(42), id(false))\n}\n",
    );

    assert_eq!(observation.value_display(), "(42, false)");
    assert_eq!(observation.type_display(), "(Int, Bool)");
}

#[test]
fn primitive_operands_refine_inferred_function_parameters() {
    let observation = run(
        "main : Unit -> Int\nmain () = {\nlet increment = fn(value) {\nvalue + 1\n}\nincrement(41)\n}\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn nested_anonymous_functions_refine_inferred_codomains() {
    let observation = run(
        "main : Unit -> Int\nmain () = {\nlet first = fn(left) {\nfn(right) {\nleft\n}\n}\nfirst(42)(false)\n}\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn parameter_refinement_updates_a_shared_inferred_codomain() {
    let observation = run(
        "apply : (A -> A) -> A -> A\napply function = fn(value) {\nfunction value\n}\n\nmain : Unit -> Unit\nmain () = apply(fn(()) {\n()\n})(())\n",
    );

    assert_eq!(observation.value_display(), "()");
    assert_eq!(observation.type_display(), "Unit");
}

#[test]
fn unit_and_tuple_patterns_refine_inferred_function_domains() {
    let observation = run(
        "main : Unit -> (Int, Int)\nmain () = {\nlet from_unit = fn(()) {\n42\n}\nlet tuple_first = fn((left, right)) {\nleft\n}\n(from_unit(()), tuple_first((7, false)))\n}\n",
    );

    assert_eq!(observation.value_display(), "(42, 7)");
    assert_eq!(observation.type_display(), "(Int, Int)");
}

#[test]
fn singleton_constructor_patterns_refine_inferred_function_domains() {
    let observation = run(
        "type Identity<A> =\nIdentity(A)\n\nmain : Unit -> Int\nmain () = {\nlet unwrap = fn(Identity(value)) {\nvalue\n}\nunwrap(Identity(42))\n}\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn boolean_patterns_refine_before_function_coverage_rejection() {
    assert_eq!(
        reason("main : Unit -> Unit\nmain () = {\nlet only_true = fn(true) {\n1\n}\n()\n}\n"),
        "pattern.refutable-function-domain"
    );
}

#[test]
fn match_patterns_refine_inferred_scrutinee_types_before_coverage() {
    let observation = run(
        "main : Unit -> Bool\nmain () = {\nlet negate = fn(value) {\nmatch value {\ntrue => false\nfalse => true\n}\n}\nnegate(true)\n}\n",
    );

    assert_eq!(observation.value_display(), "false");
    assert_eq!(observation.type_display(), "Bool");
}

#[test]
fn local_patterns_refine_inferred_binding_types_before_coverage() {
    let observation = run(
        "main : Unit -> Int\nmain () = {\nlet consume = fn(value) {\nlet () = value\n42\n}\nconsume(())\n}\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn constructor_patterns_instantiate_the_expected_nominal_arguments() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\nunwrap_or : (A, Option<A>) -> A\nunwrap_or (fallback, None) = fallback\nunwrap_or (_, Some(value)) = value\n\nmain : Unit -> Int\nmain () = unwrap_or(0, Some(42))\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn coverage_substitutes_parameterized_constructor_payloads() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\nclassify : Option<Bool> -> Int\nclassify None = 0\nclassify (Some true) = 1\nclassify (Some false) = 2\n\nmain : Unit -> Int\nmain () = classify(Some(false))\n",
    );
    assert_eq!(observation.value_display(), "2");
}

#[test]
fn parameterized_guarded_recursive_data_keeps_runtime_types_erased() {
    let observation = run(
        "type Stream<A> =\nCons(A, Stream<A>)\n\nmain : Unit -> Stream<Int>\nmain () = {\nlet rec ones : Stream<Int> = Cons(1, ones)\nones\n}\n",
    );

    assert_eq!(observation.value_display(), "Cons(1, <cycle>)");
    assert_eq!(observation.type_display(), "Stream<Int>");
}

#[test]
fn duplicate_type_parameters_are_rejected_at_resolution() {
    assert_eq!(
        reason(
            "type Pair<A, A> =\nPair(A, A)\n\nmain : Unit -> Pair<Int, Int>\nmain () = Pair(1, 2)\n"
        ),
        "resolve.duplicate-type-parameter"
    );
}

#[test]
fn unknown_type_variables_are_rejected_at_resolution() {
    assert_eq!(
        reason(
            "type Wrapped<A> =\nWrapped(B)\n\nmain : Unit -> Wrapped<Int>\nmain () = Wrapped(1)\n"
        ),
        "resolve.unknown-type"
    );
}

#[test]
fn nominal_constructors_at_value_boundaries_must_end_at_type() {
    assert_eq!(
        reason(
            "type Option<A> =\nNone\n| Some(A)\n\nbad : Option -> Int\nbad _ = 0\n\nmain : Unit -> Int\nmain () = bad None\n"
        ),
        "kind.expected-type"
    );
}

#[test]
fn type_parameters_of_kind_type_are_not_applicable() {
    assert_eq!(
        reason("type Bad<A> =\nBad(A<Int>)\n\nmain : Unit -> Bad<Int>\nmain () = Bad(1)\n"),
        "kind.not-applicable"
    );
}

#[test]
fn application_shaped_local_bindings_remain_monomorphic() {
    assert_eq!(
        reason(
            "make : Unit -> (A -> A)\nmake _ = fn(value) {\nvalue\n}\n\nmain : Unit -> (Int, Bool)\nmain () = {\nlet id = make(())\n(id(42), id(false))\n}\n"
        ),
        "type.argument"
    );
}

#[test]
fn function_generalization_excludes_inference_shared_with_the_environment() {
    assert_eq!(
        reason(
            "make : Unit -> (A -> A)\nmake _ = fn(value) {\nvalue\n}\n\nmain : Unit -> (Int, Bool)\nmain () = {\nlet shared = make(())\nlet get = fn(ignored) {\nshared\n}\n(get(())(42), get(())(false))\n}\n"
        ),
        "type.argument"
    );
}

#[test]
fn inferred_polymorphic_recursion_is_rejected() {
    assert_eq!(
        reason(
            "loop : A -> Unit\nloop value = loop((value, value))\n\nmain : Unit -> Unit\nmain () = loop(1)\n"
        ),
        "type.polymorphic-recursion"
    );
}

#[test]
fn unresolved_polymorphic_method_argument_is_type_ambiguous() {
    assert_eq!(
        reason(concat!(
            "interface Project<I> {\n",
            "project<A> : I -> (I, A)\n",
            "}\n\n",
            "probe : Int -> Unit where Project<Int>\n",
            "probe value = {\nlet _ = project value\n()\n}\n",
        )),
        "type.ambiguous"
    );
}

#[test]
fn polymorphic_recursive_method_self_use_is_rejected() {
    assert_eq!(
        reason(concat!(
            "interface Repeat<I> {\nrepeat<A> : (I, A) -> A\n}\n\n",
            "impl Repeat<Int> {\n",
            "repeat (owner, value) = repeat((owner, (value, value)))\n",
            "}\n",
        )),
        "type.polymorphic-recursion"
    );
}

#[test]
fn unrelated_method_body_failure_is_not_displaced_by_staged_recursive_dispatch() {
    assert_eq!(
        reason(concat!(
            "interface Repeat<I> {\nrepeat<A> : (I, A) -> A\n}\n\n",
            "impl Repeat<Int> {\n",
            "repeat (owner, value) = {\n",
            "let ignored = repeat((owner, (value, value)))\n",
            "false\n",
            "}\n",
            "}\n",
        )),
        "type.definition-result"
    );
}

#[test]
fn recursive_global_self_uses_apply_the_same_rigid_parameters() {
    let observation =
        run("repeat : A -> A\nrepeat value = repeat value\n\nmain : Unit -> Int\nmain () = 0\n");
    assert_eq!(observation.value_display(), "0");
}

#[test]
fn infinite_inferred_types_are_rejected_by_the_occurs_check() {
    assert_eq!(
        reason(
            "main : Unit -> Unit\nmain () = {\nlet omega = fn(value) {\nvalue(value)\n}\n()\n}\n"
        ),
        "type.infinite"
    );
}

#[test]
fn unresolved_local_function_inference_is_a_source_ambiguity() {
    assert_eq!(
        reason(
            "main : Unit -> Unit\nmain () = {\nlet constant = fn(ignored) {\n42\n}\nlet _ = constant\n()\n}\n"
        ),
        "type.ambiguous"
    );
}

#[test]
fn discarded_anonymous_function_inference_is_a_source_ambiguity() {
    assert_eq!(
        reason("main : Unit -> Unit\nmain () = {\nlet _ = fn(value) {\nvalue\n}\n()\n}\n"),
        "type.ambiguous"
    );
}

#[test]
fn unused_parameterized_constructor_inference_is_a_source_ambiguity() {
    assert_eq!(
        reason(
            "type Option<A> =\nNone\n| Some(A)\n\nmain : Unit -> Unit\nmain () = {\nlet unused = None\n()\n}\n"
        ),
        "type.ambiguous"
    );
}

#[test]
fn deep_parameter_substitution_completes_on_a_small_stack() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, || {
                let mut argument = "Unit".to_owned();
                for _ in 0..(ash::parser::STRUCTURAL_DEPTH_LIMIT - 4) {
                    argument = format!("Unit -> {argument}");
                }
                let text = format!(
                    "type Holder<A> =\nHold(Unit -> A)\n\nread : Holder<{argument}> -> Int\nread (Hold function) = 0\n\nmain : Unit -> Int\nmain () = 0\n"
                );
                assert_eq!(run(&text).value_display(), "0");
            })
            .expect("small-stack thread should start")
            .join()
            .expect("substitution must not consume the host stack");
    });
}
