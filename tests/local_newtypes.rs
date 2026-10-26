use std::{
    collections::HashSet,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{
        EffectExprKind, EffectOperation, EffectOperationFamily, PureComputation, PureExprKind,
        PureValue, dialect::CoreOperationFamily, validate_effect_modules,
    },
    elaborate::{EffectElaborator, TypeError, TypeReason, check_module, link_modules},
    eval::{Value, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason, resolve_module},
    resolved::{
        CheckedModule, ResolvedDefinitionKind, ResolvedExprKind, ResolvedLocalDeclaration,
        ResolvedModule,
    },
    types::{ConstructorId, EffectInstance, EffectRow, NominalTypeId, Type},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory =
                std::env::temp_dir().join(format!("ash-local-newtype-{}-{id}", std::process::id()));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join("entry.ash");
                    fs::write(&path, text).expect("local-newtype fixture should be writable");
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("local-newtype fixture should be creatable: {error}"),
            }
        }
    }

    fn resolve(&self) -> ash::resolved::ResolvedModule {
        let graph = load_module_graph(&self.0, &ModuleRoots::empty())
            .expect("local-newtype fixture should load");
        resolve_entry(&graph).expect("local-newtype fixture should resolve")
    }
}

fn resolve_entry(graph: &ModuleGraph) -> Result<ResolvedModule, ResolveModuleError> {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked: &&CheckedModule| checked.module() == edge.target())
                    .expect("dependency order must retain the exact target first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("each checked summary must authenticate its actual dependency edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies);
        if module.id() == graph.entry() {
            return resolved;
        }
        checked.push(
            check_module(resolved.expect("preceding dependencies should resolve"))
                .expect("preceding dependencies should check"),
        );
    }
    panic!("the graph must retain its actual entry");
}

fn checked_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked: &&CheckedModule| checked.module() == edge.target())
                    .expect("the exact dependency target precedes its importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the actual edge authenticates")
            })
            .collect::<Vec<_>>();
        checked.push(
            check_module(resolve_module(module, &dependencies).expect("the component resolves"))
                .expect("the component checks"),
        );
    }
    checked
}

fn default_row(graph: &ModuleGraph) -> EffectRow {
    let mut checked = Vec::new();
    for module in graph.modules() {
        if module.id() == graph.entry() {
            break;
        }
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked: &&CheckedModule| checked.module() == edge.target())
                    .expect("the exact dependency target precedes its importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the actual edge authenticates")
            })
            .collect::<Vec<_>>();
        checked.push(
            check_module(resolve_module(module, &dependencies).expect("the dependency resolves"))
                .expect("the dependency checks"),
        );
    }
    let defining = checked
        .iter()
        .find(|module| {
            graph
                .module(module.module())
                .unwrap()
                .source()
                .display_path()
                == "@compiler.region"
        })
        .expect("the defining compiler service remains checked");
    let effects = defining
        .effects()
        .iter()
        .filter(|effect| effect.spelling == "DefaultAlloc")
        .collect::<Vec<_>>();
    let [effect] = effects.as_slice() else {
        panic!("the canonical service effect is unique");
    };
    assert_eq!(effect.id.module(), defining.module());
    assert!(effect.parameters.is_empty());
    EffectRow::singleton(EffectInstance::new(effect.id, Box::new([])))
}

fn resolution_error(text: &str) -> ResolveReason {
    let fixture = Fixture::new(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("rejected local-newtype fixture should load");
    match resolve_entry(&graph).expect_err("local-newtype fixture should fail resolution") {
        ResolveModuleError::Resolution(error) => error.reason,
        ResolveModuleError::Kind(error) => {
            panic!("kind checking stole resolution ownership: {error:?}")
        }
        ResolveModuleError::Representation(error) => {
            panic!("fixture unexpectedly reached representation checking: {error:?}")
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn constructor_head(expression: &ash::resolved::ResolvedExpr) -> ConstructorId {
    let ResolvedExprKind::Apply(application) = &expression.kind else {
        panic!("expected constructor application")
    };
    let ResolvedExprKind::Constructor(constructor) = &application.function.kind else {
        panic!("expected constructor head")
    };
    constructor.constructor
}

fn annotated_nominal(binding: &ash::resolved::ResolvedBinding) -> NominalTypeId {
    let Some(annotation) = &binding.annotation else {
        panic!("expected binding annotation")
    };
    let Type::Nominal(nominal) = annotation.ty else {
        panic!("expected nominal annotation")
    };
    nominal
}

#[test]
fn identity_free_closure_may_capture_a_local_newtype() {
    let fixture = Fixture::new(concat!(
        "make : Unit -> (Unit -> Int)\n",
        "make () = {\n",
        "    newtype Offset = Offset(Int)\n",
        "    let offset = Offset(41)\n",
        "    fn(ignored) {\n",
        "        match offset {\n",
        "            Offset(value) => value + 1\n",
        "        }\n",
        "    }\n",
        "}\n\n",
        "main : Unit -> (Unit -> Int)\n",
        "main () = make()\n",
    ));
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("identity-free closure fixture should load");
    let checked = checked_graph(&graph);
    let entry = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .unwrap();
    let offsets = entry
        .registry()
        .lexical_nominals()
        .iter()
        .filter(|nominal| nominal.spelling == "Offset")
        .collect::<Vec<_>>();
    let [offset] = offsets.as_slice() else {
        panic!("the entry owns one Offset nominal");
    };
    let offset = offset.id;
    let linked = link_modules(checked, graph.entry()).expect("fixture should link");
    let linked = validate_interface_evidence(linked).expect("fixture evidence should validate");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("fixture Core namespace should fit");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("identity-free closure should elaborate");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("identity-free closure Core should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let relation = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let program = validate_effect_modules(unchecked, &sources, &relation)
        .expect("identity-free closure Core should validate");

    let evaluation = evaluate_effect(&program).expect("identity-free closure should execute");
    assert!(
        matches!(evaluation.value, Value::RegionFunction(_)),
        "main returns its stored identity-free closure"
    );
    let root_type = &program.node(program.root()).unwrap().ty;
    let function = root_type
        .function_view()
        .expect("the result remains callable");
    assert_eq!(function.domain(), &Type::Unit);
    assert_eq!(function.value(), &Type::Int);
    assert_eq!(function.effects(), Some(&default_row(&graph)));
    let owned_nodes = |root| {
        let mut pending = vec![root];
        let mut seen = HashSet::new();
        while let Some(id) = pending.pop() {
            if seen.insert(id) {
                let node = program.node(id).unwrap();
                pending.extend((0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)));
            }
        }
        seen
    };
    let scopes = owned_nodes(program.root()).into_iter().filter(|id|
        matches!(program.node(*id).unwrap().kind,
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::LocalNominalScope(scope))) if scope.owner() == offset))
        .collect::<Vec<_>>();
    let [scope] = scopes.as_slice() else {
        panic!("Offset has one actual lexical scope");
    };
    let owned = owned_nodes(*scope);
    let bindings = owned
        .iter()
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) =
                &program.node(*id)?.kind
            else {
                return None;
            };
            (binding.binder().ty() == &Type::Nominal(offset)).then_some(binding.binder().id())
        })
        .collect::<Vec<_>>();
    let [offset_binding] = bindings.as_slice() else {
        panic!("the scope retains one offset value binder");
    };
    let closures = owned
        .iter()
        .filter(|id| {
            let node = program.node(**id).unwrap();
            matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::RegionClosure(_))
            ) && &node.ty == root_type
        })
        .collect::<Vec<_>>();
    let [closure] = closures.as_slice() else {
        panic!("the scope owns one exact returned callable");
    };
    let closure = program.node(**closure).unwrap();
    let mut parameters = Vec::new();
    EffectOperationFamily::visit_operation_binders(&closure.kind, &mut |parameter| {
        parameters.push(parameter.ty().clone())
    });
    assert_eq!(parameters, [Type::Unit]);
    assert!((0..closure.kind.child_count()).filter_map(|i| closure.kind.child_at(i)).any(|id|
        matches!(program.node(id).unwrap().kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == *offset_binding)),
        "the stored callable retains the exact preceding offset value");

    let mut pending = vec![program.root()];
    let mut scopes = 0;
    let mut conversions = 0;
    let mut ordinary_constructors = 0;
    while let Some(node) = pending.pop() {
        let expression = program.node(node).expect("reachable Core node");
        match &expression.kind {
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Constructor(_))) => {
                ordinary_constructors += 1
            }
            EffectExprKind::Pure(PureExprKind::Computation(
                PureComputation::NewtypeConversion(_),
            )) => conversions += 1,
            EffectExprKind::Pure(PureExprKind::Computation(
                PureComputation::LocalNominalScope(_),
            )) => scopes += 1,
            EffectExprKind::Operation(EffectOperation::RegionTuple(_))
                if expression.ty == Type::Nominal(offset) =>
            {
                ordinary_constructors += 1
            }
            _ => {}
        }
        pending
            .extend((0..expression.kind.child_count()).filter_map(|i| expression.kind.child_at(i)));
    }
    assert_eq!(scopes, 1);
    assert_eq!(conversions, 2);
    assert_eq!(ordinary_constructors, 0);
    let invoked = Fixture::new(
        &graph
            .module(graph.entry())
            .unwrap()
            .source()
            .text()
            .replace(
                "main : Unit -> (Unit -> Int)\nmain () = make()\n",
                "main : Unit -> Int\nmain () = make()()\n",
            ),
    );
    let observed = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: invoked.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("the captured offset remains usable after its nominal scope returns");
    assert_eq!(observed.value_display(), "42");
}

#[test]
fn direct_local_value_cannot_escape() {
    let resolved = Fixture::new(concat!(
        "main : Unit -> Int\n",
        "main () = {\n",
        "    let escaped = {\n",
        "        newtype Hidden = Hidden(Int)\n",
        "        Hidden(1)\n",
        "    }\n",
        "    0\n",
        "}\n",
    ))
    .resolve();
    let TypeError::Source(diagnostic) = check_module(resolved)
        .expect_err("the local nominal identity must not cross its lexical boundary")
    else {
        panic!("escape should be a source typing error")
    };
    assert_eq!(diagnostic.reason, TypeReason::LocalNominalEscape);
}

#[test]
fn local_nominal_cannot_escape_through_an_outer_inference_variable() {
    assert_local_escape(
        concat!(
            "main : Unit -> Int\n",
            "main () = {\n",
            "    let outer = fn(value) {\n",
            "        let discarded = {\n",
            "            newtype Hidden = Hidden(Int)\n",
            "            match value {\n",
            "                Hidden(number) => ()\n",
            "            }\n",
            "        }\n",
            "        0\n",
            "    }\n",
            "    42\n",
            "}\n",
        ),
        0,
    );
}

#[test]
fn delayed_requirement_cannot_solve_an_outer_type_to_a_local_nominal() {
    assert_local_escape(
        concat!(
            "type Box<A> = Box(A)\n",
            "interface Rel<Key, Value> where Key -> Value {\n    relate : (Key, Value) -> Unit\n}\n",
            "impl<A> Rel<Box<A>, A> {\n    relate pair = ()\n}\n",
            "main : Unit -> Int\nmain () = {\n",
            "    let outer = fn(value) {\n        let discarded = {\n",
            "            newtype Hidden = Hidden(Int)\n",
            "            relate((Box(Hidden(42)), value))\n",
            "        }\n        0\n    }\n    42\n}\n",
        ),
        0,
    );
}

#[test]
fn internal_nominal_requirement_keeps_an_unrelated_outward_type_generalizable() {
    assert_execution(concat!(
        "type Box<A> = Box(A)\n",
        "interface Rel<Key, Value> where Key -> Value {\n    relate : (Key, Value) -> Unit\n}\n",
        "impl<A> Rel<Box<A>, A> {\n    relate pair = ()\n}\n",
        "main : Unit -> Int\nmain () = {\n",
        "    let ordinary = fn(value) {\n        let discarded = {\n",
        "            newtype Hidden = Hidden(Int)\n",
        "            relate((Box(Hidden(42)), Hidden(0)))\n",
        "        }\n        value\n    }\n    ordinary(42)\n}\n",
    ));
}

#[test]
fn local_representation_may_use_an_enclosing_type_parameter() {
    let fixture = Fixture::new(concat!(
        "wrap<A> : A -> A\n",
        "wrap value = {\n",
        "    newtype Local = Local(A)\n",
        "    match Local(value) {\n",
        "        Local(result) => result\n",
        "    }\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = wrap(42)\n",
    ));
    let observation = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("a local representation may use the preceding lexical type scope");
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn parameterized_local_newtype_reaches_execution() {
    assert_execution(concat!(
        "main : Unit -> Int\nmain () = {\n",
        "    newtype Local<A> = Local(A)\n",
        "    match Local(42) {\n        Local(value) => value\n    }\n}\n",
    ));
}

#[test]
fn kinded_local_newtype_reuses_constructor_application() {
    assert_execution(concat!(
        "type Option<A> =\n    None\n    | Some(A)\n",
        "main : Unit -> Int\nmain () = {\n",
        "    newtype Local<F : Type -> Type, A> = Local(F<A>)\n",
        "    let wrapped : Local<Option, Int> = Local(Some(42))\n",
        "    match wrapped {\n        Local(Some(value)) => value\n        Local(None) => 0\n    }\n}\n",
    ));
}

#[test]
fn following_recursive_group_executes_with_local_nominal() {
    assert_execution(concat!(
        "main : Unit -> Int\nmain () = {\n",
        "    newtype Cell = Cell(Int)\n",
        "    let rec reveal : Cell -> Int = fn(cell) {\n",
        "        match cell {\n            Cell(value) => value\n        }\n    }\n",
        "    reveal(Cell(42))\n}\n",
    ));
}

#[test]
fn representation_interface_evidence_does_not_transfer_to_a_local_nominal() {
    let resolved = Fixture::new(concat!(
        "interface Render<A> {\n    render : A -> Int\n}\n",
        "impl Render<Int> {\n    render value = value\n}\n",
        "main : Unit -> Int\nmain () = {\n",
        "    newtype UserId = UserId(Int)\n    render(UserId(41))\n}\n",
    ))
    .resolve();
    let TypeError::Interface(diagnostic) =
        check_module(resolved).expect_err("representation evidence is not nominal evidence")
    else {
        panic!("the interface checker owns the rejection")
    };
    assert_eq!(
        diagnostic.reason,
        ash::interface::InterfaceReason::Unsatisfied
    );
}

#[test]
fn local_representation_captures_a_generic_implementation_parameter() {
    assert_execution(concat!(
        "type Box<A> = Box(A)\n",
        "interface Keep<A> {\n    keep : A -> A\n}\n",
        "impl<A> Keep<Box<A>> {\n    keep (Box(value)) = {\n",
        "        newtype Local = Local(A)\n",
        "        match Local(value) {\n            Local(result) => Box(result)\n        }\n    }\n}\n",
        "main : Unit -> Int\nmain () = match keep(Box(42)) {\n    Box(value) => value\n}\n",
    ));
}

fn assert_execution(source: &str) {
    let fixture = Fixture::new(source);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty()).expect("fixture should load");
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked: &&CheckedModule| checked.module() == edge.target())
                    .expect("dependency order must retain the exact target first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("each checked summary must authenticate its actual dependency edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the interaction component should resolve");
        checked.push(check_module(resolved).expect("the interaction component should check"));
    }
    let linked = link_modules(checked, graph.entry()).expect("fixture should link");
    let linked = validate_interface_evidence(linked).expect("evidence should authenticate");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("Core namespace should fit");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("fixture should elaborate");
    let program = elaborator.finish(typed.node).expect("Core should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let relation = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let validated =
        validate_effect_modules(program, &sources, &relation).expect("Core should validate");
    for transformed in [
        ash::core::transform::identity_effect_traversal(&validated)
            .expect("identity traversal should rebuild"),
        ash::core::transform::fold_effect_literal_primitives(&validated)
            .expect("literal folding should rebuild"),
    ] {
        let validated = validate_effect_modules(transformed, &sources, &relation)
            .expect("transformed Core should validate");
        let observed = evaluate_effect(&validated).expect("transformed Core should execute");
        assert!(matches!(observed.value, Value::SmallInteger(value) if value.to_string() == "42"));
    }
}

fn assert_local_escape(source: &str, case: usize) {
    let resolved = Fixture::new(source).resolve();
    let error = check_module(resolved)
        .expect_err("the local nominal identity must not cross its lexical boundary");
    let TypeError::Source(diagnostic) = error else {
        panic!("escape case {case} should be a source typing error: {error:?}")
    };
    assert_eq!(diagnostic.reason, TypeReason::LocalNominalEscape);
}

#[test]
fn local_nominal_escape_matrix_covers_nested_outward_types() {
    let prefix = "type Box<A> = Box(A)\n\neffect Read<A> {\nread : Unit -> A\n}\n\nmain : Unit -> Int\nmain () = {\n    let escaped = {\n        newtype Hidden = Hidden(Int)\n";
    let suffix = "\n    }\n    0\n}\n";
    let cases = [
        "        Hidden",
        "        (Hidden(1), 0)",
        "        Box(Hidden(1))",
        concat!(
            "        let expose : Hidden -> Int = fn(value) {\n",
            "            0\n",
            "        }\n",
            "        expose",
        ),
        concat!(
            "        let expose : Unit -> Hidden = fn(value) {\n",
            "            Hidden(1)\n",
            "        }\n",
            "        expose",
        ),
        concat!(
            "        let expose : Unit -> Unit ! {Read<Hidden>} = ",
            "fn(value) {\n",
            "            ()\n",
            "        }\n",
            "        expose",
        ),
        concat!(
            "        let project = fn((hidden, value)) {\n",
            "            match hidden {\n",
            "                Hidden(number) => value\n",
            "            }\n",
            "        }\n",
            "        project",
        ),
        concat!(
            "        let reveal : Hidden -> Int = fn(value) {\n",
            "            match value {\n",
            "                Hidden(number) => number\n",
            "            }\n",
            "        }\n",
            "        (Hidden(1), reveal)",
        ),
    ];
    for (index, case) in cases.into_iter().enumerate() {
        assert_local_escape(&format!("{prefix}{case}{suffix}"), index);
    }
}

#[test]
fn local_nominal_scope_accepts_identity_free_representation_and_polymorphic_results() {
    for body in [
        concat!(
            "        match Hidden(42) {\n",
            "            Hidden(value) => value\n",
            "        }",
        ),
        "        ignore(Hidden(1))",
    ] {
        let source = format!(
            "ignore<A> : A -> Int\nignore value = 42\n\nmain : Unit -> Int\nmain () = {{\n    let accepted = {{\n        newtype Hidden = Hidden(Int)\n{body}\n    }}\n    accepted\n}}\n"
        );
        let resolved = Fixture::new(&source).resolve();
        check_module(resolved).expect("identity-free outward type should be accepted");
    }
}

#[test]
fn deep_local_nominal_scopes_accept_and_reject_on_a_small_stack() {
    const DEPTH: usize = 4_096;

    std::thread::Builder::new()
        .name("deep-local-nominal-scopes".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut declarations = String::new();
            for index in 0..DEPTH {
                declarations.push_str(&format!("        newtype N{index} = N{index}(Int)\n"));
            }

            let accepted = Fixture::new(&format!(
                "main : Unit -> Unit\nmain () = {{\n    let accepted = {{\n{declarations}        ()\n    }}\n    accepted\n}}\n"
            ));
            let observation = ash::driver::run_path(ash::driver::RunConfiguration {
                entry: accepted.0.clone(), roots: ModuleRoots::empty(),
            }).unwrap_or_else(|failure| panic!("deep public acceptance: {failure:?}; work={:?}", failure.compilation_work()));
            assert!(matches!(observation.value(), Value::Unit));
            assert_eq!(observation.ty(), &Type::Unit);

            let rejected = Fixture::new(&format!(
                "main : Unit -> Unit\nmain () = {{\n    let escaped = {{\n{declarations}        N{}(0)\n    }}\n    ()\n}}\n",
                DEPTH - 1,
            ));
            let failure = ash::driver::run_path(ash::driver::RunConfiguration {
                entry: rejected.0.clone(), roots: ModuleRoots::empty(),
            }).expect_err("the deep outward local identity must be rejected");
            let Some(ash::driver::PipelineFailure::Typing(TypeError::Source(diagnostic))) = failure.pipeline_failure() else {
                panic!("deep escape should remain a source typing error: {failure:?}");
            };
            assert_eq!(diagnostic.reason, TypeReason::LocalNominalEscape);

        })
        .expect("the deep local-scope thread should start")
        .join()
        .expect("deep accepted and rejected local scopes must remain stack-safe");
}

#[test]
fn nested_shadowed_local_newtypes_keep_distinct_lexical_identities() {
    let fixture = Fixture::new(concat!(
        "newtype Shadow = Shadow(Int)\n\n",
        "main : Unit -> Unit\n",
        "main () = {\n",
        "    newtype Shadow = Shadow(Shadow)\n",
        "    let outer : Shadow = Shadow(1)\n",
        "    let nested = {\n",
        "        newtype Shadow = Shadow(Shadow)\n",
        "        let inner : Shadow = Shadow(2)\n",
        "        ()\n",
        "    }\n",
        "    let restored : Shadow = Shadow(3)\n",
        "    ()\n",
        "}\n\n",
        "after : Shadow -> Shadow\n",
        "after value = Shadow(value)\n",
    ));
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty()).unwrap();
    let default_row = default_row(&graph);
    let resolved = resolve_entry(&graph).expect("the actual entry resolves");

    let [module_nominal] = resolved.registry().nominals() else {
        panic!("expected one module nominal")
    };
    let [outer_nominal, inner_nominal] = resolved.registry().lexical_nominals() else {
        panic!("expected two lexical nominals")
    };
    assert!(!module_nominal.id.is_lexical());
    assert!(outer_nominal.id.is_lexical());
    assert!(inner_nominal.id.is_lexical());
    assert_ne!(module_nominal.id, outer_nominal.id);
    assert_ne!(outer_nominal.id, inner_nominal.id);
    assert_eq!(
        outer_nominal.representation,
        Some(Type::Nominal(module_nominal.id))
    );
    assert_eq!(
        inner_nominal.representation,
        Some(Type::Nominal(outer_nominal.id))
    );

    let [outer_constructor, inner_constructor] = resolved.registry().lexical_constructors() else {
        panic!("expected two lexical constructors")
    };
    assert_eq!(outer_constructor.owner, outer_nominal.id);
    assert_eq!(outer_constructor.id.owner(), outer_nominal.id);
    assert_eq!(inner_constructor.owner, inner_nominal.id);
    assert_eq!(inner_constructor.id.owner(), inner_nominal.id);

    let ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[0].kind else {
        panic!("expected equational main")
    };
    let ResolvedExprKind::Block(block) = &main.equations[0].body.kind else {
        panic!("expected main block")
    };
    let ResolvedLocalDeclaration::Newtype(outer_owner) = block.declarations[0] else {
        panic!("expected outer local newtype marker")
    };
    assert_eq!(outer_owner, outer_nominal.id);
    let ResolvedLocalDeclaration::Binding(outer) = &block.declarations[1] else {
        panic!("expected outer binding")
    };
    assert_eq!(annotated_nominal(outer), outer_nominal.id);
    assert_eq!(constructor_head(&outer.initializer), outer_constructor.id);

    let ResolvedLocalDeclaration::Binding(nested) = &block.declarations[2] else {
        panic!("expected nested block binding")
    };
    let ResolvedExprKind::Block(nested_block) = &nested.initializer.kind else {
        panic!("expected nested block")
    };
    let ResolvedLocalDeclaration::Newtype(inner_owner) = nested_block.declarations[0] else {
        panic!("expected inner local newtype marker")
    };
    assert_eq!(inner_owner, inner_nominal.id);
    let ResolvedLocalDeclaration::Binding(inner) = &nested_block.declarations[1] else {
        panic!("expected inner binding")
    };
    assert_eq!(annotated_nominal(inner), inner_nominal.id);
    assert_eq!(constructor_head(&inner.initializer), inner_constructor.id);

    let ResolvedLocalDeclaration::Binding(restored) = &block.declarations[3] else {
        panic!("expected restored outer binding")
    };
    assert_eq!(annotated_nominal(restored), outer_nominal.id);
    assert_eq!(
        constructor_head(&restored.initializer),
        outer_constructor.id
    );

    let ResolvedDefinitionKind::Equational(after) = &resolved.definitions()[1].kind else {
        panic!("expected post-block definition")
    };
    let function = after
        .interface
        .annotation
        .ty
        .function_view()
        .expect("expected post-block function annotation");
    assert_eq!(function.domain(), &Type::Nominal(module_nominal.id));
    assert_eq!(function.value(), &Type::Nominal(module_nominal.id));
    assert_eq!(function.effects(), Some(&default_row));
    assert_eq!(
        constructor_head(&after.equations[0].body),
        resolved.registry().constructors()[0].id
    );
}

#[test]
fn sibling_local_newtypes_with_equal_shapes_have_distinct_identities() {
    let resolved = Fixture::new(concat!(
        "main : Unit -> Unit\n",
        "main () = {\n",
        "    let first = {\n",
        "        newtype Token = Token(Int)\n",
        "        ()\n",
        "    }\n",
        "    let second = {\n",
        "        newtype Token = Token(Int)\n",
        "        ()\n",
        "    }\n",
        "    ()\n",
        "}\n",
    ))
    .resolve();

    let [first, second] = resolved.registry().lexical_nominals() else {
        panic!("expected two sibling lexical facts")
    };
    assert_ne!(first.id, second.id);
    assert_eq!(first.spelling, "Token");
    assert_eq!(second.spelling, "Token");
    assert_eq!(first.representation, Some(Type::Int));
    assert_eq!(second.representation, Some(Type::Int));
}

#[test]
fn local_nominal_shadows_same_spelled_module_interface() {
    let resolved = Fixture::new(concat!(
        "interface Token<A> {\n",
        "    token : A -> A\n",
        "}\n\n",
        "main : Unit -> Unit\n",
        "main () = {\n",
        "    newtype Token = Token(Int)\n",
        "    let local : Token = Token(1)\n",
        "    ()\n",
        "}\n",
    ))
    .resolve();

    let [local] = resolved.registry().lexical_nominals() else {
        panic!("expected one lexical nominal")
    };
    let ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[0].kind else {
        panic!("expected equational main")
    };
    let ResolvedExprKind::Block(block) = &main.equations[0].body.kind else {
        panic!("expected main block")
    };
    let ResolvedLocalDeclaration::Binding(binding) = &block.declarations[1] else {
        panic!("expected binding after local newtype")
    };
    assert_eq!(annotated_nominal(binding), local.id);
}

#[test]
fn local_newtype_visibility_is_strictly_sequential() {
    assert_eq!(
        resolution_error(concat!(
            "main : Unit -> Unit\n",
            "main () = {\n",
            "    newtype SelfRef = SelfRef(SelfRef)\n",
            "    ()\n",
            "}\n",
        )),
        ResolveReason::UnknownType,
    );
    assert_eq!(
        resolution_error(concat!(
            "main : Unit -> Unit\n",
            "main () = {\n",
            "    newtype First = First(Second)\n",
            "    newtype Second = Second(Int)\n",
            "    ()\n",
            "}\n",
        )),
        ResolveReason::UnknownType,
    );
    assert_eq!(
        resolution_error(concat!(
            "main : Unit -> Unit\n",
            "main () = {\n",
            "    let nested = {\n",
            "        newtype Hidden = Hidden(Int)\n",
            "        ()\n",
            "    }\n",
            "    let escaped : Hidden = 1\n",
            "    ()\n",
            "}\n",
        )),
        ResolveReason::UnknownType,
    );
    assert_eq!(
        resolution_error(concat!(
            "main : Unit -> Unit\n",
            "main () = {\n",
            "    let nested = {\n",
            "        newtype Hidden = Hidden(Int)\n",
            "        ()\n",
            "    }\n",
            "    let escaped = Hidden(1)\n",
            "    ()\n",
            "}\n",
        )),
        ResolveReason::UnknownConstructor,
    );
}

#[test]
fn following_recursive_group_uses_local_nominal_without_absorbing_declaration() {
    let fixture = Fixture::new(concat!(
        "main : Unit -> Unit\n",
        "main () = {\n",
        "    newtype Cell = Cell(Int)\n",
        "    let rec loop : Cell -> Cell = fn(value) {\n",
        "        value\n",
        "    }\n",
        "    ()\n",
        "}\n",
    ));
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty()).unwrap();
    let default_row = default_row(&graph);
    let resolved = resolve_entry(&graph).expect("the actual entry resolves");
    let owner = resolved.registry().lexical_nominals()[0].id;
    let ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[0].kind else {
        panic!("expected equational main")
    };
    let ResolvedExprKind::Block(block) = &main.equations[0].body.kind else {
        panic!("expected main block")
    };
    assert!(matches!(block.declarations[0], ResolvedLocalDeclaration::Newtype(id) if id == owner));
    let ResolvedLocalDeclaration::Recursive(group) = &block.declarations[1] else {
        panic!("expected following recursive group")
    };
    let [member] = group.members.as_slice() else {
        panic!("the newtype must not become a recursive member")
    };
    let function = member
        .annotation
        .ty
        .function_view()
        .expect("the recursive member remains callable");
    assert_eq!(function.domain(), &Type::Nominal(owner));
    assert_eq!(function.value(), &Type::Nominal(owner));
    assert_eq!(function.effects(), Some(&default_row));
}

#[test]
fn local_facts_do_not_enter_module_or_export_partitions() {
    let resolved = Fixture::new(concat!(
        "pub newtype Visible = Visible(Int)\n\n",
        "main : Unit -> Unit\n",
        "main () = {\n",
        "    newtype Hidden = Hidden(Visible)\n",
        "    ()\n",
        "}\n",
    ))
    .resolve();
    let [local] = resolved.registry().lexical_nominals() else {
        panic!("expected one lexical nominal")
    };

    assert_eq!(resolved.registry().nominals().len(), 1);
    assert_eq!(resolved.registry().constructors().len(), 1);
    assert!(resolved.export_candidate().nominal("Visible").is_some());
    assert!(resolved.export_candidate().constructor("Visible").is_some());
    assert!(resolved.export_candidate().nominal("Hidden").is_none());
    assert!(resolved.export_candidate().constructor("Hidden").is_none());
    assert!(
        resolved
            .export_candidate()
            .hidden_nominal(local.id)
            .is_none()
    );
    assert!(!resolved.export_candidate().is_private("Hidden"));
    assert!(resolved.imported_facts().nominal(local.id).is_none());
    assert!(
        resolved
            .imported_facts()
            .constructor(resolved.registry().lexical_constructors()[0].id)
            .is_none()
    );
}
