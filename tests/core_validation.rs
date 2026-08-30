use ash::{
    core::{
        BuildError, CORE_PAYLOAD_DEPTH_LIMIT, CoreBuilder, CoreMatchArm, CorePattern,
        CorePatternKind, Primitive, PureComputation, PureExprKind, PureValue, ValidatedProgram,
        ValidationReason,
        transform::{fold_literal_primitives, identity_traversal},
        validate,
    },
    driver::{RunConfiguration, run_path},
    elaborate::{Elaborator, check_module, link_modules},
    eval::{Value, evaluate},
    evidence_validation::validate_interface_evidence,
    integer::Integer,
    interface::{EvidenceNode, ImplId, ImplMethodId, InterfaceId},
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{
        BinderId, ResolvedConstructor, ResolvedDefinitionKind, ResolvedExprKind,
        ResolvedNominalType, ResolvedRegistry, ResolvedTermName, ResolvedTypeVariable,
    },
    source::{ByteRange, GeneratedReason, Origin, SourceFile},
    surface::SurfaceKindKind,
    types::{
        ConstructorId, InferenceVariableId, Kind, NominalTypeId, Type, TypeVariableId, same_type,
    },
};
use std::{
    collections::HashSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

static INTERFACE_CORE_FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

struct InterfaceCoreFixture(PathBuf);

impl InterfaceCoreFixture {
    fn create(text: &str) -> Self {
        loop {
            let id = INTERFACE_CORE_FIXTURE_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir().join(format!(
                "ash-core-interface-check-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join("entry.ash");
                    fs::write(&path, text).expect("the Core interface fixture should be writable");
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("the Core interface fixture should be creatable: {error}"),
            }
        }
    }
}

impl Drop for InterfaceCoreFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn validated_interface_core(text: &str) -> ValidatedProgram {
    validated_interface_core_with_graph(text).0
}

fn validated_interface_core_with_graph(text: &str) -> (ValidatedProgram, ModuleGraph) {
    let fixture = InterfaceCoreFixture::create(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the Core interface fixture should load");
    let module = graph
        .module(graph.entry())
        .expect("the Core interface entry should remain admitted");
    let resolved = resolve_module(module, &[]).expect("the Core interface fixture should resolve");
    let checked = check_module(resolved).expect("the Core interface fixture should check");
    let linked =
        link_modules(vec![checked], graph.entry()).expect("the Core interface fixture should link");
    let linked = validate_interface_evidence(linked)
        .expect("the Core interface evidence should authenticate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("the linked namespace should reserve");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("the authenticated interface evidence should lower");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the authenticated interface Core should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let program = ash::core::validate_modules(unchecked, &sources, &module_sources)
        .expect("the authenticated interface Core should independently validate");
    (program, graph)
}

fn reachable_nodes(program: &ValidatedProgram) -> Vec<ash::core::NodeId> {
    let mut pending = vec![program.root()];
    let mut visited = HashSet::new();
    let mut nodes = Vec::new();
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }
        let node = program
            .node(id)
            .expect("every reachable Core handle should belong to the program");
        pending.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
        nodes.push(id);
    }
    nodes
}

fn linked_product_entry() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/explicit-kinds/linked-product/entry.ash")
}

fn linked_relational_entry() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/relational-interfaces/linked-composite/entry.ash")
}

fn module_named<'a>(graph: &'a ModuleGraph, name: &str) -> &'a LoadedModule {
    graph
        .modules()
        .iter()
        .find(|module| module.canonical_path().file_name() == Some(name.as_ref()))
        .expect("the static linked product module should load")
}

fn assert_type_to_type(kind: &Kind) {
    assert_eq!(
        kind,
        &Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
    );
}

fn assert_surface_type_to_type(kind: &SurfaceKindKind) {
    let SurfaceKindKind::Function { domain, codomain } = kind else {
        panic!("the projected kind should retain its source arrow");
    };
    assert!(matches!(domain.kind, SurfaceKindKind::Type));
    assert!(matches!(codomain.kind, SurfaceKindKind::Type));
}

fn assert_higher_kinded_linked_core(
    program: &ValidatedProgram,
    option: NominalTypeId,
    relay: BinderId,
    relay_parameter: TypeVariableId,
) {
    let mut work = vec![program.root()];
    let mut relay_abstraction = None;
    let mut relay_instantiation = None;
    while let Some(id) = work.pop() {
        let node = program
            .node(id)
            .expect("every linked Core child should belong to the validated arena");
        match &node.kind {
            PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                for member in group.members() {
                    if member.binder().id() == relay {
                        assert!(
                            relay_abstraction.replace(member.initializer()).is_none(),
                            "relay should have exactly one linked recursive definition",
                        );
                    }
                }
            }
            PureExprKind::Computation(PureComputation::TypeApplication(application)) => {
                let function = program
                    .node(application.function())
                    .expect("the linked type application function should exist");
                if matches!(
                    function.kind,
                    PureExprKind::Variable(variable) if variable.binder() == relay
                ) {
                    assert!(
                        relay_instantiation.replace(id).is_none(),
                        "relay should have exactly one linked type instantiation",
                    );
                }
            }
            PureExprKind::Value(_)
            | PureExprKind::Variable(_)
            | PureExprKind::Computation(
                PureComputation::Bind(_)
                | PureComputation::Apply(_)
                | PureComputation::Primitive(_)
                | PureComputation::Tuple(_)
                | PureComputation::Match(_)
                | PureComputation::TypeAbstraction(_),
            ) => {}
        }
        work.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
    }

    let abstraction_id = relay_abstraction.expect("relay should retain its linked initializer");
    let abstraction_node = program
        .node(abstraction_id)
        .expect("relay's linked initializer should exist");
    let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
        &abstraction_node.kind
    else {
        panic!("relay should retain an explicit outer type abstraction");
    };
    assert_eq!(abstraction.parameters().len(), 1);
    assert_eq!(abstraction.parameters()[0].0, relay_parameter);
    assert!(matches!(abstraction.parameters()[0].1, Kind::Arrow(_, _)));
    let Type::Forall(scheme_parameters, scheme_body) = &abstraction_node.ty else {
        panic!("relay's abstraction should expose its outer Forall");
    };
    assert_eq!(scheme_parameters.as_ref(), abstraction.parameters());
    assert!(same_type(
        &program
            .node(abstraction.body())
            .expect("relay's abstraction body should exist")
            .ty,
        scheme_body,
    ));

    let instantiation_id =
        relay_instantiation.expect("the entry module should instantiate linked relay");
    let instantiation_node = program
        .node(instantiation_id)
        .expect("relay's linked type application should exist");
    let PureExprKind::Computation(PureComputation::TypeApplication(instantiation)) =
        &instantiation_node.kind
    else {
        panic!("relay should be used through an explicit type application");
    };
    let function = program
        .node(instantiation.function())
        .expect("relay's type-application function should exist");
    assert!(same_type(&function.ty, &abstraction_node.ty));
    assert_eq!(instantiation.arguments(), &[Type::Nominal(option)]);
    let option_int = Type::Application(Box::new(Type::Nominal(option)), Box::new(Type::Int));
    let substituted = Type::Function(Box::new(option_int.clone()), Box::new(option_int));
    assert!(same_type(&instantiation_node.ty, &substituted));
}

fn assert_primitive_profile(
    program: &ValidatedProgram,
    expected_additions: usize,
    expected_folded_forty_twos: usize,
) {
    let forty_two = Integer::parse_decimal("42").expect("the folded result should parse");
    let mut work = vec![program.root()];
    let mut visited = HashSet::new();
    let mut additions = 0;
    let mut folded_forty_twos = 0;
    while let Some(id) = work.pop() {
        if !visited.insert(id) {
            continue;
        }
        let node = program
            .node(id)
            .expect("every linked Core child should belong to the validated arena");
        if matches!(
            &node.kind,
            PureExprKind::Computation(PureComputation::Primitive(operation))
                if operation.primitive() == Primitive::Add
        ) {
            additions += 1;
        }
        if matches!(
            &node.kind,
            PureExprKind::Value(PureValue::Integer(integer))
                if integer.value() == &forty_two
                    && node.origin.generated_reason() == Some(GeneratedReason::ConstantFolding)
        ) {
            folded_forty_twos += 1;
        }
        work.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
    }
    assert_eq!(additions, expected_additions);
    assert_eq!(folded_forty_twos, expected_folded_forty_twos);
}

fn assert_integer_evaluation(program: &ValidatedProgram, expected: &str) {
    let evaluation = evaluate(program).expect("validated linked Core should erase and evaluate");
    let Value::Integer(value) = evaluation.value else {
        panic!("the transformed linked program should evaluate to an integer");
    };
    assert_eq!(
        value,
        Integer::parse_decimal(expected).expect("the expected integer should parse"),
    );
}

#[test]
fn abstract_polymorphic_method_evidence_instantiates_at_retained_arguments() {
    let program = validated_interface_core(concat!(
        "interface Pairing<I> {\n",
        "pair<A, B> : (I, A, B) -> (A, B)\n",
        "}\n\n",
        "impl Pairing<Int> {\n",
        "pair (owner, left, right) = (left, right)\n",
        "}\n\n",
        "use_pairing<I> : I -> (Int, Bool) where Pairing<I>\n",
        "use_pairing owner = pair((owner, 1, true))\n\n",
        "main : Unit -> (Int, Bool)\n",
        "main () = use_pairing(42)\n",
    ));

    let mut evidence_binder = None;
    for id in reachable_nodes(&program) {
        let node = program.node(id).expect("the reachable node should exist");
        let PureExprKind::Value(PureValue::Function(function)) = &node.kind else {
            continue;
        };
        if matches!(function.parameter().ty(), Type::Forall(parameters, _) if parameters.len() == 2)
        {
            assert!(
                evidence_binder.replace(function.parameter().id()).is_none(),
                "the constrained definition should expose one polymorphic evidence binder",
            );
        }
    }
    let evidence_binder =
        evidence_binder.expect("the generated evidence domain should retain the method scheme");

    let applications = reachable_nodes(&program)
        .into_iter()
        .filter_map(|id| {
            let node = program.node(id)?;
            let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                &node.kind
            else {
                return None;
            };
            let function = program.node(application.function())?;
            matches!(
                function.kind,
                PureExprKind::Variable(variable) if variable.binder() == evidence_binder
            )
            .then(|| application.arguments().to_vec())
        })
        .collect::<Vec<_>>();
    assert_eq!(
        applications,
        [vec![Type::Int, Type::Bool]],
        "the abstract evidence occurrence must instantiate the complete retained method arguments once",
    );
}

#[test]
fn complete_interface_application_authenticates_before_method_arguments() {
    let (program, graph) = validated_interface_core_with_graph(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "type Wrap<A> = Wrap(A)\n\n",
        "interface Combine<F : Type -> Type, Item> {\n",
        "combine<X> : (F<Item>, Item, X) -> Int\n",
        "}\n\n",
        "impl<F : Type -> Type, A> Combine<F, Wrap<A>> {\n",
        "combine (container, item, ignored) = 42\n",
        "}\n\n",
        "use_combine<F : Type -> Type, A> : (F<Wrap<A>>, Wrap<A>) -> Int where Combine<F, Wrap<A>>\n",
        "use_combine (container, item) = combine((container, item, true))\n\n",
        "main : Unit -> Int\n",
        "main () = use_combine((Some(Wrap(0)), Wrap(42)))\n",
    ));

    assert_integer_evaluation(&program, "42");
    let option = program
        .registry()
        .nominals()
        .iter()
        .find(|nominal| nominal.spelling == "Option")
        .expect("the higher-kinded interface argument should retain Option")
        .id;
    let mut aligned_adapter_application = None;
    let mut method_local_application = None;
    for id in reachable_nodes(&program) {
        let node = program
            .node(id)
            .expect("the reachable Core node should exist");
        let PureExprKind::Computation(PureComputation::TypeApplication(application)) = &node.kind
        else {
            continue;
        };
        let function = program
            .node(application.function())
            .expect("the aligned method application function should exist");
        match application.arguments() {
            [
                Type::Nominal(actual_option),
                Type::Int,
                Type::Variable(method_argument),
            ] if *actual_option == option => {
                let Type::Forall(parameters, _) = &function.ty else {
                    panic!("the aligned adapter application should consume one Core scheme");
                };
                assert_eq!(parameters.len(), 3);
                assert_type_to_type(&parameters[0].1);
                assert_eq!(parameters[1].1, Kind::Type);
                assert_eq!(parameters[2].1, Kind::Type);
                assert!(matches!(method_argument, TypeVariableId::Generated(_)));
                assert!(
                    aligned_adapter_application.replace(id).is_none(),
                    "the adapter should apply the interface-derived head prefix once",
                );
            }
            [Type::Bool] => {
                let Type::Forall(parameters, _) = &function.ty else {
                    continue;
                };
                if parameters.len() == 1 && parameters[0].1 == Kind::Type {
                    assert!(
                        method_local_application.replace(id).is_none(),
                        "the method-local suffix should instantiate once",
                    );
                }
            }
            _ => {}
        }
    }
    assert!(
        aligned_adapter_application.is_some(),
        "Core must apply interface-derived [F, A] before the forwarded method-local X",
    );
    assert!(
        method_local_application.is_some(),
        "the source call must instantiate method-local X only after the interface application",
    );
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let identity = identity_traversal(&program)
        .expect("identity traversal should preserve the complete interface application");
    let identity = ash::core::validate_modules(identity, &sources, &module_sources)
        .expect("identity traversal should independently revalidate complete authentication");
    assert_integer_evaluation(&identity, "42");
    let folded = fold_literal_primitives(&program)
        .expect("literal folding should preserve the complete interface application");
    let folded = ash::core::validate_modules(folded, &sources, &module_sources)
        .expect("literal folding should independently revalidate complete authentication");
    assert_integer_evaluation(&folded, "42");
}

#[test]
fn concrete_method_evidence_uses_one_generated_adapter() {
    let program = validated_interface_core(concat!(
        "type Wrap<A> = Wrap(A)\n\n",
        "interface Base<I> {\n",
        "base : I -> I\n",
        "}\n\n",
        "interface Convert<I> {\n",
        "convert<X> : (I, X) -> I\n",
        "}\n\n",
        "impl Base<Int> {\n",
        "base value = value\n",
        "}\n\n",
        "impl<A> Convert<Wrap<A>> where Base<A> {\n",
        "convert (Wrap(value), ignored) = Wrap(base(value))\n",
        "}\n\n",
        "main : Unit -> Wrap<Int>\n",
        "main () = convert((Wrap(42), true))\n",
    ));

    let mut recursive_initializers = HashSet::new();
    for id in reachable_nodes(&program) {
        let node = program.node(id).expect("the reachable node should exist");
        if let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &node.kind {
            recursive_initializers
                .extend(group.members().iter().map(|member| member.initializer()));
        }
    }

    let adapters = reachable_nodes(&program)
        .into_iter()
        .filter(|id| {
            matches!(
                &program.node(*id).expect("the reachable node should exist").kind,
                PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction))
                    if abstraction.parameters().len() == 1 && !recursive_initializers.contains(id)
            )
        })
        .collect::<Vec<_>>();
    let [adapter] = adapters.as_slice() else {
        panic!("the concrete method selection should create exactly one expression-local adapter");
    };
    let adapter_node = program.node(*adapter).expect("the adapter should exist");
    let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
        &adapter_node.kind
    else {
        unreachable!("the selected adapter node is a type abstraction")
    };
    let [(method_parameter, Kind::Type)] = abstraction.parameters() else {
        panic!("the adapter should bind the one declared method parameter at its exact kind");
    };
    let body = program
        .node(abstraction.body())
        .expect("the adapter body should exist");
    let PureExprKind::Computation(PureComputation::Apply(prerequisite_application)) = &body.kind
    else {
        panic!("the adapter should apply prerequisite evidence after type instantiation");
    };
    let type_application = program
        .node(prerequisite_application.function())
        .expect("the adapter's type application should exist");
    let PureExprKind::Computation(PureComputation::TypeApplication(type_application)) =
        &type_application.kind
    else {
        panic!("the implementation method must be type-applied before prerequisites");
    };
    assert_eq!(
        type_application.arguments(),
        &[Type::Int, Type::Variable(*method_parameter)],
        "implementation head arguments must precede the adapter's method arguments",
    );
    assert!(matches!(
        program
            .node(type_application.function())
            .expect("the original implementation-method occurrence should exist")
            .kind,
        PureExprKind::Variable(_)
    ));
    assert!(matches!(
        program
            .node(prerequisite_application.argument())
            .expect("the prerequisite evidence occurrence should exist")
            .kind,
        PureExprKind::Variable(_)
    ));
}

#[test]
fn polymorphic_method_domains_follow_declaration_order() {
    let program = validated_interface_core(concat!(
        "interface Ordered<I> {\n",
        "first<A> : (I, A) -> A\n",
        "second<A, B> : (I, A, B) -> B\n",
        "}\n\n",
        "impl Ordered<Int> {\n",
        "first (owner, value) = value\n",
        "second (owner, left, right) = right\n",
        "}\n\n",
        "use<I> : I -> (Int, Bool) where Ordered<I>\n",
        "use owner = (first((owner, 1)), second((owner, 1, true)))\n\n",
        "main : Unit -> (Int, Bool)\n",
        "main () = use(42)\n",
    ));

    let mut ordered_chain = None;
    for id in reachable_nodes(&program) {
        let Some(node) = program.node(id) else {
            continue;
        };
        let PureExprKind::Value(PureValue::Function(first)) = &node.kind else {
            continue;
        };
        let Type::Forall(first_parameters, _) = first.parameter().ty() else {
            continue;
        };
        let Some(second_node) = program.node(first.body()) else {
            continue;
        };
        let PureExprKind::Value(PureValue::Function(second)) = &second_node.kind else {
            continue;
        };
        let Type::Forall(second_parameters, _) = second.parameter().ty() else {
            continue;
        };
        if first_parameters.len() == 1 && second_parameters.len() == 2 {
            assert!(ordered_chain.replace((id, first.body())).is_none());
        }
    }
    assert!(
        ordered_chain.is_some(),
        "the two polymorphic domains must link in declaration order"
    );
}

#[test]
fn polymorphic_evidence_forwards_directly_between_matching_domains() {
    let program = validated_interface_core(concat!(
        "interface Forward<I> {\n",
        "forward<A> : (I, A) -> A\n",
        "}\n\n",
        "impl Forward<Int> {\n",
        "forward (owner, value) = value\n",
        "}\n\n",
        "inner<I> : I -> Int where Forward<I>\n",
        "inner owner = forward((owner, 1))\n\n",
        "outer<I> : I -> Int where Forward<I>\n",
        "outer owner = inner(owner)\n\n",
        "main : Unit -> Int\n",
        "main () = outer(42)\n",
    ));

    let direct_forwards = reachable_nodes(&program)
        .into_iter()
        .filter(|id| {
            let Some(node) = program.node(*id) else { return false };
            let PureExprKind::Computation(PureComputation::Apply(application)) = &node.kind else { return false };
            let Some(function) = program.node(application.function()) else { return false };
            let Some(argument) = program.node(application.argument()) else { return false };
            matches!(function.ty, Type::Function(ref domain, _) if matches!(domain.as_ref(), Type::Forall(_, _)))
                && matches!(argument.kind, PureExprKind::Variable(_))
        })
        .count();
    assert_eq!(
        direct_forwards, 1,
        "forwarding must supply the matching evidence variable directly once"
    );
}

#[test]
fn exact_current_polymorphic_adapter_reuses_abstract_prerequisites() {
    let program = validated_interface_core(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Score<A> {\n",
        "score<X> : (A, X) -> Int\n",
        "}\n\n",
        "impl Score<Int> {\n",
        "score (value, ignored) = value\n",
        "}\n\n",
        "impl Score<Option<A>> where Score<A> {\n",
        "score (None, ignored) = 4\n",
        "score (Some(value), ignored) = {\n",
        "let empty : Option<A> = None\n",
        "score((empty, ignored)) * 10 + score((value, ignored))\n",
        "}\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = score((Some(2), true))\n",
    ));

    let abstract_prerequisite_adapters = reachable_nodes(&program)
        .into_iter()
        .filter(|id| {
            let Some(node) = program.node(*id) else {
                return false;
            };
            let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                &node.kind
            else {
                return false;
            };
            let Some(body) = program.node(abstraction.body()) else {
                return false;
            };
            let PureExprKind::Computation(PureComputation::Apply(application)) = &body.kind else {
                return false;
            };
            program
                .node(application.argument())
                .is_some_and(|argument| matches!(argument.kind, PureExprKind::Variable(_)))
        })
        .count();
    assert!(
        abstract_prerequisite_adapters >= 1,
        "the exact-current adapter must reuse its active abstract prerequisite"
    );
}

#[test]
fn nested_same_implementation_selections_keep_distinct_polymorphic_adapters() {
    let (program, graph) = validated_interface_core_with_graph(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Score<A> {\n",
        "score<X> : (A, X) -> Int\n",
        "}\n\n",
        "impl Score<Int> {\n",
        "score (value, ignored) = value\n",
        "}\n\n",
        "impl Score<Option<A>> where Score<A> {\n",
        "score (None, ignored) = 4\n",
        "score (Some(value), ignored) = {\n",
        "let empty : Option<A> = None\n",
        "score((empty, ignored)) * 10 + score((value, ignored))\n",
        "}\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = score((Some(Some(2)), true))\n",
    ));

    let recursive_initializers = reachable_nodes(&program)
        .into_iter()
        .filter_map(|id| {
            let node = program.node(id)?;
            let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &node.kind
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
    let mut adapter_heads = Vec::new();
    for id in reachable_nodes(&program) {
        if recursive_initializers.contains(&id) {
            continue;
        }
        let Some(node) = program.node(id) else {
            continue;
        };
        let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) = &node.kind
        else {
            continue;
        };
        let mut current = abstraction.body();
        while let Some(node) = program.node(current) {
            match &node.kind {
                PureExprKind::Computation(PureComputation::Apply(application)) => {
                    current = application.function();
                }
                PureExprKind::Computation(PureComputation::TypeApplication(application)) => {
                    if let Some(head) = application
                        .arguments()
                        .first()
                        .filter(|head| !matches!(head, Type::Variable(_)))
                        && let Some(function) = program.node(application.function())
                        && let PureExprKind::Variable(variable) = &function.kind
                    {
                        adapter_heads.push((variable.binder(), head.clone()));
                    }
                    break;
                }
                _ => break,
            }
        }
    }
    assert_eq!(
        adapter_heads.len(),
        2,
        "both selected evidence nodes need adapters"
    );
    assert!(
        adapter_heads[0].0 == adapter_heads[1].0,
        "both adapters must apply the same implementation method binder",
    );
    assert!(
        !same_type(&adapter_heads[0].1, &adapter_heads[1].1),
        "the same implementation identity must retain distinct head substitutions",
    );
    assert_integer_evaluation(&program, "82");

    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let identity = identity_traversal(&program).expect("identity must preserve both adapters");
    let identity = ash::core::validate_modules(identity, &sources, &module_sources)
        .expect("identity output must freshly validate both adapters");
    assert_integer_evaluation(&identity, "82");
    let folded = fold_literal_primitives(&program).expect("folding must preserve both adapters");
    let folded = ash::core::validate_modules(folded, &sources, &module_sources)
        .expect("fold output must freshly validate both adapters");
    assert_integer_evaluation(&folded, "82");
}

#[test]
fn linked_higher_kinded_core_revalidates_after_both_transforms() {
    let entry = linked_product_entry();
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the linked higher-kinded Core graph should load");
    let dependency = module_named(&graph, "dependency.ash");
    let [surface_observe] = dependency.surface().interfaces.as_slice() else {
        panic!("the projected dependency should retain Observe");
    };
    assert_eq!(surface_observe.name.text, "Observe");
    assert_surface_type_to_type(
        &surface_observe.parameters[0]
            .kind
            .as_ref()
            .expect("Observe should retain its explicit kind")
            .kind,
    );
    let surface_relay = dependency
        .surface()
        .definitions
        .iter()
        .find_map(|definition| match &definition.kind {
            ash::surface::SurfaceDefinitionKind::Equational(global)
                if global.interface.name.text == "relay" =>
            {
                Some(&global.interface)
            }
            ash::surface::SurfaceDefinitionKind::Equational(_)
            | ash::surface::SurfaceDefinitionKind::InlineOperational(_) => None,
        })
        .expect("the projected dependency should retain relay");
    let [surface_relay_parameter] = surface_relay
        .type_parameters
        .as_deref()
        .expect("relay should retain its complete explicit binder list")
    else {
        panic!("relay should project exactly one explicit binder");
    };
    assert_surface_type_to_type(
        &surface_relay_parameter
            .kind
            .as_ref()
            .expect("relay should retain its explicit kind")
            .kind,
    );

    let resolved_dependency = resolve_module(dependency, &[])
        .expect("the dependency should resolve and kind-check without imports");
    let option = resolved_dependency
        .registry()
        .nominals()
        .iter()
        .find(|nominal| nominal.spelling == "Option")
        .expect("the defining Option identity should resolve")
        .id;
    let [option_parameter] = resolved_dependency
        .registry()
        .nominal_parameters(option)
        .expect("Option should retain its canonical parameter")
    else {
        panic!("Option should have one canonical parameter");
    };
    assert_eq!(option_parameter.kind, Kind::Type);
    let option_parameter = option_parameter.id;
    let some = resolved_dependency
        .registry()
        .constructors()
        .iter()
        .find(|constructor| constructor.spelling == "Some")
        .expect("the defining Some identity should resolve")
        .id;
    let [resolved_observe] = resolved_dependency.interfaces() else {
        panic!("Observe should be the only resolved interface");
    };
    assert_eq!(resolved_observe.spelling, "Observe");
    assert_type_to_type(&resolved_observe.parameters[0].kind);
    let observe: InterfaceId = resolved_observe.id;
    let [resolved_observe_method] = resolved_observe.methods.as_ref() else {
        panic!("Observe should resolve exactly one method");
    };
    let observe_method = resolved_observe_method.id;
    let [resolved_implementation] = resolved_dependency.implementations() else {
        panic!("the dependency should retain one implementation");
    };
    assert_eq!(resolved_implementation.head.interface.id, observe);
    let implementation: ImplId = resolved_implementation.id;
    let resolved_relay = resolved_dependency
        .definitions()
        .iter()
        .find_map(|definition| match &definition.kind {
            ResolvedDefinitionKind::Equational(global)
                if global.interface.name.spelling == "relay" =>
            {
                Some(&global.interface)
            }
            ResolvedDefinitionKind::Equational(_)
            | ResolvedDefinitionKind::InlineOperational(_) => None,
        })
        .expect("relay should retain its resolved global identity");
    let relay = resolved_relay.name.id;
    let [resolved_relay_parameter] = resolved_relay.type_parameters.as_ref() else {
        panic!("relay should resolve exactly one binder");
    };
    assert_type_to_type(&resolved_relay_parameter.kind);
    let relay_parameter = resolved_relay_parameter.id;

    let checked_dependency = check_module(resolved_dependency)
        .expect("the kinded dependency should complete ordinary type checking");
    let [checked_observe] = checked_dependency.interface_facts() else {
        panic!("the checked dependency should retain one interface fact");
    };
    assert_eq!(checked_observe.id, observe);
    let [checked_observe_parameter] = checked_observe.parameters.as_ref() else {
        panic!("the checked interface should retain one parameter");
    };
    assert_type_to_type(&checked_observe_parameter.kind);
    let [checked_implementation] = checked_dependency.implementation_facts() else {
        panic!("the checked dependency should retain one implementation fact");
    };
    assert_eq!(checked_implementation.id, implementation);
    assert_eq!(checked_implementation.interface(), observe);
    assert_eq!(checked_implementation.arguments(), [Type::Nominal(option)]);
    let checked_relay = checked_dependency
        .schemes()
        .iter()
        .find(|scheme| scheme.binder == relay)
        .expect("the checked dependency should retain relay's scheme");
    assert_eq!(
        checked_relay.scheme.type_parameters.as_ref(),
        [(
            relay_parameter,
            Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
        )],
    );

    let dependency_summary = checked_dependency.into_exports();
    let entry_module = module_named(&graph, "entry.ash");
    let [entry_edge] = entry_module.dependencies() else {
        panic!("the entry should have one direct dependency");
    };
    let detached_dependency = DependencyExports::new(entry_edge, &dependency_summary)
        .expect("the detached summary should authenticate its import edge");
    let resolved_entry = resolve_module(entry_module, &[detached_dependency])
        .expect("the entry should resolve and kind-check solely from the detached summary");
    let imported = resolved_entry.imported_facts();
    let imported_option = imported
        .nominal(option)
        .expect("the entry should import Option's canonical fact");
    assert_eq!(imported_option.id, option);
    let [imported_option_parameter] = imported_option.parameters.as_ref() else {
        panic!("the imported Option fact should retain one parameter");
    };
    assert_eq!(imported_option_parameter.id, option_parameter);
    assert_eq!(imported_option_parameter.kind, Kind::Type);
    assert!(imported_option.constructors.contains(&some));
    let imported_some = imported
        .constructor(some)
        .expect("the entry should import Some's physical constructor fact");
    assert_eq!(imported_some.id, some);
    assert_eq!(imported_some.spelling, "Some");
    assert_eq!(
        imported_some.payload.as_ref(),
        Some(&Type::Variable(option_parameter)),
    );
    assert_eq!(
        imported_some.scheme.type_parameters.as_ref(),
        [(option_parameter, Kind::Type)],
    );
    assert!(imported_some.scheme.requirements.is_empty());
    assert_eq!(
        imported_some.scheme.value_type(),
        &Type::Function(
            Box::new(Type::Variable(option_parameter)),
            Box::new(Type::Application(
                Box::new(Type::Nominal(option)),
                Box::new(Type::Variable(option_parameter)),
            )),
        ),
    );
    let imported_observe = imported
        .interface(observe)
        .expect("the entry should import Observe's canonical fact");
    assert_eq!(imported_observe.id, observe);
    let [imported_observe_parameter] = imported_observe.parameters.as_ref() else {
        panic!("the imported interface should retain one parameter");
    };
    assert_type_to_type(&imported_observe_parameter.kind);
    let imported_relay = imported
        .global(relay)
        .expect("the entry should import relay's canonical scheme");
    assert_eq!(
        imported_relay.scheme.type_parameters.as_ref(),
        [(
            relay_parameter,
            Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
        )],
    );
    let imported_implementation = imported
        .implementation(implementation)
        .expect("the entry should import the selected Observe<Option> implementation");
    assert_eq!(imported_implementation.id, implementation);
    assert_eq!(imported_implementation.interface(), observe);
    assert_eq!(imported_implementation.arguments(), [Type::Nominal(option)]);
    let checked_entry = check_module(resolved_entry)
        .expect("the entry should type-check from detached imported facts");
    let main = checked_entry
        .definitions()
        .iter()
        .find_map(|definition| match definition.kind() {
            ResolvedDefinitionKind::Equational(global)
                if global.interface.name.spelling == "main" =>
            {
                Some(global)
            }
            ResolvedDefinitionKind::Equational(_)
            | ResolvedDefinitionKind::InlineOperational(_) => None,
        })
        .expect("the checked entry should retain main");
    let [main_equation] = main.equations.as_slice() else {
        panic!("main should retain exactly one equation");
    };
    let ResolvedExprKind::Apply(observe_application) = &main_equation.body.kind else {
        panic!("main's body should apply observe");
    };
    let ResolvedExprKind::Occurrence(observe_occurrence) = &observe_application.function.kind
    else {
        panic!("main's outer function should be the observe occurrence");
    };
    assert_eq!(
        observe_occurrence.term,
        ResolvedTermName::Method(observe_method),
    );
    let [observe_slot] = observe_occurrence.evidence.as_ref() else {
        panic!("observe should retain one occurrence-local evidence slot");
    };
    let observe_selection = observe_slot
        .selection()
        .expect("entry checking should fill observe's evidence slot");
    assert_eq!(observe_selection.interface(), observe);
    assert_eq!(observe_selection.arguments(), [Type::Nominal(option)]);
    assert_eq!(observe_selection.node_count(), 1);
    let Some(EvidenceNode::Implementation {
        implementation: selected_implementation,
        substitution,
        prerequisites,
        methods,
    }) = observe_selection.node(observe_selection.root())
    else {
        panic!("observe should select concrete implementation evidence");
    };
    assert_eq!(selected_implementation, implementation);
    assert!(substitution.is_empty());
    assert!(prerequisites.is_empty());
    assert_eq!(
        methods,
        &[ImplMethodId::new(implementation, observe_method)]
    );
    drop(dependency_summary);

    let rechecked_dependency = check_module(
        resolve_module(dependency, &[])
            .expect("the dependency should be re-resolved only to recover linkable bodies"),
    )
    .expect("the dependency bodies should recheck for final linking");
    let linked = link_modules(vec![rechecked_dependency, checked_entry], graph.entry())
        .expect("the checked higher-kinded graph should link");
    let linked = validate_interface_evidence(linked)
        .expect("linked higher-kinded evidence should authenticate");
    let dependency_group = linked
        .groups()
        .iter()
        .find(|group| group.module() == dependency.id())
        .expect("linked evidence should retain the dependency group");
    let [linked_observe] = dependency_group.interface_facts() else {
        panic!("linked evidence should retain one interface fact");
    };
    assert_eq!(linked_observe.id, observe);
    let [linked_implementation] = dependency_group.implementation_facts() else {
        panic!("linked evidence should retain one implementation fact");
    };
    assert_eq!(linked_implementation.id, implementation);
    assert_eq!(linked_implementation.interface(), observe);
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("the linked binder namespace should fit");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("authenticated linked kinds should lower to Core");
    assert_eq!(typed.ty, Type::Int);
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the linked Core root should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let original = ash::core::validate_modules(unchecked, &sources, &module_sources)
        .expect("linked higher-kinded Core should independently validate");
    let original_registry = Arc::clone(original.registry());
    assert_higher_kinded_linked_core(&original, option, relay, relay_parameter);
    assert_primitive_profile(&original, 1, 0);
    assert_integer_evaluation(&original, "42");
    let identity = identity_traversal(&original).expect("the identity transform should rebuild");
    let identity = ash::core::validate_modules(identity, &sources, &module_sources)
        .expect("the identity transform should independently revalidate");
    assert!(Arc::ptr_eq(identity.registry(), &original_registry));
    assert_higher_kinded_linked_core(&identity, option, relay, relay_parameter);
    assert_primitive_profile(&identity, 1, 0);
    assert_integer_evaluation(&identity, "42");
    let folded =
        fold_literal_primitives(&original).expect("literal folding should independently rebuild");
    let folded = ash::core::validate_modules(folded, &sources, &module_sources)
        .expect("literal folding should independently revalidate");
    assert!(Arc::ptr_eq(folded.registry(), &original_registry));
    assert_higher_kinded_linked_core(&folded, option, relay, relay_parameter);
    assert_primitive_profile(&folded, 0, 1);
    assert_integer_evaluation(&folded, "42");

    let observation = run_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("the static linked product should run through the public library path");
    let Value::Integer(value) = observation.value() else {
        panic!("the public library path should observe an integer");
    };
    assert_eq!(
        value,
        &Integer::parse_decimal("42").expect("42 should parse")
    );
    assert_eq!(observation.ty(), &Type::Int);

    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(&entry)
        .output()
        .expect("the Ash executable should run the static linked product");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn linked_relational_program_crosses_facade_diamond_transforms_and_runtime() {
    let entry = linked_relational_entry();
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the linked relational graph should load");
    let base_module = module_named(&graph, "base.ash");
    let entry_module = module_named(&graph, "entry.ash");
    let short_module = module_named(&graph, "short.ash");
    let long_one_module = module_named(&graph, "long_one.ash");
    let long_two_module = module_named(&graph, "long_two.ash");

    let mut checked = Vec::new();
    let mut relation = None;
    let mut relation_parameters = None;
    let mut relation_method = None;
    let mut implementation = None;
    let mut implementation_method_binder = None;
    let mut wrap = None;

    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked: &&ash::resolved::CheckedModule| {
                        checked.module() == edge.target()
                    })
                    .expect("the dependency should already have checked body-free exports");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the detached relational summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("every relational fixture module should resolve from summaries");

        if module.id() == base_module.id() {
            let [resolved_relation] = resolved.interfaces() else {
                panic!("the base should resolve one relational interface");
            };
            assert_eq!(resolved_relation.spelling, "Relation");
            assert_eq!(
                resolved_relation
                    .parameters
                    .iter()
                    .map(|parameter| parameter.spelling.as_str())
                    .collect::<Vec<_>>(),
                ["F", "Key", "Dep"],
            );
            assert_type_to_type(&resolved_relation.parameters[0].kind);
            assert_eq!(resolved_relation.parameters[1].kind, Kind::Type);
            assert_eq!(resolved_relation.parameters[2].kind, Kind::Type);
            relation = Some(resolved_relation.id);
            relation_parameters = Some([
                resolved_relation.parameters[0].id,
                resolved_relation.parameters[1].id,
                resolved_relation.parameters[2].id,
            ]);
            let [method] = resolved_relation.methods.as_ref() else {
                panic!("Relation should resolve one polymorphic method");
            };
            let [method_parameter] = method.type_parameters.as_ref() else {
                panic!("relate should retain one method-local parameter");
            };
            assert_eq!(method_parameter.spelling, "X");
            relation_method = Some(method.id);

            let [resolved_implementation] = resolved.implementations() else {
                panic!("the base should resolve one public implementation");
            };
            implementation = Some(resolved_implementation.id);
            let [head_parameter] = resolved_implementation.head_parameters.as_ref() else {
                panic!("the relational implementation should retain one head parameter");
            };
            assert_eq!(head_parameter.spelling, "A");
            let [method_group] = resolved_implementation.method_groups.as_ref() else {
                panic!("the implementation should retain one method body");
            };
            implementation_method_binder = Some(method_group.binder.id);
            wrap = Some(
                resolved
                    .registry()
                    .nominals()
                    .iter()
                    .find(|nominal| nominal.spelling == "Wrap")
                    .expect("the base should retain Wrap")
                    .id,
            );
        } else {
            if matches!(
                module.id(),
                id if id == short_module.id()
                    || id == long_one_module.id()
                    || id == long_two_module.id()
                    || id == entry_module.id()
            ) {
                let relation = relation.expect("the base should resolve before its facades");
                let implementation =
                    implementation.expect("the base implementation should already exist");
                assert_eq!(
                    resolved
                        .imported_facts()
                        .interface(relation)
                        .map(|fact| fact.id),
                    Some(relation),
                    "every facade route must preserve the defining interface identity",
                );
                assert_eq!(
                    resolved
                        .imported_facts()
                        .implementation(implementation)
                        .map(|fact| fact.id),
                    Some(implementation),
                    "every facade route must preserve the defining implementation identity",
                );
            }
        }

        let module_checked = check_module(resolved)
            .expect("every relational fixture module should check independently");
        if module.id() == base_module.id() {
            let relation = relation.expect("the base relation identity should be retained");
            let relation_parameters =
                relation_parameters.expect("the interface parameter order should be retained");
            let relation_method = relation_method.expect("the method identity should be retained");
            let implementation =
                implementation.expect("the implementation identity should be retained");
            let wrap = wrap.expect("the Wrap identity should be retained");
            let [interface_fact] = module_checked.interface_facts() else {
                panic!("the checked base should retain one interface fact");
            };
            assert_eq!(interface_fact.id, relation);
            assert_eq!(
                interface_fact
                    .parameters
                    .iter()
                    .map(|parameter| parameter.id)
                    .collect::<Vec<_>>(),
                relation_parameters,
            );
            let [implementation_fact] = module_checked.implementation_facts() else {
                panic!("the checked base should retain one implementation fact");
            };
            assert_eq!(implementation_fact.id, implementation);
            assert_eq!(implementation_fact.interface(), relation);
            assert_eq!(implementation_fact.arguments().len(), 3);
            assert_eq!(implementation_fact.arguments()[0], Type::Nominal(wrap));
            assert!(matches!(
                &implementation_fact.arguments()[1],
                Type::Application(function, argument)
                    if function.as_ref() == &Type::Nominal(wrap)
                        && argument.as_ref()
                            == &Type::Variable(implementation_fact.head_parameters[0].id)
            ));
            assert_eq!(
                implementation_fact.arguments()[2],
                Type::Variable(implementation_fact.head_parameters[0].id),
            );

            let relay = module_checked
                .definitions()
                .iter()
                .find_map(|definition| match definition.kind() {
                    ResolvedDefinitionKind::Equational(global)
                        if global.interface.name.spelling == "relay" =>
                    {
                        Some(global)
                    }
                    ResolvedDefinitionKind::Equational(_)
                    | ResolvedDefinitionKind::InlineOperational(_) => None,
                })
                .expect("the checked base should retain relay");
            let ResolvedExprKind::Apply(call) = &relay.equations[0].body.kind else {
                panic!("relay should call the interface method");
            };
            let ResolvedExprKind::Occurrence(occurrence) = &call.function.kind else {
                panic!("relay should retain the abstract method occurrence");
            };
            assert_eq!(occurrence.term, ResolvedTermName::Method(relation_method));
            let [slot] = occurrence.evidence.as_ref() else {
                panic!("the abstract method occurrence should own one evidence slot");
            };
            let selection = slot
                .selection()
                .expect("base checking should fill abstract method evidence");
            assert_eq!(selection.interface(), relation);
            assert_eq!(selection.arguments().len(), 3);
            assert_eq!(slot.method_arguments().len(), 1);
            assert!(matches!(
                selection.node(selection.root()),
                Some(EvidenceNode::Abstract { methods, .. }) if methods == [relation_method]
            ));
        }
        if module.id() == entry_module.id() {
            let relation = relation.expect("the entry should preserve Relation");
            let implementation = implementation.expect("the entry should preserve the impl");
            let wrap = wrap.expect("the entry should preserve Wrap");
            let [available] = module_checked.available_implementations() else {
                panic!("the diamond should deduplicate one effective implementation");
            };
            assert_eq!(available.id(), implementation);
            assert_eq!(
                available.authorization().hops().len(),
                2,
                "the unequal diamond must retain the shorter entry-short-base route",
            );

            let main = module_checked
                .definitions()
                .iter()
                .find_map(|definition| match definition.kind() {
                    ResolvedDefinitionKind::Equational(global)
                        if global.interface.name.spelling == "main" =>
                    {
                        Some(global)
                    }
                    ResolvedDefinitionKind::Equational(_)
                    | ResolvedDefinitionKind::InlineOperational(_) => None,
                })
                .expect("the checked entry should retain main");
            let ResolvedExprKind::Apply(reveal_call) = &main.equations[0].body.kind else {
                panic!("main should call reveal");
            };
            let ResolvedExprKind::Apply(relay_call) = &reveal_call.argument.kind else {
                panic!("main should call relay before reveal");
            };
            let ResolvedExprKind::Occurrence(relay_occurrence) = &relay_call.function.kind else {
                panic!("main should retain the constrained relay occurrence");
            };
            let [slot] = relay_occurrence.evidence.as_ref() else {
                panic!("relay should own one concrete evidence slot");
            };
            let selection = slot
                .selection()
                .expect("entry checking should fill concrete implementation evidence");
            assert_eq!(selection.interface(), relation);
            assert_eq!(
                selection.arguments(),
                [
                    Type::Nominal(wrap),
                    Type::Application(Box::new(Type::Nominal(wrap)), Box::new(Type::Int)),
                    Type::Int,
                ],
            );
            assert!(matches!(
                selection.node(selection.root()),
                Some(EvidenceNode::Implementation {
                    implementation: selected,
                    substitution,
                    prerequisites: [],
                    ..
                }) if selected == implementation
                    && substitution.len() == 1
                    && substitution[0].argument() == &Type::Int
            ));
        }
        checked.push(module_checked);
    }

    let linked =
        link_modules(checked, graph.entry()).expect("the checked relational diamond should link");
    let linked = validate_interface_evidence(linked)
        .expect("the complete relational applications and routes should authenticate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("the relational namespace should reserve");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("the authenticated relational program should lower");
    assert_eq!(typed.ty, Type::Int);
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the relational Core root should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let original = ash::core::validate_modules(unchecked, &sources, &module_sources)
        .expect("relational Core should independently validate");
    let implementation_method_binder =
        implementation_method_binder.expect("the implementation binder should be retained");
    let adapter_applications = reachable_nodes(&original)
        .into_iter()
        .filter_map(|node| {
            let payload = original.node(node)?;
            let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                &payload.kind
            else {
                return None;
            };
            let function = original.node(application.function())?;
            matches!(
                function.kind,
                PureExprKind::Variable(variable)
                    if variable.binder() == implementation_method_binder
            )
            .then_some((node, application.arguments()))
        })
        .collect::<Vec<_>>();
    let [(adapter_application, adapter_arguments)] = adapter_applications.as_slice() else {
        panic!("the generic implementation should retain one generated adapter application");
    };
    let [Type::Int, Type::Variable(method_argument)] = adapter_arguments else {
        panic!("the implementation-head argument must precede the method-local argument");
    };
    assert!(reachable_nodes(&original).into_iter().any(|node| {
        matches!(
            &original
                .node(node)
                .expect("the adapter abstraction should remain reachable")
                .kind,
            PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction))
                if abstraction.body() == *adapter_application
                    && abstraction.parameters() == [(*method_argument, Kind::Type)]
        )
    }));
    assert_primitive_profile(&original, 1, 0);
    assert_integer_evaluation(&original, "42");

    let identity = identity_traversal(&original)
        .expect("the identity transform should rebuild relational Core");
    let identity = ash::core::validate_modules(identity, &sources, &module_sources)
        .expect("identity-transformed relational Core should independently revalidate");
    assert_integer_evaluation(&identity, "42");
    let folded =
        fold_literal_primitives(&original).expect("literal folding should rebuild relational Core");
    let folded = ash::core::validate_modules(folded, &sources, &module_sources)
        .expect("folded relational Core should independently revalidate");
    assert_primitive_profile(&folded, 0, 1);
    assert_integer_evaluation(&folded, "42");

    let observation = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("the public driver path should run the body-free relational entry");
    assert_eq!(observation.ty(), &Type::Int);
    assert!(matches!(
        observation.value(),
        Value::Integer(value)
            if value == &Integer::parse_decimal("42").expect("42 should parse")
    ));
}

#[test]
fn structurally_validates_higher_kinded_outer_instantiation() {
    let file = source("PairPairValueABF");
    let origin = whole_origin(&file);
    let pair = NominalTypeId::new(file.id(), 0);
    let pair_value = ConstructorId::new(pair, 0);
    let pair_left = TypeVariableId::new(0);
    let pair_right = TypeVariableId::new(1);
    let outer = ResolvedTypeVariable {
        id: TypeVariableId::new(2),
        spelling: "F".into(),
        kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
        origin: range_origin(&file, 15, 16),
    };
    let registry = Arc::new(
        ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: pair,
                spelling: "Pair".into(),
                constructors: vec![pair_value].into_boxed_slice(),
                origin: range_origin(&file, 0, 15),
            }],
            vec![ResolvedConstructor {
                id: pair_value,
                owner: pair,
                spelling: "PairValue".into(),
                payload: None,
                origin: range_origin(&file, 4, 13),
            }],
        )
        .with_type_parameters(vec![(
            pair,
            vec![
                ResolvedTypeVariable {
                    id: pair_left,
                    spelling: "A".into(),
                    kind: Kind::Type,
                    origin: range_origin(&file, 13, 14),
                },
                ResolvedTypeVariable {
                    id: pair_right,
                    spelling: "B".into(),
                    kind: Kind::Type,
                    origin: range_origin(&file, 14, 15),
                },
            ],
        )]),
    );

    let mut builder = CoreBuilder::with_registry(registry);
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("outer abstraction body");
    let outer_scheme = Type::Forall(
        vec![(outer.id, outer.kind.clone())].into_boxed_slice(),
        Box::new(Type::Unit),
    );
    let abstraction = builder
        .type_abstraction(
            vec![(outer.id, outer.kind.clone())],
            body,
            outer_scheme,
            origin.clone(),
        )
        .expect("function-kinded outer abstraction");
    let partial_pair = Type::Application(Box::new(Type::Nominal(pair)), Box::new(Type::Int));
    let root = builder
        .type_application(abstraction, vec![partial_pair], Type::Unit, origin)
        .expect("simultaneous outer instantiation");

    validate(builder.finish(root).expect("Core root"), &[&file])
        .expect("a matching higher-kinded outer instantiation should validate");
}

#[test]
fn core_transforms_preserve_higher_kinded_outer_binders() {
    let file = source("transformed higher kind");
    let origin = whole_origin(&file);
    let parameter = TypeVariableId::new(0);
    let parameter_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
    let mut builder = CoreBuilder::new();
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("outer abstraction body");
    let root = builder
        .type_abstraction(
            vec![(parameter, parameter_kind.clone())],
            body,
            Type::Forall(
                vec![(parameter, parameter_kind.clone())].into_boxed_slice(),
                Box::new(Type::Unit),
            ),
            origin,
        )
        .expect("unchecked higher-kinded abstraction");
    let validated = validate(builder.finish(root).expect("Core root"), &[&file])
        .expect("source Core validates");

    for transformed in [
        identity_traversal(&validated).expect("identity transform"),
        fold_literal_primitives(&validated).expect("folding transform"),
    ] {
        let transformed = validate(transformed, &[&file]).expect("transformed Core revalidates");
        let node = transformed
            .node(transformed.root())
            .expect("transformed abstraction root");
        let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) = &node.kind
        else {
            panic!("transformed root remains a type abstraction");
        };
        assert_eq!(
            abstraction.parameters(),
            &[(parameter, parameter_kind.clone())]
        );
        assert!(matches!(
            &node.ty,
            Type::Forall(parameters, _) if parameters.as_ref() == [(parameter, parameter_kind.clone())]
        ));
    }
}

#[test]
fn rejects_outer_instantiation_argument_of_the_wrong_kind() {
    let file = source("wrong outer kind");
    let origin = whole_origin(&file);
    let parameter = TypeVariableId::new(0);
    let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
    let mut builder = CoreBuilder::new();
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("outer abstraction body");
    let abstraction = builder
        .type_abstraction(
            vec![(parameter, function_kind.clone())],
            body,
            Type::Forall(
                vec![(parameter, function_kind)].into_boxed_slice(),
                Box::new(Type::Unit),
            ),
            origin.clone(),
        )
        .expect("unchecked higher-kinded abstraction");
    let root = builder
        .type_application(abstraction, vec![Type::Int], Type::Unit, origin)
        .expect("unchecked wrong-kind instantiation");

    let error = validate(builder.finish(root).expect("Core root"), &[&file])
        .expect_err("a Type argument cannot instantiate a Type-to-Type binder");

    assert_eq!(error.reason(), ValidationReason::TypeOperation);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_disagreement_between_abstraction_and_outer_scheme_kinds() {
    let file = source("forged abstraction kind");
    let origin = whole_origin(&file);
    let parameter = TypeVariableId::new(0);
    let mut builder = CoreBuilder::new();
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("outer abstraction body");
    let root = builder
        .type_abstraction(
            vec![(
                parameter,
                Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            )],
            body,
            Type::Forall(
                vec![(parameter, Kind::Type)].into_boxed_slice(),
                Box::new(Type::Unit),
            ),
            origin,
        )
        .expect("unchecked mismatched abstraction");

    let error = validate(builder.finish(root).expect("Core root"), &[&file])
        .expect_err("the abstraction payload and scheme must retain the same kinds");

    assert_eq!(error.reason(), ValidationReason::TypeOperation);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_reordered_abstraction_and_outer_scheme_binders() {
    let file = source("reordered abstraction scheme");
    let origin = whole_origin(&file);
    let value_parameter = TypeVariableId::new(0);
    let constructor_parameter = TypeVariableId::new(1);
    let constructor_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
    let mut builder = CoreBuilder::new();
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("outer abstraction body");
    let root = builder
        .type_abstraction(
            vec![
                (value_parameter, Kind::Type),
                (constructor_parameter, constructor_kind.clone()),
            ],
            body,
            Type::Forall(
                vec![
                    (constructor_parameter, constructor_kind),
                    (value_parameter, Kind::Type),
                ]
                .into_boxed_slice(),
                Box::new(Type::Unit),
            ),
            origin,
        )
        .expect("unchecked reordered abstraction");

    let error = validate(builder.finish(root).expect("Core root"), &[&file])
        .expect_err("the abstraction payload and outer scheme have one canonical order");

    assert_eq!(error.reason(), ValidationReason::TypeOperation);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_nested_forall_as_an_outer_instantiation_argument() {
    let file = source("nested scheme argument");
    let origin = whole_origin(&file);
    let outer = TypeVariableId::new(0);
    let nested = TypeVariableId::new(1);
    let mut builder = CoreBuilder::new();
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("outer abstraction body");
    let abstraction = builder
        .type_abstraction(
            vec![(outer, Kind::Type)],
            body,
            Type::Forall(
                vec![(outer, Kind::Type)].into_boxed_slice(),
                Box::new(Type::Unit),
            ),
            origin.clone(),
        )
        .expect("unchecked outer abstraction");
    let nested_scheme = Type::Forall(
        vec![(nested, Kind::Type)].into_boxed_slice(),
        Box::new(Type::Int),
    );
    let root = builder
        .type_application(abstraction, vec![nested_scheme], Type::Unit, origin)
        .expect("unchecked nested-scheme instantiation");

    let error = validate(builder.finish(root).expect("Core root"), &[&file])
        .expect_err("Core type-application arguments must remain monomorphic");

    assert_eq!(error.reason(), ValidationReason::TypeOperation);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_non_type_ordinary_core_annotation() {
    let file = source("OptionParameterValue");
    let origin = whole_origin(&file);
    let option = NominalTypeId::new(file.id(), 0);
    let option_value = ConstructorId::new(option, 0);
    let parameter = ResolvedTypeVariable {
        id: TypeVariableId::new(0),
        spelling: "A".into(),
        kind: Kind::Type,
        origin: range_origin(&file, 6, 7),
    };
    let registry = ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: option,
            spelling: "Option".into(),
            constructors: Box::new([option_value]),
            origin: range_origin(&file, 0, 12),
        }],
        vec![ResolvedConstructor {
            id: option_value,
            owner: option,
            spelling: "Value".into(),
            payload: None,
            origin: range_origin(&file, 7, 12),
        }],
    )
    .with_type_parameters(vec![(option, vec![parameter])]);
    let mut builder = CoreBuilder::with_registry(Arc::new(registry));
    let binder = builder
        .binder(Type::Nominal(option), origin.clone())
        .expect("unchecked constructor-kinded binder");
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("function body");
    let root = builder
        .function(
            binder,
            body,
            Type::Function(Box::new(Type::Nominal(option)), Box::new(Type::Unit)),
            origin,
        )
        .expect("unchecked constructor-kinded function");

    let error = validate(builder.finish(root).expect("Core root"), &[&file])
        .expect_err("ordinary Core binders and node annotations must have kind Type");

    assert_eq!(error.reason(), ValidationReason::NodeType);
}

#[test]
fn rejects_higher_kinded_variable_as_ordinary_core_annotation() {
    let file = source("higher kind ordinary annotation");
    let origin = whole_origin(&file);
    let parameter = TypeVariableId::new(0);
    let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Variable(parameter), origin.clone())
        .expect("unchecked constructor-kinded binder");
    let unit = builder
        .unit(Type::Unit, origin.clone())
        .expect("function body");
    let function_type = Type::Function(Box::new(Type::Variable(parameter)), Box::new(Type::Unit));
    let function = builder
        .function(binder, unit, function_type.clone(), origin.clone())
        .expect("unchecked constructor-kinded function");
    let root = builder
        .type_abstraction(
            vec![(parameter, function_kind.clone())],
            function,
            Type::Forall(
                vec![(parameter, function_kind)].into_boxed_slice(),
                Box::new(function_type),
            ),
            origin,
        )
        .expect("unchecked outer abstraction");

    let error = validate(builder.finish(root).expect("Core root"), &[&file])
        .expect_err("ordinary Core annotations must synthesize Kind::Type");

    assert_eq!(error.reason(), ValidationReason::NodeType);
    assert_eq!(error.node(), Some(function));
}

#[test]
fn rejects_inference_escape_as_type_scope() {
    let file = source("escaped inference");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let root = builder
        .unit(Type::Inference(InferenceVariableId::new(0)), origin)
        .expect("unchecked inference annotation");

    let error = validate(builder.finish(root).expect("Core root"), &[&file])
        .expect_err("inference variables cannot escape into Core");

    assert_eq!(error.reason(), ValidationReason::TypeScope);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_malformed_explicit_type_operations_and_free_type_variables() {
    let file = source("explicit type operations");
    let origin = whole_origin(&file);
    let parameter = TypeVariableId::new(7);

    let mut builder = CoreBuilder::new();
    let body = builder.unit(Type::Unit, origin.clone()).expect("unit body");
    let abstraction = builder
        .type_abstraction(
            vec![(parameter, Kind::Type)],
            body,
            Type::Forall(
                vec![(parameter, Kind::Type)].into_boxed_slice(),
                Box::new(Type::Unit),
            ),
            origin.clone(),
        )
        .expect("unchecked abstraction");
    let malformed = builder
        .type_application(
            abstraction,
            vec![Type::Int, Type::Bool],
            Type::Unit,
            origin.clone(),
        )
        .expect("unchecked application");
    let error = validate(builder.finish(malformed).expect("root"), &[&file])
        .expect_err("type argument arity must be rechecked");
    assert_eq!(error.reason(), ValidationReason::TypeOperation);

    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Variable(parameter), origin.clone())
        .expect("unchecked parameter binder");
    let occurrence = builder
        .variable(binder.id(), Type::Variable(parameter), origin.clone())
        .expect("unchecked variable");
    let root = builder
        .function(
            binder,
            occurrence,
            Type::Function(
                Box::new(Type::Variable(parameter)),
                Box::new(Type::Variable(parameter)),
            ),
            origin,
        )
        .expect("unchecked function");
    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("a free Core type variable must not escape");
    assert_eq!(error.reason(), ValidationReason::TypeScope);
}

#[test]
fn rejects_polymorphic_match_domains() {
    let file = source("polymorphic match domain");
    let origin = whole_origin(&file);
    let parameter = TypeVariableId::new(0);
    let scheme = Type::Forall(
        vec![(parameter, Kind::Type)].into_boxed_slice(),
        Box::new(Type::Unit),
    );
    let mut builder = CoreBuilder::new();
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("abstraction body");
    let scrutinee = builder
        .type_abstraction(
            vec![(parameter, Kind::Type)],
            body,
            scheme.clone(),
            origin.clone(),
        )
        .expect("unchecked type abstraction");
    let arm_body = builder
        .unit(Type::Unit, origin.clone())
        .expect("match arm body");
    let arm = CoreMatchArm::new(
        CorePattern::new(scheme, origin.clone(), CorePatternKind::Wildcard),
        arm_body,
        origin.clone(),
    );
    let root = builder
        .match_expression(scrutinee, vec![arm], Type::Unit, origin)
        .expect("unchecked polymorphic match");

    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("match domains must remain monomorphic");

    assert_eq!(error.reason(), ValidationReason::Pattern);
}

#[test]
fn core_construction_charges_type_cells_cumulatively_before_storage() {
    let file = source("bounded type construction");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let function = builder
        .unit(Type::Unit, origin.clone())
        .expect("small node");
    let error = builder
        .type_application(
            function,
            vec![Type::Int; ash::types::TYPE_WORK_LIMIT],
            Type::Unit,
            origin,
        )
        .expect_err("cumulative argument admission must stop before storage");
    assert_eq!(error, BuildError::TypeWorkExceeded);
}

#[test]
fn core_construction_charges_forall_quantifiers_before_storage() {
    let file = source("bounded forall construction");
    let origin = whole_origin(&file);
    let parameters = (0..ash::types::TYPE_WORK_LIMIT)
        .map(|index| {
            (
                TypeVariableId::new(u32::try_from(index).expect("parameter identity")),
                Kind::Type,
            )
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let mut builder = CoreBuilder::new();

    let error = builder
        .unit(Type::Forall(parameters, Box::new(Type::Unit)), origin)
        .expect_err("quantifiers must consume Core's cumulative type budget");

    assert_eq!(error, BuildError::TypeWorkExceeded);
}

#[test]
fn core_construction_charges_type_abstraction_binders_before_storage() {
    let file = source("bounded type abstraction construction");
    let origin = whole_origin(&file);
    let parameters = (0..ash::types::TYPE_WORK_LIMIT)
        .map(|index| {
            (
                TypeVariableId::new(u32::try_from(index).expect("parameter identity")),
                Kind::Type,
            )
        })
        .collect::<Vec<_>>();
    let mut builder = CoreBuilder::new();
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("small abstraction body");

    let error = builder
        .type_abstraction(parameters, body, Type::Unit, origin)
        .expect_err("abstraction binders must consume Core's cumulative type budget");

    assert_eq!(error, BuildError::TypeWorkExceeded);
}

#[test]
fn expanded_malformed_type_application_maps_to_validation_resource() {
    // Simultaneous substitution expands the W-element argument at each of the
    // W occurrences in the result tuple. W=1,000 therefore requires at least
    // 1,000,000 retained Type cells, beyond Core validation's 983,040-unit
    // cumulative ledger, while the compact Core construction remains within
    // its unchanged TYPE_WORK_LIMIT ledger.
    const WIDTH: usize = 1_000;
    let file = source("expanded malformed type application");
    let origin = whole_origin(&file);
    let type_parameter = TypeVariableId::new(0);
    let element_type = Type::Variable(type_parameter);
    let tuple_type = Type::Tuple(vec![element_type.clone(); WIDTH].into_boxed_slice());
    let function_type =
        Type::Function(Box::new(element_type.clone()), Box::new(tuple_type.clone()));
    let mut builder = CoreBuilder::new();
    let parameter = builder
        .binder(element_type.clone(), origin.clone())
        .expect("parameter binder");
    let occurrence = builder
        .variable(parameter.id(), element_type, origin.clone())
        .expect("parameter occurrence");
    let tuple = builder
        .tuple(vec![occurrence; WIDTH], tuple_type, origin.clone())
        .expect("compact tuple body");
    let function = builder
        .function(parameter, tuple, function_type.clone(), origin.clone())
        .expect("polymorphic function body");
    let abstraction = builder
        .type_abstraction(
            vec![(type_parameter, Kind::Type)],
            function,
            Type::Forall(
                vec![(type_parameter, Kind::Type)].into_boxed_slice(),
                Box::new(function_type),
            ),
            origin.clone(),
        )
        .expect("unchecked type abstraction");
    let wide_argument = Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice());
    let root = builder
        .type_application(abstraction, vec![wide_argument], Type::Unit, origin)
        .expect("compact malformed type application");

    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("expanded substitution must stop at the validation budget");

    assert_eq!(error.reason(), ValidationReason::Resource);
}

#[test]
fn validates_registry_tuples_constructors_and_structured_matches() {
    let file = source("data core");
    let origin = whole_origin(&file);
    let nominal_origin = range_origin(&file, 0, 9);
    let constructor_origin = range_origin(&file, 5, 9);
    let nominal = NominalTypeId::new(file.id(), 0);
    let empty = ConstructorId::new(nominal, 0);
    let registry = Arc::new(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: nominal,
            spelling: "Choice".into(),
            constructors: vec![empty].into_boxed_slice(),
            origin: nominal_origin,
        }],
        vec![ResolvedConstructor {
            id: empty,
            owner: nominal,
            spelling: "Empty".into(),
            payload: None,
            origin: constructor_origin,
        }],
    ));
    let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
    let constructor = builder
        .constructor(empty, Type::Nominal(nominal), origin.clone())
        .expect("constructor node");
    let arm = CoreMatchArm::new(
        CorePattern::new(
            Type::Nominal(nominal),
            origin.clone(),
            CorePatternKind::Constructor {
                constructor: empty,
                payload: None,
            },
        ),
        constructor,
        origin.clone(),
    );
    let root = builder
        .match_expression(constructor, vec![arm], Type::Nominal(nominal), origin)
        .expect("match node");

    let program = validate(builder.finish(root).expect("root"), &[&file])
        .expect("well-formed data Core should validate");
    assert!(Arc::ptr_eq(program.registry(), &registry));
}

#[test]
fn rejects_malformed_data_registries_and_constructor_annotations() {
    let file = source("malformed data core");
    let origin = whole_origin(&file);
    let nominal = NominalTypeId::new(file.id(), 0);
    let empty_registry = Arc::new(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: nominal,
            spelling: "Empty".into(),
            constructors: Box::new([]),
            origin: origin.clone(),
        }],
        Vec::new(),
    ));
    let mut builder = CoreBuilder::with_registry(empty_registry);
    let root = builder.unit(Type::Unit, origin.clone()).expect("unit");
    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("empty nominal declaration");
    assert_eq!(error.reason(), ValidationReason::Registry);

    let constructor = ConstructorId::new(nominal, 0);
    let registry = Arc::new(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: nominal,
            spelling: "One".into(),
            constructors: vec![constructor].into_boxed_slice(),
            origin: origin.clone(),
        }],
        vec![ResolvedConstructor {
            id: constructor,
            owner: nominal,
            spelling: "One".into(),
            payload: None,
            origin: origin.clone(),
        }],
    ));
    let mut builder = CoreBuilder::with_registry(registry);
    let root = builder
        .constructor(constructor, Type::Int, origin)
        .expect("unchecked wrong annotation");
    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("constructor type disagreement");
    assert_eq!(error.reason(), ValidationReason::NodeType);
}

#[test]
fn rejects_constructor_payload_variables_outside_the_owner_parameters() {
    let file = source("parameterized registry payload");
    let origin = whole_origin(&file);
    let nominal = NominalTypeId::new(file.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let parameter = TypeVariableId::new(0);
    let foreign = TypeVariableId::new(1);
    let registry = Arc::new(
        ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                spelling: "Wrap".into(),
                constructors: vec![constructor].into_boxed_slice(),
                origin: origin.clone(),
            }],
            vec![ResolvedConstructor {
                id: constructor,
                owner: nominal,
                spelling: "Wrapped".into(),
                payload: Some(Type::Variable(foreign)),
                origin: range_origin(&file, 1, 2),
            }],
        )
        .with_type_parameters(vec![(
            nominal,
            vec![ResolvedTypeVariable {
                id: parameter,
                spelling: "A".into(),
                kind: ash::types::Kind::Type,
                origin: range_origin(&file, 2, 3),
            }],
        )]),
    );
    let mut builder = CoreBuilder::with_registry(registry);
    let root = builder.unit(Type::Unit, origin).expect("unit root");

    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("constructor payload variables must belong to their owner");

    assert_eq!(error.reason(), ValidationReason::Registry);
}

#[test]
fn rejects_higher_kinded_constructor_payload_as_a_value_type() {
    let file = source("HolderFMake");
    let origin = whole_origin(&file);
    let nominal = NominalTypeId::new(file.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let parameter = TypeVariableId::new(0);
    let registry = Arc::new(
        ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                spelling: "Holder".into(),
                constructors: Box::new([constructor]),
                origin: origin.clone(),
            }],
            vec![ResolvedConstructor {
                id: constructor,
                owner: nominal,
                spelling: "Make".into(),
                payload: Some(Type::Variable(parameter)),
                origin: range_origin(&file, 7, 11),
            }],
        )
        .with_type_parameters(vec![(
            nominal,
            vec![ResolvedTypeVariable {
                id: parameter,
                spelling: "F".into(),
                kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                origin: range_origin(&file, 6, 7),
            }],
        )]),
    );
    let mut builder = CoreBuilder::with_registry(registry);
    let root = builder.unit(Type::Unit, origin).expect("unit root");

    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("constructor payloads are ordinary value types of kind Type");

    assert_eq!(error.reason(), ValidationReason::Registry);
}

#[test]
fn rejects_polymorphic_constructor_payloads_in_the_registry() {
    let file = source("polymorphic registry payload");
    let origin = whole_origin(&file);
    let nominal = NominalTypeId::new(file.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let parameter = TypeVariableId::new(0);
    let registry = Arc::new(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: nominal,
            spelling: "Wrap".into(),
            constructors: vec![constructor].into_boxed_slice(),
            origin: origin.clone(),
        }],
        vec![ResolvedConstructor {
            id: constructor,
            owner: nominal,
            spelling: "Wrapped".into(),
            payload: Some(Type::Forall(
                vec![(parameter, Kind::Type)].into_boxed_slice(),
                Box::new(Type::Variable(parameter)),
            )),
            origin: range_origin(&file, 1, 2),
        }],
    ));
    let mut builder = CoreBuilder::with_registry(registry);
    let root = builder.unit(Type::Unit, origin).expect("unit root");

    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("constructor payloads must remain monomorphic");

    assert_eq!(error.reason(), ValidationReason::Registry);
}

#[test]
fn rejects_registry_type_parameter_identities_out_of_source_order() {
    let file = source("parameter order");
    let origin = whole_origin(&file);
    let nominal = NominalTypeId::new(file.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let registry = Arc::new(
        ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                spelling: "Pair".into(),
                constructors: vec![constructor].into_boxed_slice(),
                origin: origin.clone(),
            }],
            vec![ResolvedConstructor {
                id: constructor,
                owner: nominal,
                spelling: "PairValue".into(),
                payload: None,
                origin: range_origin(&file, 4, 5),
            }],
        )
        .with_type_parameters(vec![(
            nominal,
            vec![
                ResolvedTypeVariable {
                    id: TypeVariableId::new(1),
                    spelling: "A".into(),
                    kind: ash::types::Kind::Type,
                    origin: range_origin(&file, 1, 2),
                },
                ResolvedTypeVariable {
                    id: TypeVariableId::new(0),
                    spelling: "B".into(),
                    kind: ash::types::Kind::Type,
                    origin: range_origin(&file, 2, 3),
                },
            ],
        )]),
    );
    let mut builder = CoreBuilder::with_registry(registry);
    let root = builder.unit(Type::Unit, origin).expect("unit root");

    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("type-parameter identities must follow source order");

    assert_eq!(error.reason(), ValidationReason::Registry);
}

#[test]
fn rejects_nominal_parameters_reused_as_type_abstraction_binders() {
    let file = source("BoxAValue");
    let origin = whole_origin(&file);
    let nominal = NominalTypeId::new(file.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let parameter = TypeVariableId::new(0);
    let registry = Arc::new(
        ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                spelling: "Box".into(),
                constructors: vec![constructor].into_boxed_slice(),
                origin: origin.clone(),
            }],
            vec![ResolvedConstructor {
                id: constructor,
                owner: nominal,
                spelling: "Boxed".into(),
                payload: Some(Type::Variable(parameter)),
                origin: range_origin(&file, 4, 9),
            }],
        )
        .with_type_parameters(vec![(
            nominal,
            vec![ResolvedTypeVariable {
                id: parameter,
                spelling: "A".into(),
                kind: ash::types::Kind::Type,
                origin: range_origin(&file, 3, 4),
            }],
        )]),
    );
    let mut builder = CoreBuilder::with_registry(registry);
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("unit abstraction body");
    let root = builder
        .type_abstraction(
            vec![(parameter, Kind::Type)],
            body,
            Type::Forall(
                vec![(parameter, Kind::Type)].into_boxed_slice(),
                Box::new(Type::Unit),
            ),
            origin,
        )
        .expect("unchecked type abstraction");

    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("nominal parameters cannot define value-level type abstractions");

    assert_eq!(error.reason(), ValidationReason::TypeOperation);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn validates_ten_thousand_constructor_owner_links_without_pairwise_scanning() {
    const WIDTH: u32 = 10_000;
    let file = source(&"x".repeat(WIDTH as usize + 1));
    let nominal = NominalTypeId::new(file.id(), 0);
    let ids = (0..WIDTH)
        .map(|index| ConstructorId::new(nominal, index))
        .collect::<Vec<_>>();
    let constructors = ids
        .iter()
        .enumerate()
        .map(|(index, id)| ResolvedConstructor {
            id: *id,
            owner: nominal,
            spelling: format!("C{index}"),
            payload: None,
            origin: range_origin(
                &file,
                u32::try_from(index + 1).expect("test index should fit"),
                u32::try_from(index + 2).expect("test index should fit"),
            ),
        })
        .collect();
    let registry = Arc::new(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: nominal,
            spelling: "Wide".into(),
            constructors: ids.into_boxed_slice(),
            origin: whole_origin(&file),
        }],
        constructors,
    ));
    let mut builder = CoreBuilder::with_registry(registry);
    let root = builder
        .unit(Type::Unit, whole_origin(&file))
        .expect("unit root");

    validate(builder.finish(root).expect("root"), &[&file])
        .expect("wide registry should validate with indexed ownership checks");
}

#[test]
fn rejects_registry_identity_order_spelling_and_source_forgery() {
    let file = source("registry root");
    let foreign = source("foreign registry origin");
    let origin = whole_origin(&file);
    let foreign_origin = whole_origin(&foreign);
    let reject = |registry: ResolvedRegistry| {
        let mut builder = CoreBuilder::with_registry(Arc::new(registry));
        let root = builder.unit(Type::Unit, origin.clone()).expect("unit root");
        let error = validate(builder.finish(root).expect("root"), &[&file, &foreign])
            .expect_err("malformed registry must fail");
        assert_eq!(error.reason(), ValidationReason::Registry);
    };

    let skipped = NominalTypeId::new(file.id(), 7);
    let skipped_constructor = ConstructorId::new(skipped, 0);
    reject(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: skipped,
            spelling: "Skipped".into(),
            constructors: vec![skipped_constructor].into_boxed_slice(),
            origin: origin.clone(),
        }],
        vec![ResolvedConstructor {
            id: skipped_constructor,
            owner: skipped,
            spelling: "Make".into(),
            payload: None,
            origin: origin.clone(),
        }],
    ));

    let nominal = NominalTypeId::new(file.id(), 0);
    let first = ConstructorId::new(nominal, 0);
    let second = ConstructorId::new(nominal, 1);
    let nominal_entry = ResolvedNominalType {
        id: nominal,
        spelling: "Choice".into(),
        constructors: vec![first, second].into_boxed_slice(),
        origin: origin.clone(),
    };
    let constructor = |id, spelling: &str, constructor_origin: Origin| ResolvedConstructor {
        id,
        owner: nominal,
        spelling: spelling.into(),
        payload: None,
        origin: constructor_origin,
    };
    reject(ResolvedRegistry::new(
        vec![nominal_entry.clone()],
        vec![
            constructor(second, "Second", origin.clone()),
            constructor(first, "First", origin.clone()),
        ],
    ));
    reject(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            spelling: "lowercase".into(),
            ..nominal_entry.clone()
        }],
        vec![
            constructor(first, "First", origin.clone()),
            constructor(second, "Second", origin.clone()),
        ],
    ));
    reject(ResolvedRegistry::new(
        vec![nominal_entry],
        vec![
            constructor(first, "First", foreign_origin),
            constructor(second, "Second", origin.clone()),
        ],
    ));

    let first_nominal = NominalTypeId::new(file.id(), 0);
    let second_nominal = NominalTypeId::new(file.id(), 1);
    let first_constructor = ConstructorId::new(first_nominal, 0);
    let second_constructor = ConstructorId::new(second_nominal, 0);
    reject(ResolvedRegistry::new(
        vec![
            ResolvedNominalType {
                id: first_nominal,
                spelling: "FirstType".into(),
                constructors: vec![first_constructor].into_boxed_slice(),
                origin: range_origin(&file, 6, 7),
            },
            ResolvedNominalType {
                id: second_nominal,
                spelling: "SecondType".into(),
                constructors: vec![second_constructor].into_boxed_slice(),
                origin: range_origin(&file, 0, 1),
            },
        ],
        vec![
            ResolvedConstructor {
                id: first_constructor,
                owner: first_nominal,
                spelling: "FirstMake".into(),
                payload: None,
                origin: range_origin(&file, 7, 8),
            },
            ResolvedConstructor {
                id: second_constructor,
                owner: second_nominal,
                spelling: "SecondMake".into(),
                payload: None,
                origin: range_origin(&file, 1, 2),
            },
        ],
    ));
}

#[test]
fn rejects_and_destroys_overdeep_registry_payloads_on_a_small_stack() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, || {
                let file = source("registry payload bounds");
                let nominal = NominalTypeId::new(file.id(), 0);
                let constructor = ConstructorId::new(nominal, 0);
                let nominal_origin = whole_origin(&file);
                let constructor_origin = range_origin(&file, 9, 16);

                let mut deep_type = Type::Int;
                for _ in 0..50_000 {
                    deep_type = Type::Function(Box::new(Type::Int), Box::new(deep_type));
                }
                let registry = Arc::new(ResolvedRegistry::new(
                    vec![ResolvedNominalType {
                        id: nominal,
                        spelling: "Bounded".into(),
                        constructors: vec![constructor].into_boxed_slice(),
                        origin: nominal_origin.clone(),
                    }],
                    vec![ResolvedConstructor {
                        id: constructor,
                        owner: nominal,
                        spelling: "Make".into(),
                        payload: Some(deep_type),
                        origin: constructor_origin.clone(),
                    }],
                ));
                let mut builder = CoreBuilder::with_registry(registry);
                let root = builder
                    .unit(Type::Unit, whole_origin(&file))
                    .expect("unit root");
                let error = validate(builder.finish(root).expect("root"), &[&file])
                    .expect_err("overdeep registry type");
                assert_eq!(error.reason(), ValidationReason::Registry);

                let mut deep_origin = nominal_origin;
                for _ in 0..50_000 {
                    deep_origin = Origin::Generated {
                        cause: Box::new(deep_origin),
                        reason: GeneratedReason::TypeChecking,
                    };
                }
                let registry = Arc::new(ResolvedRegistry::new(
                    vec![ResolvedNominalType {
                        id: nominal,
                        spelling: "Bounded".into(),
                        constructors: vec![constructor].into_boxed_slice(),
                        origin: deep_origin,
                    }],
                    vec![ResolvedConstructor {
                        id: constructor,
                        owner: nominal,
                        spelling: "Make".into(),
                        payload: None,
                        origin: constructor_origin,
                    }],
                ));
                let mut builder = CoreBuilder::with_registry(registry);
                let root = builder
                    .unit(Type::Unit, whole_origin(&file))
                    .expect("unit root");
                let error = validate(builder.finish(root).expect("root"), &[&file])
                    .expect_err("overdeep registry origin");
                assert_eq!(error.reason(), ValidationReason::Registry);
            })
            .expect("small-stack thread should start")
            .join()
            .expect("registry rejection and destruction must fit the small stack");
    });
}

#[test]
fn rejects_and_destroys_overdeep_registry_parameter_origins_on_a_small_stack() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, move || {
                let file = source("parameter origin bounds");
                let nominal = NominalTypeId::new(file.id(), 0);
                let constructor = ConstructorId::new(nominal, 0);
                let parameter = TypeVariableId::new(0);
                let origin = whole_origin(&file);
                let mut deep_parameter_origin = range_origin(&file, 0, 1);
                for _ in 0..5_000 {
                    deep_parameter_origin = Origin::Generated {
                        cause: Box::new(deep_parameter_origin),
                        reason: GeneratedReason::TypeChecking,
                    };
                }
                let registry = Arc::new(
                    ResolvedRegistry::new(
                        vec![ResolvedNominalType {
                            id: nominal,
                            spelling: "Bounded".into(),
                            constructors: vec![constructor].into_boxed_slice(),
                            origin: origin.clone(),
                        }],
                        vec![ResolvedConstructor {
                            id: constructor,
                            owner: nominal,
                            spelling: "Make".into(),
                            payload: Some(Type::Variable(parameter)),
                            origin: range_origin(&file, 1, 2),
                        }],
                    )
                    .with_type_parameters(vec![(
                        nominal,
                        vec![ResolvedTypeVariable {
                            id: parameter,
                            spelling: "A".into(),
                            kind: ash::types::Kind::Type,
                            origin: deep_parameter_origin,
                        }],
                    )]),
                );
                let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
                let root = builder.unit(Type::Unit, origin).expect("unit root");
                let error = validate(builder.finish(root).expect("root"), &[&file])
                    .expect_err("overdeep parameter origin");
                assert_eq!(error.reason(), ValidationReason::Registry);
                drop(registry);
            })
            .expect("small-stack thread should start")
            .join()
            .expect("parameter-origin rejection and destruction must fit the small stack");
    });
}

#[test]
fn rejects_and_destroys_replaced_registry_parameter_ids_on_a_small_stack() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, move || {
                let file = source("replaced parameter identity");
                let nominal = NominalTypeId::new(file.id(), 0);
                let constructor = ConstructorId::new(nominal, 0);
                let parameter = TypeVariableId::new(0);
                let origin = whole_origin(&file);
                let registry = Arc::new(
                    ResolvedRegistry::new(
                        vec![ResolvedNominalType {
                            id: nominal,
                            spelling: "Bounded".into(),
                            constructors: vec![constructor].into_boxed_slice(),
                            origin: origin.clone(),
                        }],
                        vec![ResolvedConstructor {
                            id: constructor,
                            owner: nominal,
                            spelling: "Make".into(),
                            payload: Some(Type::Variable(parameter)),
                            origin: range_origin(&file, 1, 2),
                        }],
                    )
                    .with_type_parameters(vec![(
                        nominal,
                        vec![
                            ResolvedTypeVariable {
                                id: parameter,
                                spelling: "A".into(),
                                kind: ash::types::Kind::Type,
                                origin: mixed_origin(&file, 5_000),
                            },
                            ResolvedTypeVariable {
                                id: parameter,
                                spelling: "B".into(),
                                kind: ash::types::Kind::Type,
                                origin: range_origin(&file, 2, 3),
                            },
                        ],
                    )]),
                );
                assert_eq!(
                    registry
                        .type_variable(parameter)
                        .map(|parameter| parameter.spelling.as_str()),
                    Some("B")
                );
                let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
                let root = builder.unit(Type::Unit, origin).expect("unit root");
                let error = validate(builder.finish(root).expect("root"), &[&file])
                    .expect_err("duplicate parameter identities must be rejected");
                assert_eq!(error.reason(), ValidationReason::Registry);
                drop(registry);
            })
            .expect("small-stack thread should start")
            .join()
            .expect("replaced parameter teardown must fit the small stack");
    });
}

#[test]
fn rejects_and_destroys_replaced_registry_parameter_owners_on_a_small_stack() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, move || {
                let file = source("replaced parameter owner");
                let nominal = NominalTypeId::new(file.id(), 0);
                let constructor = ConstructorId::new(nominal, 0);
                let first_parameter = TypeVariableId::new(0);
                let second_parameter = TypeVariableId::new(1);
                let origin = whole_origin(&file);
                let registry = Arc::new(
                    ResolvedRegistry::new(
                        vec![ResolvedNominalType {
                            id: nominal,
                            spelling: "Bounded".into(),
                            constructors: vec![constructor].into_boxed_slice(),
                            origin: origin.clone(),
                        }],
                        vec![ResolvedConstructor {
                            id: constructor,
                            owner: nominal,
                            spelling: "Make".into(),
                            payload: Some(Type::Variable(first_parameter)),
                            origin: range_origin(&file, 1, 2),
                        }],
                    )
                    .with_type_parameters(vec![(
                        nominal,
                        vec![ResolvedTypeVariable {
                            id: first_parameter,
                            spelling: "A".into(),
                            kind: ash::types::Kind::Type,
                            origin: mixed_origin(&file, 5_000),
                        }],
                    )])
                    .with_type_parameters(vec![(
                        nominal,
                        vec![ResolvedTypeVariable {
                            id: second_parameter,
                            spelling: "B".into(),
                            kind: ash::types::Kind::Type,
                            origin: range_origin(&file, 2, 3),
                        }],
                    )]),
                );
                assert_eq!(
                    registry
                        .nominal_parameters(nominal)
                        .and_then(|parameters| parameters.first())
                        .map(|parameter| parameter.spelling.as_str()),
                    Some("B")
                );
                let mut builder = CoreBuilder::with_registry(Arc::clone(&registry));
                let root = builder.unit(Type::Unit, origin).expect("unit root");
                let error = validate(builder.finish(root).expect("root"), &[&file])
                    .expect_err("duplicate parameter owners must be rejected");
                assert_eq!(error.reason(), ValidationReason::Registry);
                drop(registry);
            })
            .expect("small-stack thread should start")
            .join()
            .expect("replaced owner teardown must fit the small stack");
    });
}

#[test]
fn rejects_missing_and_redundant_structured_match_arms() {
    let file = source("coverage core");
    let origin = whole_origin(&file);
    let mut missing = CoreBuilder::new();
    let scrutinee = missing
        .boolean(true, Type::Bool, origin.clone())
        .expect("scrutinee");
    let body = missing
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("body");
    let arm = CoreMatchArm::new(
        CorePattern::new(Type::Bool, origin.clone(), CorePatternKind::Boolean(true)),
        body,
        origin.clone(),
    );
    let root = missing
        .match_expression(scrutinee, vec![arm], Type::Int, origin.clone())
        .expect("unchecked match");
    let error =
        validate(missing.finish(root).expect("root"), &[&file]).expect_err("missing false witness");
    assert_eq!(error.reason(), ValidationReason::Coverage);

    let mut redundant = CoreBuilder::new();
    let scrutinee = redundant
        .boolean(true, Type::Bool, origin.clone())
        .expect("scrutinee");
    let first = redundant
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("first body");
    let second = redundant
        .integer(integer("2"), Type::Int, origin.clone())
        .expect("second body");
    let wildcard = || CorePattern::new(Type::Bool, origin.clone(), CorePatternKind::Wildcard);
    let root = redundant
        .match_expression(
            scrutinee,
            vec![
                CoreMatchArm::new(wildcard(), first, origin.clone()),
                CoreMatchArm::new(wildcard(), second, origin.clone()),
            ],
            Type::Int,
            origin,
        )
        .expect("unchecked redundant match");
    let error =
        validate(redundant.finish(root).expect("root"), &[&file]).expect_err("redundant wildcard");
    assert_eq!(error.reason(), ValidationReason::Coverage);
}

#[test]
fn oversized_unchecked_match_maps_coverage_exhaustion_to_resource() {
    const WIDTH: u32 = 800;
    let file = source(&"x".repeat(WIDTH as usize + 1));
    let origin = whole_origin(&file);
    let nominal = NominalTypeId::new(file.id(), 0);
    let constructors = (0..WIDTH)
        .map(|index| ConstructorId::new(nominal, index))
        .collect::<Vec<_>>();
    let constructor_entries = constructors
        .iter()
        .enumerate()
        .map(|(index, id)| ResolvedConstructor {
            id: *id,
            owner: nominal,
            spelling: format!("C{index}"),
            payload: None,
            origin: range_origin(
                &file,
                u32::try_from(index + 1).expect("test index should fit"),
                u32::try_from(index + 2).expect("test index should fit"),
            ),
        })
        .collect();
    let registry = Arc::new(ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: nominal,
            spelling: "TooWide".into(),
            constructors: constructors.clone().into_boxed_slice(),
            origin: origin.clone(),
        }],
        constructor_entries,
    ));
    let mut builder = CoreBuilder::with_registry(registry);
    let scrutinee = builder
        .constructor(constructors[0], Type::Nominal(nominal), origin.clone())
        .expect("constructor scrutinee");
    let body = builder
        .unit(Type::Unit, origin.clone())
        .expect("shared arm body");
    let arms = constructors
        .into_iter()
        .map(|constructor| {
            CoreMatchArm::new(
                CorePattern::new(
                    Type::Nominal(nominal),
                    origin.clone(),
                    CorePatternKind::Constructor {
                        constructor,
                        payload: None,
                    },
                ),
                body,
                origin.clone(),
            )
        })
        .collect();
    let root = builder
        .match_expression(scrutinee, arms, Type::Unit, origin)
        .expect("unchecked oversized match");

    let error = validate(builder.finish(root).expect("root"), &[&file])
        .expect_err("coverage budget exhaustion must reject unchecked Core");
    assert_eq!(error.reason(), ValidationReason::Resource);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn nominal_identity_and_tuple_structure_share_one_type_equality_rule() {
    let first_source = source("first nominal source");
    let second_source = source("second nominal source");
    let first = NominalTypeId::new(first_source.id(), 0);
    let same = NominalTypeId::new(first_source.id(), 0);
    let other_declaration = NominalTypeId::new(first_source.id(), 1);
    let other_source = NominalTypeId::new(second_source.id(), 0);

    assert!(same_type(&Type::Nominal(first), &Type::Nominal(same)));
    assert!(!same_type(
        &Type::Nominal(first),
        &Type::Nominal(other_declaration)
    ));
    assert!(!same_type(
        &Type::Nominal(first),
        &Type::Nominal(other_source)
    ));

    let left = Type::Tuple(vec![Type::Int, Type::Nominal(first)].into_boxed_slice());
    let right = Type::Tuple(vec![Type::Int, Type::Nominal(same)].into_boxed_slice());
    assert!(same_type(&left, &right));
    assert_eq!(left.to_string(), format!("(Int, {})", Type::Nominal(first)));
}

#[test]
fn structural_types_render_with_unambiguous_function_association() {
    assert_eq!(Type::Int.to_string(), "Int");
    assert_eq!(Type::Bool.to_string(), "Bool");
    assert_eq!(Type::Unit.to_string(), "Unit");

    let curried = Type::Function(
        Box::new(Type::Int),
        Box::new(Type::Function(Box::new(Type::Bool), Box::new(Type::Unit))),
    );
    assert_eq!(curried.to_string(), "Int -> Bool -> Unit");

    let higher_order = Type::Function(
        Box::new(Type::Function(Box::new(Type::Int), Box::new(Type::Bool))),
        Box::new(Type::Unit),
    );
    assert_eq!(higher_order.to_string(), "(Int -> Bool) -> Unit");
}

fn source(text: &str) -> SourceFile {
    SourceFile::new("test.ash", text).expect("test source should be representable")
}

fn whole_origin(source: &SourceFile) -> Origin {
    let end = u32::try_from(source.text().len()).expect("test source should fit u32");
    let range = ByteRange::new(0, end).expect("ordered test range");
    Origin::Source(
        source
            .span(range)
            .expect("test range should belong to source"),
    )
}

fn range_origin(source: &SourceFile, start: u32, end: u32) -> Origin {
    Origin::Source(
        source
            .span(ByteRange::new(start, end).expect("ordered test range"))
            .expect("test range should belong to source"),
    )
}

fn integer(text: &str) -> Integer {
    Integer::parse_decimal(text).expect("test integer should be valid")
}

fn function_type(depth: usize) -> Type {
    let mut ty = Type::Unit;
    for _ in 0..depth {
        ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
    }
    ty
}

fn generated_origin(source: &SourceFile, depth: usize) -> Origin {
    let mut origin = whole_origin(source);
    for _ in 0..depth {
        origin = Origin::Generated {
            cause: Box::new(origin),
            reason: GeneratedReason::TypeChecking,
        };
    }
    origin
}

fn mixed_origin(source: &SourceFile, depth: usize) -> Origin {
    let span = source
        .span(ByteRange::new(0, 1).expect("ordered origin range"))
        .expect("origin range should belong to source");
    let mut origin = Origin::Source(span);
    for index in 0..depth {
        origin = if index % 2 == 0 {
            Origin::Generated {
                cause: Box::new(origin),
                reason: GeneratedReason::TypeChecking,
            }
        } else {
            Origin::Related {
                primary: Box::new(origin),
                related: vec![span],
            }
        };
    }
    origin
}

#[test]
fn validates_a_recursive_function_binding_group() {
    let file = source("recursive core");
    let origin = whole_origin(&file);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
    let mut builder = CoreBuilder::new();
    let recursive = builder
        .binder(function_type.clone(), origin.clone())
        .expect("recursive binder");
    let parameter = builder
        .binder(Type::Unit, origin.clone())
        .expect("function parameter");
    let forty_two = builder
        .integer(integer("42"), Type::Int, origin.clone())
        .expect("function body");
    let function = builder
        .function(parameter, forty_two, function_type.clone(), origin.clone())
        .expect("function initializer");
    let occurrence = builder
        .variable(recursive.id(), function_type, origin.clone())
        .expect("recursive occurrence");
    let argument = builder
        .unit(Type::Unit, origin.clone())
        .expect("unit argument");
    let application = builder
        .application(occurrence, argument, Type::Int, origin.clone())
        .expect("recursive call");
    let root = builder
        .recursive_binding(vec![(recursive, function)], application, Type::Int, origin)
        .expect("recursive group");

    let validated = validate(builder.finish(root).expect("root"), &[&file])
        .expect("well-formed recursive Core should validate");

    assert_eq!(validated.root(), root);
    assert_eq!(validated.node(root).expect("group root").ty, Type::Int);
}

#[test]
fn validates_a_deep_guarded_initializer_on_a_small_stack() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, || {
                let file = source("deep guarded core");
                let origin = whole_origin(&file);
                let nominal_origin = range_origin(&file, 0, 17);
                let constructor_origin = range_origin(&file, 6, 13);
                let nominal = NominalTypeId::new(file.id(), 0);
                let step = ConstructorId::new(nominal, 0);
                let registry = Arc::new(ResolvedRegistry::new(
                    vec![ResolvedNominalType {
                        id: nominal,
                        spelling: "Chain".into(),
                        constructors: vec![step].into_boxed_slice(),
                        origin: nominal_origin,
                    }],
                    vec![ResolvedConstructor {
                        id: step,
                        owner: nominal,
                        spelling: "Step".into(),
                        payload: Some(Type::Nominal(nominal)),
                        origin: constructor_origin,
                    }],
                ));
                let chain = Type::Nominal(nominal);
                let constructor_type =
                    Type::Function(Box::new(chain.clone()), Box::new(chain.clone()));
                let mut builder = CoreBuilder::with_registry(registry);
                let member = builder
                    .binder(chain.clone(), origin.clone())
                    .expect("recursive binder");
                let occurrence = builder
                    .variable(member.id(), chain.clone(), origin.clone())
                    .expect("recursive occurrence");
                let constructor = builder
                    .constructor(step, constructor_type, origin.clone())
                    .expect("constructor function");
                let mut initializer = occurrence;
                for _ in 0..10_000 {
                    initializer = builder
                        .application(constructor, initializer, chain.clone(), origin.clone())
                        .expect("guarded constructor application");
                }
                let root = builder
                    .recursive_binding(vec![(member, initializer)], occurrence, chain, origin)
                    .expect("recursive group");
                validate(builder.finish(root).expect("root"), &[&file])
                    .expect("deep guarded Core must validate");
            })
            .expect("small-stack thread should start")
            .join()
            .expect("guarded validation must fit the small stack");
    });
}

#[test]
fn rejects_empty_and_non_function_recursive_groups() {
    let empty_file = source("empty recursive core");
    let empty_origin = whole_origin(&empty_file);
    let mut empty_builder = CoreBuilder::new();
    let empty_body = empty_builder
        .integer(integer("1"), Type::Int, empty_origin.clone())
        .expect("empty body");
    let empty_root = empty_builder
        .recursive_binding(Vec::new(), empty_body, Type::Int, empty_origin)
        .expect("unchecked empty group");
    let empty_error = validate(
        empty_builder.finish(empty_root).expect("empty root"),
        &[&empty_file],
    )
    .expect_err("an empty recursive group is malformed");
    assert_eq!(empty_error.reason(), ValidationReason::RecursiveBinding);

    let value_file = source("value recursive core");
    let value_origin = whole_origin(&value_file);
    let mut value_builder = CoreBuilder::new();
    let binder = value_builder
        .binder(Type::Int, value_origin.clone())
        .expect("value binder");
    let initializer = value_builder
        .integer(integer("1"), Type::Int, value_origin.clone())
        .expect("value initializer");
    let body = value_builder
        .integer(integer("2"), Type::Int, value_origin.clone())
        .expect("value body");
    let root = value_builder
        .recursive_binding(vec![(binder, initializer)], body, Type::Int, value_origin)
        .expect("unchecked value group");
    let value_error = validate(
        value_builder.finish(root).expect("value root"),
        &[&value_file],
    )
    .expect_err("a recursive initializer must be a function node");
    assert_eq!(value_error.reason(), ValidationReason::RecursiveBinding);
}

#[test]
fn rejects_recursive_member_type_disagreement_and_duplicate_binders() {
    let mismatch_file = source("mismatched recursive core");
    let mismatch_origin = whole_origin(&mismatch_file);
    let declared_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
    let actual_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
    let mut mismatch_builder = CoreBuilder::new();
    let member = mismatch_builder
        .binder(declared_type, mismatch_origin.clone())
        .expect("member binder");
    let parameter = mismatch_builder
        .binder(Type::Unit, mismatch_origin.clone())
        .expect("member parameter");
    let unit = mismatch_builder
        .unit(Type::Unit, mismatch_origin.clone())
        .expect("unit body");
    let function = mismatch_builder
        .function(parameter, unit, actual_type, mismatch_origin.clone())
        .expect("mismatched function");
    let result = mismatch_builder
        .integer(integer("1"), Type::Int, mismatch_origin.clone())
        .expect("group result");
    let mismatch_root = mismatch_builder
        .recursive_binding(vec![(member, function)], result, Type::Int, mismatch_origin)
        .expect("unchecked mismatch group");
    let mismatch_error = validate(
        mismatch_builder
            .finish(mismatch_root)
            .expect("mismatch root"),
        &[&mismatch_file],
    )
    .expect_err("the member type must agree with its function initializer");
    assert_eq!(mismatch_error.reason(), ValidationReason::NodeType);

    let duplicate_file = source("duplicate recursive core");
    let duplicate_origin = whole_origin(&duplicate_file);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
    let mut duplicate_builder = CoreBuilder::new();
    let member = duplicate_builder
        .binder(function_type.clone(), duplicate_origin.clone())
        .expect("member binder");
    let parameter = duplicate_builder
        .binder(Type::Unit, duplicate_origin.clone())
        .expect("member parameter");
    let result = duplicate_builder
        .integer(integer("1"), Type::Int, duplicate_origin.clone())
        .expect("member body");
    let function = duplicate_builder
        .function(parameter, result, function_type, duplicate_origin.clone())
        .expect("member function");
    let duplicate_root = duplicate_builder
        .recursive_binding(
            vec![(member.clone(), function), (member, function)],
            result,
            Type::Int,
            duplicate_origin,
        )
        .expect("unchecked duplicate group");
    let duplicate_error = validate(
        duplicate_builder
            .finish(duplicate_root)
            .expect("duplicate root"),
        &[&duplicate_file],
    )
    .expect_err("one binder cannot have two recursive definition sites");
    assert_eq!(duplicate_error.reason(), ValidationReason::Scope);
}

#[test]
fn recursive_group_rejects_foreign_children_and_binder_capabilities() {
    let file = source("foreign recursive core");
    let origin = whole_origin(&file);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));

    let mut foreign_builder = CoreBuilder::new();
    let foreign_parameter = foreign_builder
        .binder(Type::Unit, origin.clone())
        .expect("foreign parameter");
    let foreign_body = foreign_builder
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("foreign body");
    let foreign_function = foreign_builder
        .function(
            foreign_parameter,
            foreign_body,
            function_type.clone(),
            origin.clone(),
        )
        .expect("foreign function");
    let foreign_binder = foreign_builder
        .binder(function_type.clone(), origin.clone())
        .expect("foreign recursive binder");

    let mut receiver = CoreBuilder::new();
    let local_binder = receiver
        .binder(function_type, origin.clone())
        .expect("local recursive binder");
    let body = receiver
        .integer(integer("2"), Type::Int, origin.clone())
        .expect("local body");
    assert_eq!(
        receiver.recursive_binding(
            vec![(foreign_binder, foreign_function)],
            body,
            Type::Int,
            origin.clone(),
        ),
        Err(BuildError::ForeignBinder)
    );

    let root = receiver
        .recursive_binding(
            vec![(local_binder, foreign_function)],
            body,
            Type::Int,
            origin,
        )
        .expect("unchecked construction accepts child handles");
    let error = validate(receiver.finish(root).expect("local root"), &[&file])
        .expect_err("recursive initializer must belong to the group arena");
    assert_eq!(error.reason(), ValidationReason::NodeBounds);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn recursive_group_rejects_foreign_group_and_binder_provenance() {
    let admitted = source("admitted recursive core");
    let foreign = source("foreign recursive core");
    let admitted_origin = whole_origin(&admitted);
    let foreign_origin = whole_origin(&foreign);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));

    let mut foreign_group_builder = CoreBuilder::new();
    let member = foreign_group_builder
        .binder(function_type.clone(), admitted_origin.clone())
        .expect("member binder");
    let parameter = foreign_group_builder
        .binder(Type::Unit, admitted_origin.clone())
        .expect("parameter binder");
    let body = foreign_group_builder
        .integer(integer("1"), Type::Int, admitted_origin.clone())
        .expect("function body");
    let function = foreign_group_builder
        .function(
            parameter,
            body,
            function_type.clone(),
            admitted_origin.clone(),
        )
        .expect("function initializer");
    let root = foreign_group_builder
        .recursive_binding(
            vec![(member, function)],
            body,
            Type::Int,
            foreign_origin.clone(),
        )
        .expect("unchecked group");
    let error = validate(
        foreign_group_builder.finish(root).expect("group root"),
        &[&admitted],
    )
    .expect_err("a recursive group origin must be admitted");
    assert_eq!(error.reason(), ValidationReason::Provenance);
    assert_eq!(error.node(), Some(root));

    let mut foreign_binder_builder = CoreBuilder::new();
    let member = foreign_binder_builder
        .binder(function_type.clone(), foreign_origin)
        .expect("unchecked foreign-origin binder");
    let parameter = foreign_binder_builder
        .binder(Type::Unit, admitted_origin.clone())
        .expect("parameter binder");
    let body = foreign_binder_builder
        .integer(integer("1"), Type::Int, admitted_origin.clone())
        .expect("function body");
    let function = foreign_binder_builder
        .function(parameter, body, function_type, admitted_origin.clone())
        .expect("function initializer");
    let root = foreign_binder_builder
        .recursive_binding(vec![(member, function)], body, Type::Int, admitted_origin)
        .expect("unchecked group");
    let error = validate(
        foreign_binder_builder.finish(root).expect("group root"),
        &[&admitted],
    )
    .expect_err("a recursive member binder origin must be admitted");
    assert_eq!(error.reason(), ValidationReason::Provenance);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn recursive_group_rejects_a_free_occurrence_and_an_unreachable_child() {
    let scope_file = source("recursive free occurrence");
    let scope_origin = whole_origin(&scope_file);
    let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
    let mut scope_builder = CoreBuilder::new();
    let member = scope_builder
        .binder(function_type.clone(), scope_origin.clone())
        .expect("member binder");
    let parameter = scope_builder
        .binder(Type::Unit, scope_origin.clone())
        .expect("parameter binder");
    let unbound = scope_builder
        .binder(Type::Int, scope_origin.clone())
        .expect("unbound binder capability");
    let free_occurrence = scope_builder
        .variable(unbound.id(), Type::Int, scope_origin.clone())
        .expect("free occurrence");
    let function = scope_builder
        .function(
            parameter,
            free_occurrence,
            function_type.clone(),
            scope_origin.clone(),
        )
        .expect("function initializer");
    let result = scope_builder
        .integer(integer("1"), Type::Int, scope_origin.clone())
        .expect("group result");
    let root = scope_builder
        .recursive_binding(vec![(member, function)], result, Type::Int, scope_origin)
        .expect("unchecked group");
    let error = validate(
        scope_builder.finish(root).expect("group root"),
        &[&scope_file],
    )
    .expect_err("a recursive function cannot acquire an unbound occurrence");
    assert_eq!(error.reason(), ValidationReason::Scope);
    assert_eq!(error.node(), Some(free_occurrence));

    let unreachable_file = source("recursive unreachable child");
    let unreachable_origin = whole_origin(&unreachable_file);
    let mut unreachable_builder = CoreBuilder::new();
    let orphan = unreachable_builder
        .integer(integer("0"), Type::Int, unreachable_origin.clone())
        .expect("orphan node");
    let member = unreachable_builder
        .binder(function_type.clone(), unreachable_origin.clone())
        .expect("member binder");
    let parameter = unreachable_builder
        .binder(Type::Unit, unreachable_origin.clone())
        .expect("parameter binder");
    let body = unreachable_builder
        .integer(integer("1"), Type::Int, unreachable_origin.clone())
        .expect("function body");
    let function = unreachable_builder
        .function(parameter, body, function_type, unreachable_origin.clone())
        .expect("function initializer");
    let root = unreachable_builder
        .recursive_binding(
            vec![(member, function)],
            body,
            Type::Int,
            unreachable_origin,
        )
        .expect("unchecked group");
    let error = validate(
        unreachable_builder.finish(root).expect("group root"),
        &[&unreachable_file],
    )
    .expect_err("all recursive arena nodes must be reachable from the group");
    assert_eq!(error.reason(), ValidationReason::Unreachable);
    assert_eq!(error.node(), Some(orphan));
}

#[test]
fn rejects_cross_builder_binders_without_consuming_receiver_state() {
    let file = source("()");
    let origin = whole_origin(&file);
    let mut owner = CoreBuilder::new();
    let foreign = owner
        .binder(Type::Unit, origin.clone())
        .expect("owner binder");

    let mut function_receiver = CoreBuilder::new();
    let body = function_receiver
        .unit(Type::Unit, origin.clone())
        .expect("receiver body");
    assert_eq!(
        function_receiver.function(
            foreign.clone(),
            body,
            Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
            origin.clone(),
        ),
        Err(BuildError::ForeignBinder)
    );
    let first_generated = function_receiver
        .binder(Type::Unit, origin.clone())
        .expect("rejection does not consume a binder identity");
    assert_eq!(first_generated.id().local(), 0);
    let program = validate(
        function_receiver
            .finish(body)
            .expect("only the original body node remains"),
        &[&file],
    )
    .expect("the receiver remains valid");
    assert_eq!(program.node_count(), 1);

    let mut binding_receiver = CoreBuilder::new();
    let unit = binding_receiver
        .unit(Type::Unit, origin.clone())
        .expect("receiver unit");
    assert_eq!(
        binding_receiver.binding(foreign, unit, unit, Type::Unit, origin.clone()),
        Err(BuildError::ForeignBinder)
    );
    let first_generated = binding_receiver
        .binder(Type::Unit, origin)
        .expect("binding rejection does not consume a binder identity");
    assert_eq!(first_generated.id().local(), 0);
    let program = validate(
        binding_receiver
            .finish(unit)
            .expect("only the original unit node remains"),
        &[&file],
    )
    .expect("the binding receiver remains valid");
    assert_eq!(program.node_count(), 1);
}

#[test]
fn foreign_binder_rejection_admits_payloads_before_checking_capability() {
    std::thread::Builder::new()
        .name("foreign-binder-payload-order".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let file = source("()");
            let origin = whole_origin(&file);
            let mut owner = CoreBuilder::new();
            let foreign = owner
                .binder(Type::Unit, origin.clone())
                .expect("owner binder");
            let mut receiver = CoreBuilder::new();
            let body = receiver
                .unit(Type::Unit, origin.clone())
                .expect("receiver body");

            assert_eq!(
                receiver.function(
                    foreign.clone(),
                    body,
                    function_type(50_000),
                    generated_origin(&file, 50_000),
                ),
                Err(BuildError::TypeDepthExceeded)
            );
            assert_eq!(
                receiver.function(
                    foreign,
                    body,
                    function_type(CORE_PAYLOAD_DEPTH_LIMIT),
                    generated_origin(&file, CORE_PAYLOAD_DEPTH_LIMIT),
                ),
                Err(BuildError::ForeignBinder)
            );
            let first_generated = receiver
                .binder(Type::Unit, origin)
                .expect("rejections leave binder allocation untouched");
            assert_eq!(first_generated.id().local(), 0);
            let program = validate(receiver.finish(body).expect("receiver root"), &[&file])
                .expect("receiver remains valid");
            assert_eq!(program.node_count(), 1);
        })
        .expect("test thread should start")
        .join()
        .expect("foreign payload rejection should remain stack safe");
}

#[test]
fn foreign_binder_rejection_dismantles_wide_binder_metadata_on_a_small_stack() {
    const WIDTH: usize = 32_768;

    std::thread::Builder::new()
        .name("foreign-wide-binder-disposal".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let file = source("()");
            let origin = whole_origin(&file);
            let mut ty = Type::Unit;
            for _ in 0..WIDTH {
                ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
            }
            let mut owner = CoreBuilder::new();
            let foreign = owner.binder(ty, origin.clone()).expect("owner binder");

            let mut receiver = CoreBuilder::new();
            let body = receiver
                .unit(Type::Unit, origin.clone())
                .expect("receiver body");
            assert_eq!(
                receiver.function(foreign, body, Type::Unit, origin),
                Err(BuildError::ForeignBinder),
            );
        })
        .expect("test thread should start")
        .join()
        .expect("foreign binder teardown should fit the small stack");
}

#[test]
fn validates_all_pure_value_and_computation_families() {
    let file = source("core");
    let origin = whole_origin(&file);

    let mut builder = CoreBuilder::new();
    let one = builder
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("small arena");
    let two = builder
        .integer(integer("2"), Type::Int, origin.clone())
        .expect("small arena");
    let sum = builder
        .primitive(Primitive::Add, one, two, Type::Int, origin.clone())
        .expect("small arena");
    let binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let variable = builder
        .variable(binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let function = builder
        .function(
            binder.clone(),
            variable,
            Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
            origin.clone(),
        )
        .expect("small arena");
    let application = builder
        .application(function, sum, Type::Int, origin.clone())
        .expect("small arena");
    let result_binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let result_variable = builder
        .variable(result_binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let root = builder
        .binding(
            result_binder,
            application,
            result_variable,
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");

    let validated = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect("well-typed Core should validate");

    assert_eq!(validated.root(), root);
    assert_eq!(validated.node(root).expect("validated root").ty, Type::Int);
    assert!(matches!(
        validated.node(root).expect("validated root").kind,
        PureExprKind::Computation(PureComputation::Bind(_))
    ));
    assert_eq!(validated.node_count(), 8);
    let function_node = validated.node(function).expect("validated function");
    let PureExprKind::Value(PureValue::Function(function_node)) = &function_node.kind else {
        panic!("expected function payload");
    };
    assert_eq!(function_node.parameter().ty(), &Type::Int);
    assert_eq!(function_node.parameter().origin(), &origin);

    for (ty, build) in [
        (Type::Bool, 0_u8),
        (Type::Unit, 1_u8),
        (Type::Bool, 2_u8),
        (Type::Int, 3_u8),
    ] {
        let mut builder = CoreBuilder::new();
        let root = match build {
            0 => builder.boolean(true, ty.clone(), origin.clone()),
            1 => builder.unit(ty.clone(), origin.clone()),
            2 => {
                let left = builder
                    .integer(integer("1"), Type::Int, origin.clone())
                    .expect("small arena");
                let right = builder
                    .integer(integer("1"), Type::Int, origin.clone())
                    .expect("small arena");
                builder.primitive(Primitive::Equal, left, right, ty.clone(), origin.clone())
            }
            _ => {
                let left = builder
                    .integer(integer("2"), Type::Int, origin.clone())
                    .expect("small arena");
                let right = builder
                    .integer(integer("3"), Type::Int, origin.clone())
                    .expect("small arena");
                builder.primitive(Primitive::Multiply, left, right, ty.clone(), origin.clone())
            }
        }
        .expect("small arena");
        let validated = validate(
            builder.finish(root).expect("root belongs to arena"),
            &[&file],
        )
        .expect("well-typed value should validate");
        let kind = &validated.node(root).expect("validated root").kind;
        assert!(matches!(
            kind,
            PureExprKind::Value(PureValue::Boolean(_))
                | PureExprKind::Value(PureValue::Unit(_))
                | PureExprKind::Computation(PureComputation::Primitive(_))
        ));
    }
}

#[test]
fn binding_initializer_does_not_see_the_binder_it_defines() {
    let file = source("let x = x; x");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let initializer = builder
        .variable(binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let body = builder
        .variable(binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let root = builder
        .binding(binder, initializer, body, Type::Int, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("binding initializer must use the incoming scope");
    assert_eq!(error.reason(), ValidationReason::Scope);
    assert_eq!(error.node(), Some(initializer));
}

#[test]
fn rejects_reusing_one_binder_identity_at_two_definition_sites() {
    let file = source("let x = (); let x = (); ()");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Unit, origin.clone())
        .expect("small binder set");
    let unit = builder
        .unit(Type::Unit, origin.clone())
        .expect("small arena");
    let inner = builder
        .binding(binder.clone(), unit, unit, Type::Unit, origin.clone())
        .expect("small arena");
    let root = builder
        .binding(binder, unit, inner, Type::Unit, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("a binder identity must name one definition site");
    assert_eq!(error.reason(), ValidationReason::Scope);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn shared_variable_reached_only_under_its_binder_is_valid() {
    let file = source("let x = 1; x + x");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let initializer = builder
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("small arena");
    let variable = builder
        .variable(binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let sum = builder
        .primitive(
            Primitive::Add,
            variable,
            variable,
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let root = builder
        .binding(binder, initializer, sum, Type::Int, origin)
        .expect("small arena");

    validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect("both shared paths introduce the binder");
}

#[test]
fn shared_variable_reached_inside_and_outside_its_binder_is_rejected_at_the_occurrence() {
    let file = source("malformed shared variable");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let variable = builder
        .variable(binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let root = builder
        .binding(binder, variable, variable, Type::Int, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("the initializer path does not introduce the binder");
    assert_eq!(error.reason(), ValidationReason::Scope);
    assert_eq!(error.node(), Some(variable));
}

#[test]
fn rejects_i001_variable_outside_its_binder_scope() {
    let file = source("x");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let root = builder
        .variable(binder.id(), Type::Int, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("free Core variable must be rejected");
    assert_eq!(error.reason(), ValidationReason::Scope);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_i002_primitive_with_wrong_result_type() {
    let file = source("1 + 2");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let left = builder
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("small arena");
    let right = builder
        .integer(integer("2"), Type::Int, origin.clone())
        .expect("small arena");
    let root = builder
        .primitive(Primitive::Add, left, right, Type::Bool, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("mis-typed primitive must be rejected");
    assert_eq!(error.reason(), ValidationReason::NodeType);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_i003_application_domain_disagreement() {
    let file = source("f true");
    let origin = whole_origin(&file);
    let mut builder = CoreBuilder::new();
    let parameter = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let body = builder
        .variable(parameter.id(), Type::Int, origin.clone())
        .expect("small arena");
    let function = builder
        .function(
            parameter,
            body,
            Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
            origin.clone(),
        )
        .expect("small arena");
    let argument = builder
        .boolean(true, Type::Bool, origin.clone())
        .expect("small arena");
    let root = builder
        .application(function, argument, Type::Int, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&file],
    )
    .expect_err("application domain mismatch must be rejected");
    assert_eq!(error.reason(), ValidationReason::ApplicationType);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_i004_origin_outside_the_admitted_source_set() {
    let admitted = source("1");
    let foreign = source("2");
    let mut builder = CoreBuilder::new();
    let root = builder
        .integer(integer("1"), Type::Int, whole_origin(&foreign))
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&admitted],
    )
    .expect_err("foreign provenance must be rejected");
    assert_eq!(error.reason(), ValidationReason::Provenance);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn rejects_related_provenance_that_crosses_source_files() {
    let primary = source("1");
    let related = source("2");
    let origin = Origin::Related {
        primary: Box::new(whole_origin(&primary)),
        related: vec![whole_origin(&related).primary_span()],
    };
    let mut builder = CoreBuilder::new();
    let root = builder
        .integer(integer("1"), Type::Int, origin)
        .expect("small arena");

    let error = validate(
        builder.finish(root).expect("root belongs to arena"),
        &[&primary, &related],
    )
    .expect_err("relations must stay within the primary source file");
    assert_eq!(error.reason(), ValidationReason::Provenance);
}

#[test]
fn rejects_a_root_handle_from_another_arena_even_when_its_index_exists() {
    let file = source("()");
    let origin = whole_origin(&file);
    let mut first = CoreBuilder::new();
    let foreign_root = first
        .unit(Type::Unit, origin.clone())
        .expect("small first arena");
    let mut second = CoreBuilder::new();
    let _local_root = second.unit(Type::Unit, origin).expect("small second arena");

    let error = second
        .finish(foreign_root)
        .expect_err("a root handle must identify its own arena");
    assert_eq!(error, ash::core::BuildError::InvalidNodeId);
}

#[test]
fn validation_rejects_a_foreign_child_even_when_its_index_exists_locally() {
    let file = source("1 + 2");
    let origin = whole_origin(&file);
    let mut first = CoreBuilder::new();
    let foreign_left = first
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("small first arena");

    let mut second = CoreBuilder::new();
    let _local_left = second
        .integer(integer("1"), Type::Int, origin.clone())
        .expect("small second arena");
    let right = second
        .integer(integer("2"), Type::Int, origin.clone())
        .expect("small second arena");
    let root = second
        .primitive(Primitive::Add, foreign_left, right, Type::Int, origin)
        .expect("unchecked construction accepts child handles");
    let error = validate(second.finish(root).expect("local root"), &[&file])
        .expect_err("validation must reject a child from another arena");
    assert_eq!(error.reason(), ValidationReason::NodeBounds);
    assert_eq!(error.node(), Some(root));
}

#[test]
fn validated_lookup_rejects_a_handle_from_another_arena() {
    let file = source("()");
    let origin = whole_origin(&file);
    let mut first = CoreBuilder::new();
    let first_root = first
        .unit(Type::Unit, origin.clone())
        .expect("small first arena");
    let first = validate(first.finish(first_root).expect("local root"), &[&file])
        .expect("valid first arena");

    let mut second = CoreBuilder::new();
    let second_root = second.unit(Type::Unit, origin).expect("small second arena");
    let _second = validate(second.finish(second_root).expect("local root"), &[&file])
        .expect("valid second arena");

    assert!(first.node(second_root).is_none());
}
