use std::{
    collections::HashSet,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{
        EffectExprKind, EffectOperation, EffectOperationFamily, PureComputation, PureExprKind,
        PureValue, ValidatedEffectProgram,
        dialect::CoreOperationFamily,
        transform::{fold_effect_literal_primitives, identity_effect_traversal},
        validate_effect_modules,
    },
    driver::{RunConfiguration, run_path},
    elaborate::{EffectElaborator, TypeError, check_module, link_modules},
    eval::{TraceEvent, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    interface::{EvidenceNode, EvidenceSlot, InterfaceId, MethodId, RequirementOwner},
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{
        CheckedDefinition, CheckedModule, ResolvedExpr, ResolvedExprKind, ResolvedLocalDeclaration,
        ResolvedTermName,
    },
    source::Origin,
    types::{EffectInstance, EffectRow, Kind, Type},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct InterfaceFixture(PathBuf);

impl InterfaceFixture {
    fn create(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir()
                .join(format!("ash-interface-check-{}-{id}", std::process::id()));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join("entry.ash");
                    fs::write(&path, text).expect("the interface fixture should be writable");
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("interface fixture directory should be creatable: {error}"),
            }
        }
    }
}

impl Drop for InterfaceFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn linked_method_product_fixture() -> InterfaceFixture {
    let fixture_directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/method-parameters/linked-product");
    let interface = fs::read_to_string(fixture_directory.join("interface.ash"))
        .expect("the retained interface fixture should be readable");
    let implementation = fs::read_to_string(fixture_directory.join("implementation.ash"))
        .expect("the retained implementation fixture should be readable");
    let entry = fs::read_to_string(fixture_directory.join("entry.ash"))
        .expect("the retained entry fixture should be readable");
    let fixture = InterfaceFixture::create(&entry);
    let staged_directory = fixture
        .0
        .parent()
        .expect("the staged linked product should have a parent directory");
    fs::write(staged_directory.join("api.ash"), interface)
        .expect("the reserved interface fixture should stage under a valid module identifier");
    fs::write(staged_directory.join("carrier.ash"), implementation)
        .expect("the implementation fixture should stage under its imported module identity");
    fixture
}

fn check_error(text: &str) -> TypeError {
    let fixture = InterfaceFixture::create(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the interface fixture should load");
    try_checked_graph(&graph).expect_err("the interface fixture should fail checking")
}

fn checked_module(text: &str) -> CheckedModule {
    checked_module_with_default_row(text).0
}

fn checked_module_with_default_row(text: &str) -> (CheckedModule, EffectRow) {
    let fixture = InterfaceFixture::create(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the interface fixture should load");
    let checked = checked_graph(&graph);
    let defining = checked
        .iter()
        .find(|module| {
            graph
                .module(module.module())
                .expect("every checked module retains its loaded source")
                .source()
                .display_path()
                == "@compiler.region"
        })
        .expect("the defining compiler service remains checked");
    let mut effects = defining
        .effects()
        .iter()
        .filter(|effect| effect.spelling == "DefaultAlloc");
    let effect = effects
        .next()
        .expect("the defining checked service retains DefaultAlloc");
    assert!(
        effects.next().is_none(),
        "the service effect identity is unique"
    );
    assert_eq!(effect.id.module(), defining.module());
    assert!(effect.parameters.is_empty());
    let row = EffectRow::singleton(EffectInstance::new(effect.id, Box::new([])));
    let entry = checked
        .into_iter()
        .find(|module| module.module() == graph.entry())
        .expect("the entry module should remain checked");
    (entry, row)
}

fn checked_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
    try_checked_graph(graph).expect("the interface fixture graph should check")
}

fn try_checked_graph(graph: &ModuleGraph) -> Result<Vec<CheckedModule>, TypeError> {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked: &&CheckedModule| checked.module() == edge.target())
                    .expect("dependency order should check the target first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("checked dependency exports should authenticate their edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the interface fixture graph should resolve");
        checked.push(check_module(resolved)?);
    }
    Ok(checked)
}

fn check_valid(text: &str) {
    drop(checked_module(text));
}

fn reason(error: &TypeError) -> String {
    let TypeError::Interface(diagnostic) = error else {
        panic!("the fixture should produce a source checking error");
    };
    diagnostic.reason.to_string()
}

fn observe_source(text: &str, expected_value: &str, expected_type: Type) {
    let fixture = InterfaceFixture::create(text);
    let observation = run_path(RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("the interface fixture should complete the modular pipeline");

    assert_eq!(observation.value_display(), expected_value);
    assert_eq!(observation.ty(), &expected_type);
}

fn validated_interface_core(text: &str) -> ValidatedEffectProgram {
    let fixture = InterfaceFixture::create(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the interface Core fixture should load");
    let checked = checked_graph(&graph);
    let linked = link_modules(checked, graph.entry()).expect("the interface Core should link");
    let linked = validate_interface_evidence(linked)
        .expect("the interface Core evidence should authenticate");
    let mut elaborator = EffectElaborator::for_module_program(&linked)
        .expect("the interface Core namespace should fit");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("the interface Core should elaborate");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the interface Core should finish");
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
    validate_effect_modules(unchecked, &sources, &module_sources)
        .expect("the interface Core should independently validate")
}

fn reachable_core_nodes(
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

fn method_occurrences(definition: &CheckedDefinition, method: MethodId) -> Vec<&EvidenceSlot> {
    let mut expressions = Vec::new();
    match definition.kind() {
        ash::resolved::ResolvedDefinitionKind::Equational(global)
        | ash::resolved::ResolvedDefinitionKind::ForeignConstant(global) => {
            expressions.extend(global.equations.iter().map(|equation| &equation.body));
        }
        ash::resolved::ResolvedDefinitionKind::InlineOperational(global) => {
            expressions.push(global.body.result.as_ref());
            for declaration in &global.body.declarations {
                schedule_local_expressions(declaration, &mut expressions);
            }
        }
    }

    let mut slots = Vec::new();
    while let Some(expression) = expressions.pop() {
        match &expression.kind {
            ResolvedExprKind::Cleanup(cleanup) => {
                expressions.push(&cleanup.action);
                expressions.push(&cleanup.body);
            }
            ResolvedExprKind::Occurrence(occurrence)
                if occurrence.term == ResolvedTermName::Method(method) =>
            {
                let [slot] = occurrence.evidence.as_ref() else {
                    panic!("one method occurrence should own one interface obligation");
                };
                slots.push(slot);
            }
            ResolvedExprKind::Occurrence(_)
            | ResolvedExprKind::String(_)
            | ResolvedExprKind::Integer(_)
            | ResolvedExprKind::Boolean(_)
            | ResolvedExprKind::Unit
            | ResolvedExprKind::Discard(_)
            | ResolvedExprKind::Retain(_)
            | ResolvedExprKind::Constructor(_) => {}
            ResolvedExprKind::Tuple(elements) => expressions.extend(elements),
            ResolvedExprKind::Apply(application) => {
                expressions.push(application.argument.as_ref());
                expressions.push(application.function.as_ref());
            }
            ResolvedExprKind::Add(binary)
            | ResolvedExprKind::Multiply(binary)
            | ResolvedExprKind::Equal(binary) => {
                expressions.push(binary.right.as_ref());
                expressions.push(binary.left.as_ref());
            }
            ResolvedExprKind::Block(block) => {
                expressions.push(block.result.as_ref());
                for declaration in &block.declarations {
                    schedule_local_expressions(declaration, &mut expressions);
                }
            }
            ResolvedExprKind::Function(function) => {
                expressions.push(function.body.result.as_ref());
                for declaration in &function.body.declarations {
                    schedule_local_expressions(declaration, &mut expressions);
                }
            }
            ResolvedExprKind::Match(matched) => {
                expressions.push(matched.scrutinee.as_ref());
                expressions.extend(matched.arms.iter().map(|arm| &arm.body));
            }
            ResolvedExprKind::Perform(request) => expressions.push(&request.operand),
            ResolvedExprKind::Handle(handler) => {
                expressions.push(&handler.body);
                if let Some(store) = &handler.store {
                    expressions.push(store);
                }
                expressions.extend(handler.clauses.iter().map(|clause| &clause.body));
            }
            ResolvedExprKind::Resume(resume) => expressions.push(&resume.value),
            ResolvedExprKind::Resource(resource) => {
                expressions.push(&resource.initializer);
                expressions.push(&resource.body);
            }
            ResolvedExprKind::Store(store) => {
                expressions.push(&store.initializer);
                expressions.push(&store.body);
            }
            ResolvedExprKind::Network(network) => {
                expressions.push(&network.initializer);
                expressions.push(&network.body);
            }
            ResolvedExprKind::Region(region) => {
                if let Some(provider) = &region.provider {
                    expressions.push(provider);
                }
                expressions.push(&region.body);
            }
            ResolvedExprKind::RegionSelection(selection) => {
                expressions.push(&selection.region);
                expressions.push(&selection.body);
            }
        }
    }
    slots.reverse();
    slots
}

fn schedule_local_expressions<'a>(
    declaration: &'a ResolvedLocalDeclaration,
    expressions: &mut Vec<&'a ResolvedExpr>,
) {
    match declaration {
        ResolvedLocalDeclaration::Evidence(source) => {
            expressions.extend(
                source
                    .method_groups
                    .iter()
                    .flat_map(|group| group.equations.iter().map(|equation| &equation.body)),
            );
        }
        ResolvedLocalDeclaration::Binding(binding) => expressions.push(&binding.initializer),
        ResolvedLocalDeclaration::Recursive(group) => {
            expressions.extend(group.members.iter().map(|member| &member.initializer));
        }
        ResolvedLocalDeclaration::Newtype(_) => {}
    }
}

#[test]
fn rejects_interface_method_without_parameter_occurrence() {
    let error = check_error("interface Equal<A> {\nequal : (Int, Int) -> Bool\n}\n");

    assert_eq!(reason(&error), "interface.method-parameter");
}

#[test]
fn ordinary_multi_parameter_relation_selects_and_evaluates() {
    let source = concat!(
        "interface Pairwise<Left, Right> {\n",
        "pairwise : (Left, Right) -> Bool\n",
        "}\n\n",
        "impl Pairwise<Int, Bool> {\n",
        "pairwise pair = true\n",
        "}\n\n",
        "main : Unit -> Bool\n",
        "main () = pairwise((1, true))\n",
    );
    let checked = checked_module(source);
    let [interface] = checked.interface_facts() else {
        panic!("the ordinary relation should retain one checked interface");
    };
    assert_eq!(
        interface
            .parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["Left", "Right"],
    );
    let [implementation] = checked.implementation_facts() else {
        panic!("the ordinary relation should retain one checked implementation");
    };
    assert_eq!(implementation.interface(), interface.id);
    assert_eq!(
        implementation.arguments(),
        &[
            ash::types::KindedArgument::TypeArg(Type::Int),
            ash::types::KindedArgument::TypeArg(Type::Bool)
        ]
    );

    let method = MethodId::new(interface.id, 0);
    let main = checked
        .definitions()
        .iter()
        .find(|definition| match definition.kind() {
            ash::resolved::ResolvedDefinitionKind::Equational(global)
            | ash::resolved::ResolvedDefinitionKind::ForeignConstant(global) => {
                global.interface.name.spelling == "main"
            }
            ash::resolved::ResolvedDefinitionKind::InlineOperational(_) => false,
        })
        .expect("the checked main definition should remain available");
    let occurrences = method_occurrences(main, method);
    let [occurrence] = occurrences.as_slice() else {
        panic!("main should retain one relational method occurrence");
    };
    let selection = occurrence
        .selection()
        .expect("the complete ordinary application should select evidence");
    assert_eq!(selection.interface(), interface.id);
    assert_eq!(
        selection.arguments(),
        &[
            ash::types::KindedArgument::TypeArg(Type::Int),
            ash::types::KindedArgument::TypeArg(Type::Bool)
        ]
    );
    assert!(matches!(
        selection.node(selection.root()),
        Some(EvidenceNode::Implementation { implementation: selected, .. })
            if selected == implementation.id
    ));

    drop(validated_interface_core(source));
    observe_source(source, "true", Type::Bool);
}

#[test]
fn ordinary_multi_parameter_method_requires_every_parameter() {
    let error = check_error(concat!(
        "interface Pairwise<Left, Right> {\n",
        "pairwise : Left -> Bool\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "interface.method-parameter");
}

#[test]
fn total_determination_admits_single_composite_and_non_final_dependents() {
    let checked = checked_module(concat!(
        "interface Iterable<I, Item> where I -> Item {\n",
        "next : I -> Item\n",
        "}\n\n",
        "interface Decode<Format, Source, Value> where (Format, Source) -> Value {\n",
        "decode : (Format, Source) -> Value\n",
        "}\n\n",
        "interface Lookup<Key, Value, Context> where (Key, Context) -> Value {\n",
        "lookup : (Key, Context) -> Value\n",
        "}\n",
    ));
    let [single, composite, non_final] = checked.interface_facts() else {
        panic!("all three total determinations should reach checked publication");
    };
    assert_eq!(
        single
            .parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["I", "Item"],
    );
    assert_eq!(
        composite
            .parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["Format", "Source", "Value"],
    );
    assert_eq!(
        non_final
            .parameters
            .iter()
            .map(|parameter| parameter.spelling.as_str())
            .collect::<Vec<_>>(),
        ["Key", "Value", "Context"],
    );
}

#[test]
fn rejects_non_partitioning_determination_parameters_uniformly() {
    let cases = [
        // Repeated determinant member.
        "interface Bad<A, B> where (A, A) -> B {\nbad : A -> B\n}\n",
        // Omitted interface parameter.
        "interface Bad<A, B, C> where A -> B {\nbad : A -> B\n}\n",
        // Determinant members do not follow declaration order.
        "interface Bad<A, B, C> where (B, A) -> C {\nbad : (A, B) -> C\n}\n",
        // The two sides overlap.
        "interface Bad<A, B, C> where (A, B) -> (B, C) {\nbad : (A, B) -> C\n}\n",
        // The written key covers the full parameter list, leaving no dependent complement.
        "interface Bad<A, B> where (A, B) -> A {\nbad : (A, B) -> A\n}\n",
        // Dependent members do not follow declaration order.
        "interface Bad<A, B, C> where A -> (C, B) {\nbad : A -> (B, C)\n}\n",
    ];

    for source in cases {
        let error = check_error(source);
        assert_eq!(reason(&error), "interface.determination-parameter");
    }
}

#[test]
fn determined_methods_require_the_complete_key_only() {
    check_valid(concat!(
        "type Wrapper<A> = Wrapper(A)\n\n",
        "interface Relation<Format, Value, Source> where (Format, Source) -> Value {\n",
        "dependent_in_domain : (Format, Source, Value) -> Int\n",
        "dependent_in_result : (Format, Source) -> Value\n",
        "dependent_nested : (Format, Source) -> Wrapper<Value>\n",
        "dependent_absent : (Format, Source) -> Int\n",
        "}\n",
    ));

    let missing_composite_member = check_error(concat!(
        "interface Relation<Format, Value, Source> where (Format, Source) -> Value {\n",
        "bad : Format -> Value\n",
        "}\n",
    ));
    assert_eq!(
        reason(&missing_composite_member),
        "interface.method-parameter"
    );

    let before_outer_shape = check_error(concat!(
        "interface Relation<Format, Value, Source> where (Format, Source) -> Value {\n",
        "bad : Format\n",
        "}\n",
    ));
    assert_eq!(reason(&before_outer_shape), "interface.method-parameter");

    let no_edge = check_error(concat!(
        "interface Ordinary<Left, Right> {\n",
        "ordinary : Left -> Int\n",
        "}\n",
    ));
    assert_eq!(reason(&no_edge), "interface.method-parameter");
}

#[test]
fn rejects_duplicate_global_requirement_before_scheme_construction() {
    let error = check_error(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nsame : A -> Bool where Equal<A>, Equal<A>\nsame value = true\n",
    );

    assert_eq!(reason(&error), "constraint.duplicate-requirement");
}

#[test]
fn rejects_interface_method_without_function_arrow() {
    let error = check_error("interface Marker<A> {\nmarker : A\n}\n");

    assert_eq!(reason(&error), "interface.method-not-function");
}

#[test]
fn rejects_interface_method_with_only_nested_function_arrow() {
    let error = check_error("interface Callable<A> {\ncallable : (A, Int -> Int)\n}\n");

    assert_eq!(reason(&error), "interface.method-not-function");
}

#[test]
fn rejects_invalid_parameter_before_nested_function_shape() {
    let error = check_error("interface Callable<A> {\ncallable : (B, Int -> Int)\n}\n");

    assert_eq!(reason(&error), "interface.method-parameter");
}

#[test]
fn accepts_top_level_function_with_nested_function_domain() {
    check_valid("interface Transform<A> {\ntransform : (A, Int -> Int) -> Int\n}\n");
}

#[test]
fn accepts_top_level_function_with_function_valued_codomain() {
    check_valid("interface Transform<A> {\ntransform : A -> Int -> Int\n}\n");
}

#[test]
fn top_level_function_with_nested_function_domain_completes_the_pipeline() {
    observe_source(
        concat!(
            "interface Transform<A> {\ntransform : (A, Int -> Int) -> Int\n}\n\n",
            "impl Transform<Int> {\n",
            "transform (value, operation) = operation value\n",
            "}\n\n",
            "increment : Int -> Int\n",
            "increment value = value + 1\n\n",
            "main : Unit -> Int\n",
            "main () = transform((41, increment))\n",
        ),
        "42",
        Type::Int,
    );
}

#[test]
fn absent_method_list_rejects_interface_method_local_type_variable() {
    let error = check_error("interface Combine<A> {\ncombine : (A, B) -> A\n}\n");

    assert_eq!(reason(&error), "interface.method-parameter");
}

#[test]
fn absent_method_list_owns_mixed_type_and_row_tail_parameter_failure() {
    let error = check_error(concat!(
        "interface Combine<A> {\n",
        "combine : (A, B) -> Unit ! {| B}\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "interface.method-parameter");
}

#[test]
fn polymorphic_method_occurrence_instantiates_all_binders_once() {
    let checked = checked_module(concat!(
        "interface Pairing<I> {\n",
        "pair<A, B> : (I, A, B) -> (A, B)\n",
        "}\n\n",
        "use_pairing<I> : I -> ((Int, Bool), (Bool, Int)) where Pairing<I>\n",
        "use_pairing value = (pair((value, 1, true)), pair((value, false, 2)))\n",
    ));
    let method = MethodId::new(InterfaceId::new(checked.module(), 0), 0);
    let definition = checked
        .definitions()
        .iter()
        .find(|definition| match definition.kind() {
            ash::resolved::ResolvedDefinitionKind::Equational(global)
            | ash::resolved::ResolvedDefinitionKind::ForeignConstant(global) => {
                global.interface.name.spelling == "use_pairing"
            }
            ash::resolved::ResolvedDefinitionKind::InlineOperational(_) => false,
        })
        .expect("the checked constrained global should remain available");
    let occurrences = method_occurrences(definition, method);
    let [first, second] = occurrences.as_slice() else {
        panic!("the body should retain two occurrences of one method scheme");
    };

    assert!(first.selection().is_some());
    assert!(second.selection().is_some());
    assert_eq!(first.method_arguments(), &[Type::Int, Type::Bool]);
    assert_eq!(second.method_arguments(), &[Type::Bool, Type::Int]);
}

#[test]
fn linked_polymorphic_method_evidence_evaluates() {
    // `interface` is a reserved Ash token, so the plan-mandated `interface.ash`
    // source is staged as `api.ash`; the graph still checks the three retained
    // fixture sources as distinct modules.
    let fixture = linked_method_product_fixture();
    let entry = fixture.0.clone();
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the linked polymorphic method product should load");
    let interface_module = graph
        .modules()
        .iter()
        .find(|module| module.canonical_path().file_name() == Some("api.ash".as_ref()))
        .expect("the separately checked interface module should load")
        .id();
    let implementation_module = graph
        .modules()
        .iter()
        .find(|module| module.canonical_path().file_name() == Some("carrier.ash".as_ref()))
        .expect("the separately checked implementation module should load")
        .id();
    let checked = checked_graph(&graph);
    let checked_interface = checked
        .iter()
        .find(|module| module.module() == interface_module)
        .expect("the interface module should check independently");
    let [functor] = checked_interface.interface_facts() else {
        panic!("the product should retain exactly one higher-kinded interface");
    };
    let [functor_parameter] = functor.parameters.as_ref() else {
        panic!("Functor should retain exactly one interface parameter");
    };
    assert_eq!(
        functor_parameter.kind,
        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
    );
    let [map_method] = functor.methods.as_ref() else {
        panic!("Functor should retain exactly map");
    };
    assert_eq!(map_method.type_parameters().len(), 2);
    let map_pair = checked_interface
        .definitions()
        .iter()
        .find(|definition| match definition.kind() {
            ash::resolved::ResolvedDefinitionKind::Equational(global)
            | ash::resolved::ResolvedDefinitionKind::ForeignConstant(global) => {
                global.interface.name.spelling == "map_pair"
            }
            ash::resolved::ResolvedDefinitionKind::InlineOperational(_) => false,
        })
        .expect("the constrained consumer should check separately from its implementation");
    let occurrences = method_occurrences(map_pair, map_method.id);
    assert_eq!(occurrences.len(), 2);
    assert!(
        occurrences
            .iter()
            .any(|slot| slot.method_arguments() == [Type::Int, Type::Bool]),
    );
    assert!(
        occurrences
            .iter()
            .any(|slot| slot.method_arguments() == [Type::Bool, Type::Int]),
    );

    let checked_implementation = checked
        .iter()
        .find(|module| module.module() == implementation_module)
        .expect("the concrete implementation module should check independently");
    let [implementation] = checked_implementation.implementation_facts() else {
        panic!("the carrier module should retain one concrete implementation");
    };
    let [implementation_method] = implementation.methods.as_ref() else {
        panic!("the concrete implementation should retain map");
    };
    assert_eq!(implementation_method.scheme.type_parameters.len(), 2);
    let implementation_method_binder = implementation_method.binder;
    let interface_source = graph
        .module(interface_module)
        .expect("the interface module should remain in the graph")
        .source();
    let implementation_source = graph
        .module(implementation_module)
        .expect("the implementation module should remain in the graph")
        .source();
    let exact_source_range = |source: &ash::source::SourceFile, snippet: &str| {
        let mut occurrences = source.text().match_indices(snippet);
        let (start, _) = occurrences.next().expect("the exact fixture text exists");
        assert!(occurrences.next().is_none(), "fixture text must be unique");
        (
            source.id(),
            u32::try_from(start).unwrap(),
            u32::try_from(start + snippet.len()).unwrap(),
        )
    };
    let method_range = exact_source_range(
        implementation_source,
        "map (function, Box(value)) = Box(function(value))",
    );
    let Origin::Related { primary, related } = &implementation_method.origin else {
        panic!("the separately checked implementation method should retain exact provenance");
    };
    let primary = primary.primary_span();
    assert_eq!(
        (
            primary.source(),
            primary.range().start(),
            primary.range().end()
        ),
        method_range,
    );
    assert_eq!(
        related
            .iter()
            .map(|span| (span.source(), span.range().start(), span.range().end()))
            .collect::<Vec<_>>(),
        [
            exact_source_range(
                implementation_source,
                "pub impl Functor<Box> {\n    map (function, Box(value)) = Box(function(value))\n}",
            ),
            method_range,
            exact_source_range(interface_source, "map<A, B> : (A -> B, F<A>) -> F<B>"),
            exact_source_range(interface_source, "(A -> B, F<A>) -> F<B>"),
            exact_source_range(implementation_source, "Box(function(value))"),
        ],
        "the checked carrier should keep the full cross-module method and annotation provenance before Core erasure",
    );

    let linked = link_modules(checked, graph.entry()).expect("the product should link");
    let linked = validate_interface_evidence(linked)
        .expect("the product's polymorphic method evidence should authenticate");
    let mut elaborator = EffectElaborator::for_module_program(&linked)
        .expect("the product Core namespace should fit");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("the authenticated polymorphic evidence should lower");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the linked product Core should finish");
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
    let original = validate_effect_modules(unchecked, &sources, &module_sources)
        .expect("the linked product Core should independently validate");

    let reachable = reachable_core_nodes(&original, original.root());
    let recursive_initializers = reachable
        .iter()
        .filter_map(|id| {
            let node = original.node(*id)?;
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
    let concrete_method_applications = reachable
        .iter()
        .copied()
        .filter(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                application,
            ))) = &original
                .node(*id)
                .expect("reachable application exists")
                .kind
            else {
                return false;
            };
            matches!(
                original.node(application.function()).map(|node| &node.kind),
                Some(EffectExprKind::Pure(PureExprKind::Variable(variable)))
                    if variable.binder() == implementation_method_binder
            )
        })
        .collect::<Vec<_>>();
    let [adapter_type_application] = concrete_method_applications.as_slice() else {
        panic!("one selection should instantiate the concrete implementation method once");
    };
    let adapters = reachable
        .iter()
        .copied()
        .filter(|id| {
            !recursive_initializers.contains(id)
                && reachable_core_nodes(&original, *id).contains(adapter_type_application)
                && matches!(
                    original.node(*id).map(|node| &node.kind),
                    Some(EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
                        abstraction
                    )))) if abstraction.parameters().len() == 2
                )
        })
        .collect::<Vec<_>>();
    let [adapter] = adapters.as_slice() else {
        panic!("one concrete selection should lower through one generated map adapter");
    };
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
        adapter_abstraction,
    ))) = &original
        .node(*adapter)
        .expect("the generated adapter should exist")
        .kind
    else {
        unreachable!("the selected adapter is a type abstraction");
    };
    let [(adapter_a, Kind::Type), (adapter_b, Kind::Type)] = adapter_abstraction.parameters()
    else {
        panic!("the generated adapter should preserve both map parameter kinds and order");
    };
    let adapter_type_application = *adapter_type_application;
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
        adapter_application,
    ))) = &original
        .node(adapter_type_application)
        .expect("the adapter implementation application should exist")
        .kind
    else {
        panic!("the generated adapter should type-apply the concrete implementation method");
    };
    assert_eq!(
        adapter_application.arguments(),
        &[Type::Variable(*adapter_a), Type::Variable(*adapter_b),],
    );
    let implementation_variable = adapter_application.function();
    let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &original
        .node(implementation_variable)
        .expect("the adapter implementation variable should exist")
        .kind
    else {
        panic!("the adapter should retain the one implementation-method body");
    };
    assert_eq!(variable.binder(), implementation_method_binder);

    let mut evidence_binders = Vec::new();
    for id in &reachable {
        let kind = &original.node(*id).expect("reachable node exists").kind;
        if matches!(
            kind,
            EffectExprKind::Operation(EffectOperation::RegionClosure(_))
        ) {
            EffectOperationFamily::visit_operation_binders(kind, &mut |parameter| {
                if matches!(parameter.ty(), Type::Forall(parameters, _) if parameters.len() == 2) {
                    evidence_binders.push(parameter.id());
                }
            });
        }
    }
    let [evidence_binder] = evidence_binders.as_slice() else {
        panic!("map_pair should expose one polymorphic evidence domain");
    };
    let mut int_to_bool = None;
    let mut bool_to_int = None;
    for type_application in reachable.iter().copied() {
        let Some(node) = original.node(type_application) else {
            continue;
        };
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
            application,
        ))) = &node.kind
        else {
            continue;
        };
        let Some(function) = original.node(application.function()) else {
            continue;
        };
        let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &function.kind else {
            continue;
        };
        if variable.binder() != *evidence_binder {
            continue;
        }
        let source_application = reachable
            .iter()
            .copied()
            .find(|candidate| {
                matches!(
                    original.node(*candidate).map(|node| &node.kind),
                    Some(EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))))
                        if application.function() == type_application
                )
            })
            .expect("each instantiated method should receive its source argument strictly");
        let retained = (source_application, type_application, application.function());
        match application.arguments() {
            [Type::Int, Type::Bool] => int_to_bool = Some(retained),
            [Type::Bool, Type::Int] => bool_to_int = Some(retained),
            arguments => panic!("unexpected map instantiation {arguments:?}"),
        }
    }
    let int_to_bool = int_to_bool.expect("map_pair should instantiate map at Int and Bool");
    let bool_to_int = bool_to_int.expect("map_pair should instantiate map at Bool and Int");

    let evaluation =
        evaluate_effect(&original).expect("the linked product should erase and evaluate");
    assert_eq!(evaluation.value.to_string(), "(Box(true), Box(42))");
    let entered = evaluation
        .trace
        .iter()
        .map(|event| match event {
            TraceEvent::Enter(id) => *id,
        })
        .collect::<Vec<_>>();
    let evidence_nodes = [
        *adapter,
        adapter_type_application,
        implementation_variable,
        int_to_bool.0,
        int_to_bool.1,
        int_to_bool.2,
        bool_to_int.0,
        bool_to_int.1,
        bool_to_int.2,
    ];
    let erased_evidence_trace = entered
        .into_iter()
        .filter(|node| evidence_nodes.contains(node))
        .collect::<Vec<_>>();
    // Main captures the implementation during group initialization. Adapter forwarding
    // looks it up again and applies type metadata without entering the TypeApplication.
    // The inner source function then captures its evidence before the strict calls.
    assert_eq!(
        erased_evidence_trace,
        [
            implementation_variable,
            *adapter,
            implementation_variable,
            int_to_bool.2,
            int_to_bool.0,
            int_to_bool.1,
            int_to_bool.2,
            bool_to_int.0,
            bool_to_int.1,
            bool_to_int.2,
        ],
        "polymorphic evidence should preserve exact capture, forwarding, and strict application order",
    );

    for transformed in [
        identity_effect_traversal(&original)
            .expect("identity traversal should preserve method evidence"),
        fold_effect_literal_primitives(&original)
            .expect("literal folding should preserve method evidence"),
    ] {
        let transformed = validate_effect_modules(transformed, &sources, &module_sources)
            .expect("each transformed product should pass fresh independent validation");
        let transformed_evaluation =
            evaluate_effect(&transformed).expect("each freshly validated product should evaluate");
        assert_eq!(
            transformed_evaluation.value.to_string(),
            evaluation.value.to_string()
        );
        assert!(ash::types::same_type(
            &transformed
                .node(transformed.root())
                .expect("the transformed root should exist")
                .ty,
            &original
                .node(original.root())
                .expect("the original root should exist")
                .ty,
        ));
    }

    let observation = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("the linked polymorphic method product should complete the library pipeline");
    assert_eq!(observation.value_display(), "(Box(true), Box(42))");
    assert_eq!(observation.type_display(), "(Box<Bool>, Box<Int>)");
}

#[test]
fn compound_method_local_variable_keeps_interface_failure_ownership() {
    let error = check_error(
        "type Pair<Left, Right> = Pair(Left, Right)\n\ninterface Combine<A> {\ncombine : Pair<A, B> -> A\n}\n",
    );

    assert_eq!(reason(&error), "interface.method-parameter");
}

#[test]
fn rejects_undetermined_global_requirement_parameter() {
    let error = check_error(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nsame : A -> Bool where Equal<B>\nsame value = true\n",
    );

    assert_eq!(reason(&error), "constraint.undetermined-parameter");
}

#[test]
fn determined_global_retains_dependent_only_binder_in_scheme_order() {
    let checked = checked_module(concat!(
        "interface Iterator<I, Item> where I -> Item {\n",
        "measure : I -> Int\n",
        "}\n\n",
        "size<I, Item> : I -> Int where Iterator<I, Item>\n",
        "size value = measure value\n",
    ));
    let scheme = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "size")
        .expect("the determined constrained global should retain its scheme");
    let [key, dependent] = scheme.scheme.type_parameters.as_ref() else {
        panic!("the scheme should retain key then dependent binder order");
    };
    let [requirement] = scheme.scheme.requirements.as_ref() else {
        panic!("the scheme should retain its complete abstract requirement");
    };

    assert!(
        matches!(requirement.arguments(), [ash::types::KindedArgument::TypeArg(Type::Variable(found)), ash::types::KindedArgument::TypeArg(Type::Variable(output))]
        if *found == key.0 && *output == dependent.0)
    );
}

#[test]
fn determined_global_rejects_missing_key_even_when_another_requirement_supplies_it() {
    let error = check_error(concat!(
        "interface First<A, B> where A -> B {\nfirst : A -> Int\n}\n",
        "interface Second<B, C> where B -> C {\nsecond : B -> Int\n}\n\n",
        "chain<A, B, C> : A -> C where First<A, B>, Second<B, C>\n",
        "chain value = value\n",
    ));

    assert_eq!(reason(&error), "constraint.undetermined-parameter");
}

#[test]
fn determined_global_requirement_pair_classifies_full_duplicate_and_key_conflict() {
    let duplicate = check_error(concat!(
        "interface Relation<A, B> where A -> B {\nrelate : A -> Int\n}\n\n",
        "probe<A, B> : A -> Int where Relation<A, B>, Relation<A, B>\n",
        "probe value = 0\n",
    ));
    assert_eq!(reason(&duplicate), "constraint.duplicate-requirement");

    let conflict = check_error(concat!(
        "interface Relation<A, B> where A -> B {\nrelate : A -> Int\n}\n\n",
        "probe<A, B, C> : A -> Int where Relation<A, B>, Relation<A, C>\n",
        "probe value = 0\n",
    ));
    assert_eq!(reason(&conflict), "constraint.determination-conflict");
}

#[test]
fn explicit_requirement_only_binder_keeps_determination_failure_ownership() {
    let error = check_error(
        "type Pair<Left, Right> = Pair(Left, Right)\n\ninterface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nsame<B : Type, A : Type> : A -> Bool where Equal<Pair<A, B>>\nsame value = true\n",
    );

    assert_eq!(reason(&error), "constraint.undetermined-parameter");
}

#[test]
fn rejects_public_global_requirement_on_private_interface() {
    let error = check_error(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\npub same : A -> Bool where Equal<A>\nsame value = true\n",
    );

    assert_eq!(reason(&error), "constraint.private-interface");
}

#[test]
fn accepts_private_global_requirement_on_private_interface() {
    check_valid(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nsame : A -> Bool where Equal<A>\nsame value = true\n",
    );
}

#[test]
fn accepts_public_method_signature_that_retains_a_hidden_nominal_identity() {
    check_valid("type Hidden = Hidden\n\npub interface Reveal<A> {\nreveal : A -> Hidden\n}\n");
}

#[test]
fn checked_equational_and_operational_schemes_keep_ordered_requirements_outside_types() {
    let (checked, default_row) = checked_module_with_default_row(concat!(
        "interface Equal<A> {\n",
        "equal : (A, A) -> Bool\n",
        "}\n",
        "same : A -> Bool where Equal<A>\n",
        "same value = true\n",
        "fn same_operational(value : B) -> Bool where Equal<B> {\n",
        "true\n",
        "}\n",
    ));

    assert_eq!(checked.schemes().len(), 2);
    for scheme in checked.schemes() {
        assert_eq!(scheme.scheme.type_parameters.len(), 1);
        assert_eq!(scheme.scheme.requirements.len(), 1);
        let function = scheme
            .scheme
            .value_type()
            .function_view()
            .expect("the checked scheme remains callable");
        assert_eq!(function.effects(), Some(&default_row));
        let requirement = &scheme.scheme.requirements[0];
        assert_eq!(
            requirement.id.owner(),
            RequirementOwner::Global(scheme.binder)
        );
        assert_eq!(requirement.id.declaration(), 0);
        let [argument] = requirement.arguments() else {
            panic!("the unary Equal requirement should retain one argument");
        };
        assert_eq!(
            argument,
            &ash::types::KindedArgument::TypeArg(Type::Variable(
                scheme.scheme.type_parameters[0].0
            ))
        );
    }
}

#[test]
fn checked_global_scheme_retains_declared_function_kind() {
    let (checked, default_row) = checked_module_with_default_row(concat!(
        "type Holder<F : Type -> Type> = Holder\n\n",
        "uses<F : Type -> Type> : Holder<F> -> Bool\n",
        "uses value = true\n",
    ));
    let [checked] = checked.schemes() else {
        panic!("the fixture should retain one checked global scheme");
    };
    let [(parameter, kind)] = checked.scheme.type_parameters.as_ref() else {
        panic!("the checked scheme should retain one canonical binder");
    };

    assert_eq!(
        kind,
        &Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
    );
    let function = checked
        .scheme
        .value_type()
        .function_view()
        .expect("the checked global should remain callable");
    assert_eq!(function.effects(), Some(&default_row));
    let Type::Application(_, argument) = function.domain() else {
        panic!("the Holder application should remain canonical");
    };
    assert_eq!(argument.as_ref(), &Type::Variable(*parameter));
}

#[test]
fn cross_module_constraint_lowers_to_method_evidence() {
    let fixture = InterfaceFixture::create(concat!(
        "import library as Library\n",
        "import library (impl Equal)\n",
        "main : Unit -> Bool\n",
        "main () = Library.same((1, 1))\n",
    ));
    fs::write(
        fixture
            .0
            .parent()
            .expect("entry fixture has a parent")
            .join("library.ash"),
        concat!(
            "pub interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n",
            "pub impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n",
            "pub same : (A, A) -> Bool where Equal<A>\n",
            "same pair = equal pair\n",
        ),
    )
    .expect("the dependency fixture should be writable");

    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the interface fixture graph should load");
    let checked = checked_graph(&graph);
    let library_id = graph
        .modules()
        .iter()
        .find(|module| module.source().display_path().ends_with("library.ash"))
        .expect("the defining library source remains loaded")
        .id();
    let library = checked
        .iter()
        .find(|module| module.module() == library_id)
        .expect("the dependency should remain checked");
    let implementation_method = library.implementation_facts()[0].methods[0].binder;
    let same = library
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "same")
        .expect("the constrained dependency global should remain checked")
        .binder;
    let main = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .expect("the entry module should remain checked")
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .expect("the entry main should remain checked")
        .binder;
    let linked = link_modules(checked, graph.entry()).expect("the checked graph should link");
    let linked =
        validate_interface_evidence(linked).expect("the linked evidence should authenticate");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("the graph namespace should reserve");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("validated interface evidence should lower through ordinary Core");
    assert_eq!(typed.ty, Type::Bool);
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the final Core builder should finish");
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
    let core = validate_effect_modules(unchecked, &sources, &module_sources)
        .expect("ordinary Core emitted from evidence lowering should validate");

    let reachable = reachable_core_nodes(&core, core.root());
    let groups = reachable
        .iter()
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) = &core.node(*id)?.kind
            else {
                return None;
            };
            Some((*id, group))
        })
        .collect::<Vec<_>>();
    let library_groups = groups
        .iter()
        .filter(|(_, group)| {
            group
                .members()
                .iter()
                .any(|member| member.binder().id() == same)
                && group
                    .members()
                    .iter()
                    .any(|member| member.binder().id() == implementation_method)
        })
        .collect::<Vec<_>>();
    let [(_, library_group)] = library_groups.as_slice() else {
        panic!("same and the original implementation method must own one defining group");
    };
    let same_initializer = library_group
        .members()
        .iter()
        .find(|member| member.binder().id() == same)
        .expect("the constrained global should remain a dependency group member")
        .initializer();
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
        abstraction,
    ))) = &core
        .node(same_initializer)
        .expect("same initializer should exist")
        .kind
    else {
        panic!("a constrained global must type-abstract before evidence binders");
    };
    let evidence_type = &core
        .node(abstraction.body())
        .expect("the quantified callable remains typed")
        .ty;
    let evidence_function = evidence_type
        .function_view()
        .expect("the first callable binds flattened evidence");
    let source_type = evidence_function.value();
    let source_function = source_type
        .function_view()
        .expect("the second callable binds the source parameter");
    let evidence_closures = reachable_core_nodes(&core, abstraction.body())
        .into_iter()
        .filter(|id| {
            let node = core.node(*id).expect("owned child remains present");
            matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::RegionClosure(_))
            ) && &node.ty == evidence_type
        })
        .collect::<Vec<_>>();
    let [evidence_closure] = evidence_closures.as_slice() else {
        panic!("the quantified initializer must contain one exact evidence callable");
    };
    let mut evidence_parameters = Vec::new();
    EffectOperationFamily::visit_operation_binders(
        &core.node(*evidence_closure).unwrap().kind,
        &mut |parameter| evidence_parameters.push((parameter.id(), parameter.ty().clone())),
    );
    let [(evidence_parameter, evidence_parameter_type)] = evidence_parameters.as_slice() else {
        panic!("the evidence callable must bind exactly one flattened parameter");
    };
    assert_eq!(evidence_parameter_type, evidence_function.domain());
    let source_closures = reachable_core_nodes(&core, *evidence_closure)
        .into_iter()
        .filter(|id| {
            let node = core.node(*id).expect("owned child remains present");
            matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::RegionClosure(_))
            ) && &node.ty == source_type
        })
        .collect::<Vec<_>>();
    let [source_closure] = source_closures.as_slice() else {
        panic!("the evidence callable must own one exact source callable");
    };
    let mut source_parameters = Vec::new();
    EffectOperationFamily::visit_operation_binders(
        &core.node(*source_closure).unwrap().kind,
        &mut |parameter| source_parameters.push((parameter.id(), parameter.ty().clone())),
    );
    let [(source_parameter, source_parameter_type)] = source_parameters.as_slice() else {
        panic!("the source callable must bind exactly one source parameter");
    };
    assert_ne!(evidence_parameter, source_parameter);
    assert_eq!(source_parameter_type, source_function.domain());
    assert!(
        library_group
            .members()
            .iter()
            .any(|member| member.binder().id() == implementation_method)
    );

    let entry_groups = groups
        .iter()
        .filter(|(_, group)| {
            group
                .members()
                .iter()
                .any(|member| member.binder().id() == main)
        })
        .collect::<Vec<_>>();
    let [(entry_group_id, entry_group)] = entry_groups.as_slice() else {
        panic!("main must own exactly one entry group");
    };
    assert_eq!(
        library_group.body(),
        *entry_group_id,
        "the entry group should directly follow its defining library"
    );
    let main_initializer = entry_group
        .members()
        .iter()
        .find(|member| member.binder().id() == main)
        .expect("main remains an entry member")
        .initializer();
    let entry_source = graph
        .module(graph.entry())
        .expect("entry remains loaded")
        .source();
    let expression = "Library.same((1, 1))";
    let start = entry_source
        .text()
        .find(expression)
        .expect("entry expression remains present");
    let expected_span = (
        entry_source.id(),
        u32::try_from(start).unwrap(),
        u32::try_from(start + expression.len()).unwrap(),
    );
    let source_applications = reachable_core_nodes(&core, main_initializer)
        .into_iter()
        .filter_map(|id| {
            let node = core.node(id)?;
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                application,
            ))) = &node.kind
            else {
                return None;
            };
            let span = node.origin.primary_span();
            ((span.source(), span.range().start(), span.range().end()) == expected_span)
                .then_some(application)
        })
        .collect::<Vec<_>>();
    let [source_application] = source_applications.as_slice() else {
        panic!(
            "the exact main initializer must contain one source application at its original span"
        );
    };
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
        evidence_application,
    ))) = &core
        .node(source_application.function())
        .expect("source application function should exist")
        .kind
    else {
        panic!("selected evidence should be applied before the source argument");
    };
    assert!(matches!(
        core.node(evidence_application.function())
            .expect("evidence application function should exist")
            .kind,
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
            _
        )))
    ));
    let EffectExprKind::Pure(PureExprKind::Variable(evidence_method)) = core
        .node(evidence_application.argument())
        .expect("evidence argument should exist")
        .kind
    else {
        panic!("concrete evidence should lower through its hidden implementation-method binder");
    };
    assert_eq!(evidence_method.binder(), implementation_method);
    let evaluation = evaluate_effect(&core).expect("cross-module evidence should evaluate");
    assert_eq!(evaluation.value.to_string(), "true");
    let observation = run_path(RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("the cross-module program should complete the public pipeline");
    assert_eq!(observation.value_display(), "true");
    assert_eq!(observation.ty(), &Type::Bool);
}

#[test]
fn facade_selection_lowers_through_the_original_core_binder() {
    let fixture = InterfaceFixture::create(concat!(
        "import facade (Equal, equal, same, impl Equal)\n",
        "main : Unit -> Bool\n",
        "main () = same((1, 1))\n",
    ));
    let directory = fixture.0.parent().expect("entry fixture has a parent");
    fs::write(
        directory.join("library.ash"),
        concat!(
            "pub interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n",
            "pub impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n",
            "pub same : (A, A) -> Bool where Equal<A>\n",
            "same pair = equal pair\n",
        ),
    )
    .expect("the defining fixture should be writable");
    fs::write(
        directory.join("facade.ash"),
        "pub import library (Equal, equal, same, impl Equal)\n",
    )
    .expect("the facade fixture should be writable");

    let observation = run_path(RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("the facade program should complete the public pipeline");
    assert_eq!(observation.value_display(), "true");
    assert_eq!(observation.ty(), &Type::Bool);

    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the facade interface graph should load");
    let checked = checked_graph(&graph);
    let library_id = graph
        .modules()
        .iter()
        .find(|module| module.source().display_path().ends_with("library.ash"))
        .expect("the defining library source remains loaded")
        .id();
    let library = checked
        .iter()
        .find(|module| module.module() == library_id)
        .expect("the defining module should retain the implementation");
    let implementation_method = library.implementation_facts()[0].methods[0].binder;
    let main = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .and_then(|module| {
            module
                .schemes()
                .iter()
                .find(|scheme| scheme.spelling == "main")
        })
        .expect("the entry main should remain checked")
        .binder;
    let linked =
        link_modules(checked, graph.entry()).expect("the checked facade graph should link");
    let linked = validate_interface_evidence(linked)
        .expect("the complete facade authorization should authenticate before Core");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("the graph namespace should reserve");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("facade evidence should lower through ordinary Core");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the final Core builder should finish");
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
    let core = validate_effect_modules(unchecked, &sources, &module_sources)
        .expect("facade lowering should pass the independent Core validator");

    let reachable = reachable_core_nodes(&core, core.root());
    let groups = reachable
        .iter()
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) = &core.node(*id)?.kind
            else {
                return None;
            };
            Some((*id, group))
        })
        .collect::<Vec<_>>();
    let library_groups = groups
        .iter()
        .filter(|(_, group)| {
            group
                .members()
                .iter()
                .any(|member| member.binder().id() == implementation_method)
        })
        .collect::<Vec<_>>();
    let [(library_group_id, library_group)] = library_groups.as_slice() else {
        panic!("the original implementation method must own exactly one defining group");
    };
    let entry_groups = groups
        .iter()
        .filter(|(_, group)| {
            group
                .members()
                .iter()
                .any(|member| member.binder().id() == main)
        })
        .collect::<Vec<_>>();
    let [(entry_group_id, entry_group)] = entry_groups.as_slice() else {
        panic!("main must own exactly one entry group");
    };
    assert_ne!(library_group_id, entry_group_id);
    assert_eq!(
        library_group.body(),
        *entry_group_id,
        "the body-free facade should add no runtime or Core group"
    );
    let main_initializer = entry_group
        .members()
        .iter()
        .find(|member| member.binder().id() == main)
        .expect("main remains an entry member")
        .initializer();
    let entry_source = graph
        .module(graph.entry())
        .expect("entry remains loaded")
        .source();
    let expression = "same((1, 1))";
    let start = entry_source
        .text()
        .find(expression)
        .expect("entry expression remains present");
    let expected_span = (
        entry_source.id(),
        u32::try_from(start).unwrap(),
        u32::try_from(start + expression.len()).unwrap(),
    );
    let source_applications = reachable_core_nodes(&core, main_initializer)
        .into_iter()
        .filter_map(|id| {
            let node = core.node(id)?;
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                application,
            ))) = &node.kind
            else {
                return None;
            };
            let span = node.origin.primary_span();
            ((span.source(), span.range().start(), span.range().end()) == expected_span)
                .then_some(application)
        })
        .collect::<Vec<_>>();
    let [source_application] = source_applications.as_slice() else {
        panic!(
            "the exact main initializer must contain one source application at its original span"
        );
    };
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
        evidence_application,
    ))) = &core
        .node(source_application.function())
        .expect("the source application function should exist")
        .kind
    else {
        panic!("selected evidence should remain an ordinary term application");
    };
    assert!(matches!(
        core.node(evidence_application.function())
            .expect("the constrained global function should exist")
            .kind,
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
            _
        )))
    ));
    let EffectExprKind::Pure(PureExprKind::Variable(evidence_method)) = core
        .node(evidence_application.argument())
        .expect("the evidence argument should exist")
        .kind
    else {
        panic!("facade evidence should lower to the defining implementation method");
    };
    assert_eq!(evidence_method.binder(), implementation_method);
}

#[test]
fn generic_option_impl_constructs_prerequisite_evidence() {
    observe_source(
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
            "impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n\n",
            "impl Equal<Option<A>> where Equal<A> {\n",
            "equal (None, None) = true\n",
            "equal (Some(left), Some(right)) = equal((left, right))\n",
            "equal pair = false\n",
            "}\n\n",
            "main : Unit -> Bool\n",
            "main () = equal((Some(42), Some(42)))\n",
        ),
        "true",
        Type::Bool,
    );
}

#[test]
fn generic_prerequisite_evidence_preserves_same_typed_method_slot_order() {
    observe_source(
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "interface Compare<A> {\n",
            "same : (A, A) -> Bool\n",
            "different : (A, A) -> Bool\n",
            "}\n\n",
            "impl Compare<Int> {\n",
            "same (left, right) = left == right\n",
            "different pair = false\n",
            "}\n\n",
            "impl Compare<Option<A>> where Compare<A> {\n",
            "same (Some(left), Some(right)) = same((left, right))\n",
            "same pair = false\n",
            "different pair = false\n",
            "}\n\n",
            "main : Unit -> Bool\n",
            "main () = same((Some(42), Some(42)))\n",
        ),
        "true",
        Type::Bool,
    );
}

#[test]
fn generic_two_prerequisite_slots_preserve_declaration_order() {
    observe_source(
        concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface First<A> {\nfirst : A -> Int\n}\n\n",
            "interface Second<A> {\nsecond : A -> Int\n}\n\n",
            "interface Combine<A> {\ncombine : A -> Int\n}\n\n",
            "impl First<Int> {\nfirst value = 4\n}\n\n",
            "impl Second<Int> {\nsecond value = 2\n}\n\n",
            "impl Combine<Wrap<A>> where First<A>, Second<A> {\n",
            "combine (Wrap(value)) = first value * 10 + second value\n",
            "}\n\n",
            "main : Unit -> Int\n",
            "main () = combine(Wrap(0))\n",
        ),
        "42",
        Type::Int,
    );
}

#[test]
fn generic_prerequisite_evidence_has_a_bounded_unspecialized_evaluation_trace() {
    let fixture = InterfaceFixture::create(concat!(
        "type Wrap<A> = Wrap(A)\n\n",
        "interface Read<A> {\nread : A -> Int\n}\n\n",
        "impl Read<Int> {\nread value = value\n}\n\n",
        "impl Read<Wrap<A>> where Read<A> {\n",
        "read (Wrap(value)) = read value\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = read(Wrap(42))\n",
    ));
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the generic evidence fixture should load");
    let checked = checked_graph(&graph);
    let module = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .expect("the actual source entry should remain checked");
    let [ground_implementation, generic_implementation] = module.implementation_facts() else {
        panic!("the fixture should retain its ground and generic implementations");
    };
    let ground_method = ground_implementation.methods[0].binder;
    let generic_method = generic_implementation.methods[0].binder;
    let main = module
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .expect("the fixture should retain main")
        .binder;

    let linked = link_modules(checked, graph.entry()).expect("the fixture should link");
    let linked =
        validate_interface_evidence(linked).expect("the generic evidence should authenticate");
    let mut elaborator = EffectElaborator::for_module_program(&linked)
        .expect("the fixture namespace should reserve");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("the generic evidence should lower");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the generic evidence Core should finish");
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
    let core = validate_effect_modules(unchecked, &sources, &module_sources)
        .expect("the unspecialized generic evidence Core should validate");

    let groups = reachable_core_nodes(&core, core.root())
        .into_iter()
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) = &core.node(id)?.kind
            else {
                return None;
            };
            group
                .members()
                .iter()
                .any(|member| member.binder().id() == main)
                .then_some(group)
        })
        .collect::<Vec<_>>();
    let [group] = groups.as_slice() else {
        panic!("the actual main binder must own exactly one module group");
    };
    assert!(
        group
            .members()
            .iter()
            .any(|member| member.binder().id() == generic_method)
    );
    assert!(
        group
            .members()
            .iter()
            .any(|member| member.binder().id() == ground_method)
    );
    let main_initializer = group
        .members()
        .iter()
        .find(|member| member.binder().id() == main)
        .unwrap()
        .initializer();
    let entry_source = graph.module(graph.entry()).unwrap().source();
    let expression = "read(Wrap(42))";
    let start = entry_source
        .text()
        .find(expression)
        .expect("the entry expression remains present");
    let expected_span = (
        entry_source.id(),
        u32::try_from(start).unwrap(),
        u32::try_from(start + expression.len()).unwrap(),
    );
    let applications = reachable_core_nodes(&core, main_initializer)
        .into_iter()
        .filter_map(|id| {
            let node = core.node(id)?;
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                application,
            ))) = &node.kind
            else {
                return None;
            };
            let span = node.origin.primary_span();
            ((span.source(), span.range().start(), span.range().end()) == expected_span)
                .then_some((id, application))
        })
        .collect::<Vec<_>>();
    let [(source_application_node, source_application)] = applications.as_slice() else {
        panic!(
            "the exact main initializer must contain one source application at its original span"
        );
    };
    let source_application_node = *source_application_node;
    let evidence_application_node = source_application.function();
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
        evidence_application,
    ))) = &core
        .node(evidence_application_node)
        .expect("the evidence application should exist")
        .kind
    else {
        panic!("the generic method should receive prerequisite evidence");
    };
    let type_application_node = evidence_application.function();
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
        type_application,
    ))) = &core
        .node(type_application_node)
        .expect("the generic method type application should exist")
        .kind
    else {
        panic!("the generic method should be type-applied before evidence");
    };
    let generic_method_node = type_application.function();
    let EffectExprKind::Pure(PureExprKind::Variable(generic_method_variable)) = core
        .node(generic_method_node)
        .expect("the generic method variable should exist")
        .kind
    else {
        panic!("the generic evidence should use the linked implementation-method binder");
    };
    assert_eq!(generic_method_variable.binder(), generic_method);
    let prerequisite_node = evidence_application.argument();
    let EffectExprKind::Pure(PureExprKind::Variable(prerequisite_variable)) = core
        .node(prerequisite_node)
        .expect("the prerequisite method variable should exist")
        .kind
    else {
        panic!("the prerequisite should remain an ordinary method function");
    };
    assert_eq!(prerequisite_variable.binder(), ground_method);

    let evaluation =
        evaluate_effect(&core).expect("the unspecialized generic evidence should evaluate");
    assert_eq!(evaluation.value.to_string(), "42");
    let entered = evaluation
        .trace
        .iter()
        .map(|event| match event {
            TraceEvent::Enter(node) => *node,
        })
        .collect::<Vec<_>>();
    let source_application_index = entered
        .iter()
        .position(|node| *node == source_application_node)
        .expect("evaluation should enter the source application");
    assert_eq!(
        entered.get(source_application_index..source_application_index + 5),
        Some(
            [
                source_application_node,
                evidence_application_node,
                type_application_node,
                generic_method_node,
                prerequisite_node,
            ]
            .as_slice(),
        ),
        "actual trace length {}, max frame depth {}",
        evaluation.trace.len(),
        evaluation.max_frame_depth,
    );
    let prerequisite_index = entered
        .iter()
        .position(|node| *node == prerequisite_node)
        .expect("evaluation should construct prerequisite evidence");
    let source_argument_index = entered
        .iter()
        .position(|node| *node == source_application.argument())
        .expect("evaluation should enter the source value argument");
    assert!(prerequisite_index < source_argument_index);
    // Accepted region startup and once-created stored captures add construction work
    // to the historical Pure profile; these remain whole Source execution bounds.
    assert!(
        evaluation.trace.len() <= 120,
        "actual trace length {}, max frame depth {}",
        evaluation.trace.len(),
        evaluation.max_frame_depth
    );
    assert!(
        evaluation.max_frame_depth <= 16,
        "actual trace length {}, max frame depth {}",
        evaluation.trace.len(),
        evaluation.max_frame_depth
    );
}

#[test]
fn generic_exact_current_self_carries_abstract_prerequisite_evidence() {
    observe_source(
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "interface Score<A> {\nscore : A -> Int\n}\n\n",
            "impl Score<Int> {\nscore value = value\n}\n\n",
            "impl Score<Option<A>> where Score<A> {\n",
            "score None = 4\n",
            "score (Some(value)) = {\n",
            "let empty : Option<A> = None\n",
            "score empty * 10 + score value\n",
            "}\n",
            "}\n\n",
            "main : Unit -> Int\n",
            "main () = score(Some(2))\n",
        ),
        "42",
        Type::Int,
    );
}

#[test]
fn generic_impl_constructor_result_zonks_before_core_alpha_renaming() {
    observe_source(
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Lift<A> {\nlift : A -> Option<A>\n}\n\n",
            "impl Lift<Wrap<A>> {\n",
            "lift value = Some(value)\n",
            "}\n\n",
            "unwrap : Option<Wrap<Int>> -> Int\n",
            "unwrap None = 0\n",
            "unwrap (Some(Wrap(value))) = value\n\n",
            "main : Unit -> Int\n",
            "main () = unwrap(lift(Wrap(42)))\n",
        ),
        "42",
        Type::Int,
    );
}

#[test]
fn module_check_method_occurrence_retains_the_interface_function_kind() {
    check_valid(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Construct<F : Type -> Type> {\n",
        "construct : Int -> F<Int>\n",
        "}\n\n",
        "impl Construct<Option> {\n",
        "construct value = Some(value)\n",
        "}\n\n",
        "main : Unit -> Option<Int>\n",
        "main () = construct 42\n",
    ));
}

#[test]
fn higher_kinded_interface_evidence_evaluates() {
    observe_source(
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "type Wrapped<F : Type -> Type, A> = Wrapped(F<A>)\n\n",
            "interface IntFunctor<F : Type -> Type> {\n",
            "fromInt : Int -> F<Int>\n",
            "}\n\n",
            "interface Extract<A> {\nextract : A -> Int\n}\n\n",
            "impl IntFunctor<Option> {\n",
            "fromInt value = Some(value)\n",
            "}\n\n",
            "impl<F : Type -> Type, A> Extract<Wrapped<F, A>> where IntFunctor<F> {\n",
            "extract (Wrapped(value)) = {\n",
            "let witness : F<Int> = fromInt 0\n",
            "42\n",
            "}\n",
            "}\n\n",
            "main : Unit -> Int\n",
            "main () = extract(Wrapped(Some(0)))\n",
        ),
        "42",
        Type::Int,
    );
}

#[test]
fn higher_kinded_interface_erasure_adds_no_runtime_state_or_transition() {
    fn runtime_classes(
        program: &ValidatedEffectProgram,
        trace: &[TraceEvent],
    ) -> Vec<&'static str> {
        trace
            .iter()
            .map(|event| {
                let TraceEvent::Enter(id) = event;
                match &program
                    .node(*id)
                    .expect("an entered interface Core node should exist")
                    .kind
                {
                    EffectExprKind::Pure(kind) => match kind {
                        PureExprKind::Value(PureValue::String(_)) => "string",
                        PureExprKind::Value(PureValue::Intrinsic(_)) => "intrinsic",
                        PureExprKind::Value(PureValue::Integer(_)) => "integer",
                        PureExprKind::Value(PureValue::Boolean(_)) => "boolean",
                        PureExprKind::Value(PureValue::Unit(_)) => "unit",
                        PureExprKind::Value(PureValue::Function(_)) => "function",
                        PureExprKind::Value(PureValue::Constructor(_)) => "constructor",
                        PureExprKind::Variable(_) => "variable-lookup",
                        PureExprKind::Computation(PureComputation::Bind(_)) => "bind",
                        PureExprKind::Computation(PureComputation::RecursiveBind(_)) => {
                            "recursive-bind"
                        }
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
                    EffectExprKind::Operation(EffectOperation::NativeInterpret(_)) => {
                        "native-interpret"
                    }
                    EffectExprKind::Operation(EffectOperation::Cleanup(_)) => "cleanup",
                    EffectExprKind::Operation(EffectOperation::Registration(_)) => "registration",
                    EffectExprKind::Operation(EffectOperation::Resource(_)) => "resource",
                    EffectExprKind::Operation(EffectOperation::Store(_)) => "store",
                    EffectExprKind::Operation(EffectOperation::Network(_)) => "network",
                    EffectExprKind::Operation(EffectOperation::Continue(_)) => "continue",
                    EffectExprKind::Operation(EffectOperation::RetainedRoot(_)) => "retained-root",
                    EffectExprKind::Operation(EffectOperation::Retain(_)) => "retain",
                    EffectExprKind::Operation(EffectOperation::Region(_)) => "region",
                    EffectExprKind::Operation(EffectOperation::RegionAllocate(_)) => {
                        "region-allocate"
                    }
                    EffectExprKind::Operation(EffectOperation::RegionValueRequest(_)) => {
                        "region-value-request"
                    }
                    EffectExprKind::Operation(EffectOperation::RegionBuffer(_)) => "region-buffer",
                    EffectExprKind::Operation(EffectOperation::RegionTuple(_)) => "region-tuple",
                    EffectExprKind::Operation(EffectOperation::RegionClosure(_)) => {
                        "region-closure"
                    }
                    EffectExprKind::Operation(EffectOperation::Request(_)) => "request",
                    EffectExprKind::Operation(EffectOperation::Handler(_)) => "handler",
                    EffectExprKind::Operation(EffectOperation::Resume(_)) => "resume",
                    EffectExprKind::Operation(EffectOperation::Discard(_)) => "discard",
                }
            })
            .collect()
    }

    fn core_type_operation_shape(program: &ValidatedEffectProgram) -> (usize, usize, usize, bool) {
        let mut visited = std::collections::HashSet::new();
        let mut work = vec![program.root()];
        let mut abstractions = 0;
        let mut applications = 0;
        let mut maximum_argument_count = 0;
        let mut has_arrow_parameter = false;
        while let Some(id) = work.pop() {
            if !visited.insert(id) {
                continue;
            }
            let node = program
                .node(id)
                .expect("a reachable interface Core node should exist");
            match &node.kind {
                EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::TypeAbstraction(operation),
                )) => {
                    abstractions += 1;
                    has_arrow_parameter |= operation
                        .parameters()
                        .iter()
                        .any(|(_, kind)| matches!(kind, Kind::Arrow(_, _)));
                }
                EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::TypeApplication(operation),
                )) => {
                    applications += 1;
                    maximum_argument_count =
                        maximum_argument_count.max(operation.arguments().len());
                }
                _ => {}
            }
            work.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
        }
        (
            abstractions,
            applications,
            maximum_argument_count,
            has_arrow_parameter,
        )
    }

    let first_order = validated_interface_core(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "type Wrapped<A> = Wrapped(A)\n\n",
        "interface Construct<A> {\nconstruct : Int -> A\n}\n\n",
        "interface Extract<A> {\nextract : A -> Int\n}\n\n",
        "impl Construct<Option<Int>> {\n",
        "construct value = Some(value)\n",
        "}\n\n",
        "impl<A> Extract<Wrapped<A>> where Construct<A> {\n",
        "extract (Wrapped(value)) = {\n",
        "let witness : A = construct 0\n",
        "42\n",
        "}\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = extract(Wrapped(Some(0)))\n",
    ));
    let higher_kinded = validated_interface_core(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "type Wrapped<F : Type -> Type, A> = Wrapped(F<A>)\n\n",
        "interface Construct<F : Type -> Type> {\n",
        "construct : Int -> F<Int>\n",
        "}\n\n",
        "interface Extract<A> {\nextract : A -> Int\n}\n\n",
        "impl Construct<Option> {\n",
        "construct value = Some(value)\n",
        "}\n\n",
        "impl<F : Type -> Type, A> Extract<Wrapped<F, A>> where Construct<F> {\n",
        "extract (Wrapped(value)) = {\n",
        "let witness : F<Int> = construct 0\n",
        "42\n",
        "}\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = extract(Wrapped(Some(0)))\n",
    ));
    let first_order_shape = core_type_operation_shape(&first_order);
    let higher_kinded_shape = core_type_operation_shape(&higher_kinded);
    assert!(!first_order_shape.3);
    assert!(higher_kinded_shape.3);
    assert!(higher_kinded_shape.2 > first_order_shape.2);
    assert_eq!(
        (higher_kinded_shape.0, higher_kinded_shape.1),
        (first_order_shape.0, first_order_shape.1),
        "simultaneous higher-kinded arguments must not add Core operation nodes",
    );

    let first_order_evaluation =
        evaluate_effect(&first_order).expect("the first-order interface Core should evaluate");
    let higher_kinded_evaluation =
        evaluate_effect(&higher_kinded).expect("the higher-kinded interface Core should evaluate");
    assert_eq!(first_order_evaluation.value.to_string(), "42");
    assert_eq!(
        higher_kinded_evaluation.value.to_string(),
        first_order_evaluation.value.to_string(),
        "Kinds and interface evidence add no runtime value or interface object",
    );
    assert_eq!(
        higher_kinded_evaluation.max_frame_depth, first_order_evaluation.max_frame_depth,
        "higher-kinded abstraction and application add no evaluator frame",
    );
    let first_order_classes = runtime_classes(&first_order, &first_order_evaluation.trace);
    let higher_kinded_classes = runtime_classes(&higher_kinded, &higher_kinded_evaluation.trace);
    assert_eq!(
        higher_kinded_classes, first_order_classes,
        "higher-kinded evidence adds no lookup or transition beyond the same erased Core shape",
    );
}

#[test]
fn higher_kinded_abstract_interface_evidence_evaluates() {
    observe_source(
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "interface IntFunctor<F : Type -> Type> {\n",
            "fromInt : Int -> F<Int>\n",
            "}\n\n",
            "relay : Option<Int> -> Int where IntFunctor<Option>\n",
            "relay value = {\n",
            "let witness : Option<Int> = fromInt 42\n",
            "42\n",
            "}\n\n",
            "impl IntFunctor<Option> {\n",
            "fromInt value = Some(value)\n",
            "}\n\n",
            "main : Unit -> Int\n",
            "main () = relay(Some(0))\n",
        ),
        "42",
        Type::Int,
    );
}

#[test]
fn generic_current_impl_does_not_freshly_instantiate_its_rigid_head() {
    let error = check_error(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Keep<A> {\nkeep : A -> A\n}\n\n",
        "impl Keep<Option<A>> where Keep<A> {\n",
        "keep value = {\n",
        "let unrelated = keep(Some(1))\n",
        "value\n",
        "}\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "constraint.unsatisfied");
}

#[test]
fn ground_cross_interface_prerequisite_cycle_has_the_exact_reason() {
    let error = check_error(concat!(
        "interface First<A> {\nfirst : A -> A\n}\n\n",
        "interface Second<A> {\nsecond : A -> A\n}\n\n",
        "impl First<Int> where Second<Int> {\nfirst value = value\n}\n\n",
        "impl Second<Int> where First<Int> {\nsecond value = value\n}\n\n",
        "main : Unit -> Int\n",
        "main () = first 1\n",
    ));

    assert_eq!(reason(&error), "constraint.cycle");
}

#[test]
fn determined_ground_cycle_tracks_complete_applications_with_different_dependents() {
    let error = check_error(concat!(
        "interface First<A, B> where A -> B {\nfirst : (A, B) -> Int\n}\n\n",
        "interface Second<A, B> where A -> B {\nsecond : (A, B) -> Int\n}\n\n",
        "impl First<Int, Bool> where Second<Int, Unit> {\nfirst value = 0\n}\n\n",
        "impl Second<Int, Unit> where First<Int, Bool> {\nsecond value = 0\n}\n\n",
        "main : Unit -> Int\n",
        "main () = first((1, true))\n",
    ));

    assert_eq!(reason(&error), "constraint.cycle");
}

#[test]
fn deep_generic_prerequisite_chain_completes_the_pipeline_on_a_small_stack() {
    const DEPTH: usize = 96;
    let worker = std::thread::Builder::new()
        .name("deep-generic-prerequisite-chain".into())
        .stack_size(320 * 1024)
        .spawn(|| {
            let mut nested = "Option<".repeat(DEPTH);
            nested.push_str("Int");
            nested.push_str(&">".repeat(DEPTH));
            let source = format!(
                concat!(
                    "type Option<A> =\nNone\n| Some(A)\n\n",
                    "interface Keep<A> {{\nkeep : A -> A\n}}\n\n",
                    "impl Keep<Int> {{\nkeep value = value\n}}\n\n",
                    "impl Keep<Option<A>> where Keep<A> {{\nkeep value = value\n}}\n\n",
                    "probe : {0} -> {0}\n",
                    "probe value = keep value\n\n",
                    "main : Unit -> Int\n",
                    "main () = 42\n",
                ),
                nested,
            );

            observe_source(&source, "42", Type::Int);
        })
        .expect("the small-stack generic selection worker should start");

    worker
        .join()
        .expect("generic prerequisite selection and destruction should remain iterative");
}
