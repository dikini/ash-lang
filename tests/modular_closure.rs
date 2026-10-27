//! Paired end-to-end evidence for retained integer equality paths.

use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{
        EffectExprKind, EffectOperation, NodeId, Primitive, PureComputation, PureExprKind,
        ValidatedEffectProgram, validate_effect_modules,
    },
    diagnostic::SourceLabel,
    driver::{RunConfiguration, run_path},
    elaborate::{EffectElaborator, TypeError, TypeReason, check_module, link_modules},
    evidence_validation::validate_interface_evidence,
    interface::InterfaceReason,
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{BinderId, CheckedModule},
    source::{SourceFile, Span},
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

const ENTRY_SOURCE: &str = concat!(
    "import equality as Equality\n",
    "import equality (impl Equal)\n\n",
    "main : Unit -> (Bool, Bool, Bool)\n",
    "main () = (\n",
    "41 == 41,\n",
    "Equality.equal(41, 41),\n",
    "Equality.same((41, 41))\n",
    ")\n",
);

const EQUALITY_SOURCE: &str = concat!(
    "pub interface Equal<A> {\n",
    "equal : (A, A) -> Bool\n",
    "}\n\n",
    "pub impl Equal<Int> {\n",
    "equal (left, right) = left == right\n",
    "}\n\n",
    "pub same : (A, A) -> Bool where Equal<A>\n",
    "same pair = equal pair\n",
);

struct ModuleTree(PathBuf);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-modular-closure-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("modular closure fixture should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, source: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be creatable");
        }
        fs::write(&path, source).expect("fixture source should be writable");
        path
    }
}

impl Drop for ModuleTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct PositiveWitness {
    _tree: ModuleTree,
    entry: PathBuf,
    graph: ModuleGraph,
    core: ValidatedEffectProgram,
    implementation_method: BinderId,
    same: BinderId,
    main: BinderId,
}

impl PositiveWitness {
    fn entry(&self) -> &Path {
        &self.entry
    }
}

fn positive_witness() -> PositiveWitness {
    // Arrange: create and load the real two-module source graph.
    let tree = ModuleTree::create();
    let entry = tree.write("entry.ash", ENTRY_SOURCE);
    tree.write("equality.ash", EQUALITY_SOURCE);
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the equality module tree should load");

    // Act: resolve and check each module before linking and validating evidence.
    let checked = check_graph(&graph).expect("the equality module tree should check");
    let equality = checked
        .iter()
        .find(|module| module.module() == module_named(&graph, "equality.ash").id())
        .expect("the equality dependency should remain checked");
    let implementation_method = equality
        .implementation_facts()
        .first()
        .and_then(|implementation| implementation.methods.first())
        .expect("Equal<Int> should retain its method binder")
        .binder;
    let same = binder_named(equality, "same");
    let main = binder_named(
        checked
            .iter()
            .find(|module| module.module() == graph.entry())
            .expect("the entry module should remain checked"),
        "main",
    );
    let linked = link_modules(checked, graph.entry()).expect("the checked graph should link");
    let linked = validate_interface_evidence(linked)
        .expect("the linked interface evidence should authenticate");

    // Act: synthesize ordinary Core and validate it independently for inspection.
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("the Core namespace should reserve");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("validated evidence should synthesize ordinary Core");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the synthesized Core arena should finish");
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
        .expect("the synthesized Core should validate independently");

    PositiveWitness {
        _tree: tree,
        entry,
        graph,
        core,
        implementation_method,
        same,
        main,
    }
}

fn check_graph(graph: &ModuleGraph) -> Result<Vec<CheckedModule>, TypeError> {
    let mut checked = Vec::with_capacity(graph.modules().len());
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked: &&CheckedModule| checked.module() == edge.target())
                    .expect("dependency order should check imported modules first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the dependency summary should authenticate its import edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the equality audit fixture should resolve before checking");
        checked.push(check_module(resolved)?);
    }
    Ok(checked)
}

fn binder_named(module: &CheckedModule, spelling: &str) -> BinderId {
    module
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == spelling)
        .unwrap_or_else(|| panic!("{spelling:?} should remain a checked global"))
        .binder
}

fn module_named<'a>(graph: &'a ModuleGraph, file_name: &str) -> &'a LoadedModule {
    graph
        .modules()
        .iter()
        .find(|module| {
            Path::new(module.source().display_path()).file_name() == Some(file_name.as_ref())
        })
        .unwrap_or_else(|| panic!("{file_name:?} should remain in the loaded graph"))
}

fn exact_span(source: &SourceFile, needle: &str) -> (u32, u32) {
    let start = source
        .text()
        .find(needle)
        .unwrap_or_else(|| panic!("{needle:?} should occur in the fixture source"));
    let end = start + needle.len();
    (
        u32::try_from(start).expect("fixture offset should fit the source model"),
        u32::try_from(end).expect("fixture offset should fit the source model"),
    )
}

fn span_matches(span: Span, source: &SourceFile, needle: &str) -> bool {
    let (start, end) = exact_span(source, needle);
    span.source() == source.id() && span.range().start() == start && span.range().end() == end
}

fn assert_no_label_overlaps(labels: &[SourceLabel], source: &SourceFile, needle: &str) {
    let (start, end) = exact_span(source, needle);
    assert!(labels.iter().all(|label| {
        let span = label.span();
        span.source() != source.id() || span.range().end() <= start || end <= span.range().start()
    }));
}

fn node(program: &ValidatedEffectProgram, id: NodeId) -> &ash::core::EffectExpr {
    program
        .node(id)
        .expect("a retained Core handle should identify its node")
}

fn group_member(group: &ash::core::RecursiveBindingNode, binder: BinderId) -> NodeId {
    group
        .members()
        .iter()
        .find(|member| member.binder().id() == binder)
        .unwrap_or_else(|| panic!("binder {binder:?} should remain in its module group"))
        .initializer()
}

fn find_node(
    program: &ValidatedEffectProgram,
    root: NodeId,
    mut predicate: impl FnMut(&ash::core::EffectExpr) -> bool,
) -> Option<NodeId> {
    let mut pending = vec![root];
    while let Some(id) = pending.pop() {
        let expression = node(program, id);
        if predicate(expression) {
            return Some(id);
        }
        pending.extend(
            (0..expression.kind.child_count())
                .rev()
                .filter_map(|index| expression.kind.child_at(index)),
        );
    }
    None
}

fn pure(program: &ValidatedEffectProgram, id: NodeId) -> &PureExprKind {
    let EffectExprKind::Pure(kind) = &node(program, id).kind else {
        panic!("the selected source operation should remain in the Pure family")
    };
    kind
}

fn equational_body(program: &ValidatedEffectProgram, initializer: NodeId) -> NodeId {
    let body = find_node(program, initializer, |expression| {
        matches!(&expression.kind,
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(group)))
        if node(program, group.scrutinee()).ty == Type::Unit)
    })
    .expect("the main function retains its Unit equation match");
    let PureExprKind::Computation(PureComputation::Match(group)) = pure(program, body) else {
        unreachable!()
    };
    let [arm] = group.arms() else {
        panic!("main retains its one Unit equation")
    };
    arm.body()
}

fn tuple_operands(program: &ValidatedEffectProgram, root: NodeId, types: &[Type]) -> Vec<NodeId> {
    let ty = Type::Tuple(types.to_vec().into_boxed_slice());
    let expression = node(program, root);
    assert_eq!(expression.ty, ty);
    let PureExprKind::Computation(PureComputation::Bind(binding)) = pure(program, root) else {
        panic!("the original tuple retains its selected context binding")
    };
    let tuple = node(program, binding.body());
    assert_eq!(tuple.ty, ty);
    assert!(matches!(
        tuple.kind,
        EffectExprKind::Operation(EffectOperation::RegionTuple(_))
    ));
    assert_eq!(
        tuple.origin.primary_span(),
        expression.origin.primary_span()
    );
    let operands = (0..tuple.kind.child_count())
        .filter_map(|i| tuple.kind.child_at(i))
        .filter(|id| types.contains(&node(program, *id).ty))
        .collect::<Vec<_>>();
    assert_eq!(
        operands
            .iter()
            .map(|id| node(program, *id).ty.clone())
            .collect::<Vec<_>>(),
        types
    );
    operands
}

fn primitive_in_subtree(
    program: &ValidatedEffectProgram,
    root: NodeId,
    primitive: Primitive,
) -> Option<NodeId> {
    let mut pending = vec![root];
    while let Some(id) = pending.pop() {
        let expression = node(program, id);
        if matches!(
            &expression.kind,
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Primitive(operation)))
                if operation.primitive() == primitive
        ) {
            return Some(id);
        }
        pending.extend(
            (0..expression.kind.child_count()).filter_map(|index| expression.kind.child_at(index)),
        );
    }
    None
}

#[test]
fn integer_equality_paths_complete_the_pipeline_with_one_observation() {
    // Arrange.
    let witness = positive_witness();

    // Act: use the public driver while the shared temporary module tree is alive.
    let observation = run_path(RunConfiguration {
        entry: witness.entry().to_path_buf(),
        roots: ModuleRoots::empty(),
    })
    .expect("the public driver should complete the equality module tree");

    // Assert.
    assert_eq!(
        observation.ty(),
        &Type::Tuple(vec![Type::Bool, Type::Bool, Type::Bool].into_boxed_slice())
    );
    assert_eq!(observation.value_display(), "(true, true, true)");
    assert_eq!(observation.type_display(), "(Bool, Bool, Bool)");
}

#[test]
fn direct_and_library_equality_retain_distinct_core_paths() {
    // Arrange and act.
    let witness = positive_witness();
    let core = &witness.core;
    let equality_source = module_named(&witness.graph, "equality.ash").source();
    let entry_source = module_named(&witness.graph, "entry.ash").source();

    // Assert: module binder identity locates the implementation intrinsic.
    let equality_group_id = find_node(core, core.root(), |expression| matches!(&expression.kind,
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(group)))
        if group.members().iter().any(|member| member.binder().id() == witness.implementation_method)))
        .expect("the equality owner retains its exact implementation binder");
    let PureExprKind::Computation(PureComputation::RecursiveBind(equality_group)) =
        pure(core, equality_group_id)
    else {
        unreachable!()
    };
    assert!(
        equality_group
            .members()
            .iter()
            .all(|member| member.binder().id().module()
                == Some(witness.implementation_method.module().unwrap()))
    );
    let implementation_initializer = group_member(equality_group, witness.implementation_method);
    let implementation_equal =
        primitive_in_subtree(core, implementation_initializer, Primitive::Equal)
            .expect("the Equal<Int> method should retain integer equality");
    assert!(span_matches(
        node(core, implementation_equal).origin.primary_span(),
        equality_source,
        "left == right"
    ));

    // Assert: source tuple position and origin identify the direct intrinsic.
    let entry_group_id = equality_group.body();
    let PureExprKind::Computation(PureComputation::RecursiveBind(entry_group)) =
        pure(core, entry_group_id)
    else {
        panic!("the entry recursive group must directly follow its equality dependency")
    };
    assert_eq!(entry_group.members().len(), 1);
    assert_eq!(entry_group.members()[0].binder().id(), witness.main);
    let main_body = equational_body(core, group_member(entry_group, witness.main));
    let results = tuple_operands(core, main_body, &[Type::Bool, Type::Bool, Type::Bool]);
    let [direct, method, constrained] = results.as_slice() else {
        panic!("main should retain the three source tuple elements");
    };
    let PureExprKind::Computation(PureComputation::Primitive(direct_equal)) = pure(core, *direct)
    else {
        panic!("direct source equality should remain a Core primitive");
    };
    assert_eq!(direct_equal.primitive(), Primitive::Equal);
    assert!(span_matches(
        node(core, *direct).origin.primary_span(),
        entry_source,
        "41 == 41"
    ));

    // Assert: the imported method is an ordinary value application.
    let PureExprKind::Computation(PureComputation::Apply(method_call)) = pure(core, *method) else {
        panic!("the explicit method call should lower to ordinary application");
    };
    let PureExprKind::Variable(method_function) = *pure(core, method_call.function()) else {
        panic!("the selected method should lower to its implementation binder");
    };
    assert_eq!(method_function.binder(), witness.implementation_method);
    assert_eq!(
        tuple_operands(core, method_call.argument(), &[Type::Int, Type::Int]).len(),
        2
    );

    // Assert: the constrained global uses ordinary type, evidence, and value applications.
    let PureExprKind::Computation(PureComputation::Apply(value_application)) =
        pure(core, *constrained)
    else {
        panic!("the constrained call should retain its source-value application");
    };
    let PureExprKind::Computation(PureComputation::Apply(evidence_application)) =
        pure(core, value_application.function())
    else {
        panic!("the constrained call should apply evidence before its source value");
    };
    let PureExprKind::Computation(PureComputation::TypeApplication(type_application)) =
        pure(core, evidence_application.function())
    else {
        panic!("the constrained call should instantiate its ordinary global scheme");
    };
    assert_eq!(type_application.arguments(), &[Type::Int]);
    let PureExprKind::Variable(same_function) = *pure(core, type_application.function()) else {
        panic!("the type application should expose the ordinary same binder");
    };
    assert_eq!(same_function.binder(), witness.same);
    let PureExprKind::Variable(evidence_method) = *pure(core, evidence_application.argument())
    else {
        panic!("the evidence argument should be the implementation method binder");
    };
    assert_eq!(evidence_method.binder(), witness.implementation_method);
    assert_eq!(
        tuple_operands(core, value_application.argument(), &[Type::Int, Type::Int]).len(),
        2
    );
}

#[test]
fn direct_boolean_equality_keeps_the_operator_operand_diagnostic() {
    // Arrange.
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        "main : Unit -> Bool\nmain () = true == false\n",
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the direct negative fixture should load");

    // Act.
    let error = check_graph(&graph).expect_err("Boolean source equality should be rejected");
    let TypeError::Source(diagnostic) = error else {
        panic!("Boolean source equality should retain a source type diagnostic");
    };
    let source = module_named(&graph, "entry.ash").source();

    // Assert.
    assert_eq!(diagnostic.reason, TypeReason::OperatorOperand);
    assert_eq!(diagnostic.reason.to_string(), "type.operator-operand");
    assert!(span_matches(diagnostic.primary.span(), source, "true"));
    assert_eq!(diagnostic.primary.message(), "this operand is not an Int");
    assert_eq!(diagnostic.related.len(), 1);
    assert!(span_matches(diagnostic.related[0].span(), source, "=="));
    assert_eq!(
        diagnostic.related[0].message(),
        "this primitive operator requires Int operands"
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
    assert!(diagnostic.help.is_none());
}

#[test]
fn imported_boolean_method_keeps_the_unsatisfied_interface_diagnostic() {
    // Arrange.
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import equality as Equality\n\n",
            "main : Unit -> Bool\n",
            "main () = Equality.equal(true, false)\n",
        ),
    );
    tree.write("equality.ash", EQUALITY_SOURCE);
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the imported negative fixture should load");

    // Act.
    let error = check_graph(&graph)
        .expect_err("the dependency exports no available Equal<Bool> implementation");
    let TypeError::Interface(diagnostic) = error else {
        panic!("the imported method should retain an interface diagnostic");
    };
    let entry_source = module_named(&graph, "entry.ash").source();
    let equality_source = module_named(&graph, "equality.ash").source();

    // Assert.
    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert_eq!(diagnostic.reason.to_string(), "constraint.unsatisfied");
    assert!(span_matches(
        diagnostic.primary.span(),
        entry_source,
        "Equality.equal"
    ));
    assert_eq!(
        diagnostic.primary.message(),
        "no available implementation satisfies this interface obligation"
    );
    assert_eq!(diagnostic.related.len(), 3);
    assert!(span_matches(
        diagnostic.related[0].span(),
        equality_source,
        "equal : (A, A) -> Bool"
    ));
    assert_eq!(
        diagnostic.related[0].message(),
        "this declaration introduced the interface obligation"
    );
    assert!(span_matches(
        diagnostic.related[1].span(),
        entry_source,
        "import equality as Equality"
    ));
    assert_eq!(
        diagnostic.related[1].message(),
        "this import made the declaration available"
    );
    assert!(span_matches(
        diagnostic.related[2].span(),
        equality_source,
        "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}"
    ));
    assert_eq!(
        diagnostic.related[2].message(),
        "this interface declaration participates in the failing selection"
    );
    assert_no_label_overlaps(
        &diagnostic.related,
        equality_source,
        "pub impl Equal<Int> {\nequal (left, right) = left == right\n}",
    );
    assert!(diagnostic.expected.is_none());
    assert!(diagnostic.found.is_none());
    assert!(diagnostic.help.is_none());
}
