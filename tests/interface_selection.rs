//! Integration fixtures for Task 5 checked interface-evidence selection.
//!
//! The traversal starts at a [`CheckedDefinition`] and follows its owned
//! expression structure to the occurrence's own evidence slot.  No test joins
//! detached selections to source spans.

use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{
        ElaborationFailure, Elaborator, TypeContext, TypeError, check_module, link_modules,
    },
    evidence_validation::validate_interface_evidence,
    interface::{EvidenceNode, ImplId, ImplMethodId, InterfaceId, MethodId, RequirementId},
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{
        CheckedDefinition, CheckedImplementationBody, CheckedModule, ImplementationRoute,
        ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind, ResolvedLocalDeclaration,
        ResolvedOccurrence, ResolvedTermName,
    },
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct SelectionFixture(PathBuf);

impl SelectionFixture {
    fn create(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir().join(format!(
                "ash-interface-selection-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let entry = directory.join("entry.ash");
                    fs::write(&entry, text).expect("selection fixture should be writable");
                    return Self(entry);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("selection fixture directory should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) {
        let path = self
            .0
            .parent()
            .expect("selection fixture entry should have a parent")
            .join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("selection fixture parent should be creatable");
        }
        fs::write(path, text).expect("selection fixture dependency should be writable");
    }
}

#[test]
fn imported_implementation_route_retains_its_exact_direct_dependency_identity() {
    let fixture = SelectionFixture::create(concat!(
        "import dependency as Dependency\n",
        "import dependency (impl Render)\n",
        "main : Unit -> Int\n",
        "main () = Dependency.render(42)\n",
    ));
    fixture.write(
        "dependency.ash",
        concat!(
            "pub interface Render<A> {\nrender : A -> Int\n}\n\n",
            "pub impl Render<Int> {\nrender value = value\n}\n",
        ),
    );
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("selection fixture graph should load");
    let checked = check_graph(&graph).expect("the imported concrete implementation should check");
    let entry = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .expect("the checked graph should retain its entry module");
    let loaded_entry = graph
        .module(graph.entry())
        .expect("the loaded graph should retain its entry module");
    let [qualified_edge, selector_edge] = loaded_entry.dependencies() else {
        panic!("the entry should retain its name and implementation dependency edges");
    };
    let [available] = entry.available_implementations() else {
        panic!("the entry should retain exactly one available implementation");
    };
    let [qualified_dependency, selector_dependency] = entry.direct_dependencies() else {
        panic!("the checked entry should retain both authenticated direct edges");
    };
    assert_eq!(qualified_dependency.target(), qualified_edge.target());
    assert_eq!(
        qualified_dependency.import_span(),
        qualified_edge.import_span()
    );
    assert_eq!(selector_dependency.target(), selector_edge.target());
    assert_eq!(
        selector_dependency.import_span(),
        selector_edge.import_span()
    );
    assert_eq!(available.id(), ImplId::new(selector_edge.target(), 0),);
    assert_eq!(
        available.route(),
        ImplementationRoute::DirectImport {
            direct_dependency: selector_edge.target(),
            available_at: selector_edge.import_span(),
        },
    );
}

impl Drop for SelectionFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn check(text: &str) -> Result<CheckedModule, TypeError> {
    let fixture = SelectionFixture::create(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("selection fixture should load");
    let loaded = graph
        .module(graph.entry())
        .expect("selection fixture entry should remain admitted");
    let resolved = resolve_module(loaded, &[]).expect("selection fixture should resolve");
    check_module(resolved)
}

fn check_graph(graph: &ModuleGraph) -> Result<Vec<CheckedModule>, TypeError> {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|module: &&CheckedModule| module.module() == edge.target())
                    .expect("dependency order should check imported modules first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("checked dependency summary should authenticate its import edge")
            })
            .collect::<Vec<_>>();
        let resolved =
            resolve_module(module, &dependencies).expect("selection fixture module should resolve");
        checked.push(check_module(resolved)?);
    }
    Ok(checked)
}

fn interface_reason(error: TypeError) -> String {
    let TypeError::Interface(diagnostic) = error else {
        panic!("expected an interface constraint diagnostic, found {error:?}");
    };
    diagnostic.reason.to_string()
}

fn diagnostic_reason(error: TypeError) -> String {
    match error {
        TypeError::Interface(diagnostic) => diagnostic.reason.to_string(),
        TypeError::Source(diagnostic) => diagnostic.reason.to_string(),
        TypeError::Mismatch(_) | TypeError::Internal(_) => {
            panic!("expected a categorized source diagnostic, found {error:?}")
        }
    }
}

fn checked_definition<'a>(checked: &'a CheckedModule, spelling: &str) -> &'a CheckedDefinition {
    checked
        .definitions()
        .iter()
        .find(|definition| match definition.kind() {
            ResolvedDefinitionKind::Equational(global) => {
                global.interface.name.spelling == spelling
            }
            ResolvedDefinitionKind::InlineOperational(global) => {
                global.header.name.spelling == spelling
            }
        })
        .unwrap_or_else(|| panic!("checked definition {spelling:?} should be retained"))
}

fn occurrence_selections(
    definition: &CheckedDefinition,
    term: ResolvedTermName,
) -> Vec<&ResolvedOccurrence> {
    let mut expressions = Vec::new();
    match definition.kind() {
        ResolvedDefinitionKind::Equational(global) => {
            expressions.extend(global.equations.iter().map(|equation| &equation.body));
        }
        ResolvedDefinitionKind::InlineOperational(global) => {
            expressions.push(global.body.result.as_ref());
            for declaration in &global.body.declarations {
                schedule_local_declaration(declaration, &mut expressions);
            }
        }
    }

    occurrences_in_expressions(expressions, term)
}

fn implementation_occurrence_selections(
    implementation: &CheckedImplementationBody,
    term: ResolvedTermName,
) -> Vec<&ResolvedOccurrence> {
    let expressions = implementation
        .method_groups()
        .iter()
        .flat_map(|group| group.equations.iter().map(|equation| &equation.body))
        .collect();
    occurrences_in_expressions(expressions, term)
}

fn occurrences_in_expressions(
    mut expressions: Vec<&ResolvedExpr>,
    term: ResolvedTermName,
) -> Vec<&ResolvedOccurrence> {
    let mut occurrences = Vec::new();
    while let Some(expression) = expressions.pop() {
        match &expression.kind {
            ResolvedExprKind::Occurrence(occurrence) => {
                if occurrence.term == term {
                    occurrences.push(occurrence);
                }
            }
            ResolvedExprKind::Integer(_)
            | ResolvedExprKind::Boolean(_)
            | ResolvedExprKind::Unit
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
                    schedule_local_declaration(declaration, &mut expressions);
                }
            }
            ResolvedExprKind::Function(function) => {
                expressions.push(function.body.result.as_ref());
                for declaration in &function.body.declarations {
                    schedule_local_declaration(declaration, &mut expressions);
                }
            }
            ResolvedExprKind::Match(matched) => {
                expressions.push(matched.scrutinee.as_ref());
                expressions.extend(matched.arms.iter().map(|arm| &arm.body));
            }
        }
    }
    occurrences
}

fn schedule_local_declaration<'a>(
    declaration: &'a ResolvedLocalDeclaration,
    expressions: &mut Vec<&'a ResolvedExpr>,
) {
    match declaration {
        ResolvedLocalDeclaration::Binding(binding) => expressions.push(&binding.initializer),
        ResolvedLocalDeclaration::Recursive(group) => {
            expressions.extend(group.members.iter().map(|member| &member.initializer));
        }
    }
}

fn selection_for_occurrence(occurrence: &ResolvedOccurrence) -> &ash::interface::EvidenceSelection {
    let [slot] = occurrence.evidence.as_ref() else {
        panic!("a constrained occurrence should retain one structural evidence slot");
    };
    slot.selection()
        .expect("checking should fill the occurrence's own evidence slot")
}

fn assert_abstract_selection(
    occurrence: &ResolvedOccurrence,
    requirement: RequirementId,
    methods: &[MethodId],
    argument: &Type,
) {
    let selection = selection_for_occurrence(occurrence);
    assert_eq!(selection.interface(), methods[0].interface());
    assert_eq!(selection.argument(), argument);
    assert_eq!(selection.node_count(), 1);
    assert_eq!(
        selection.node(selection.root()),
        Some(EvidenceNode::Abstract {
            requirement,
            methods,
        })
    );
}

#[test]
fn constrained_method_selects_its_exact_abstract_requirement_before_a_matching_impl() {
    let checked = check(concat!(
        "interface Convert<A> {\nconvert : A -> A\n}\n\n",
        "impl Convert<Int> {\nconvert value = value\n}\n\n",
        "use_abstract : Int -> Int where Convert<Int>\n",
        "use_abstract value = convert value\n",
    ))
    .expect("the constrained method body should check using its declared evidence");

    let scheme = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "use_abstract")
        .expect("the constrained global scheme should remain checked");
    let [requirement] = scheme.scheme.requirements.as_ref() else {
        panic!("the constrained global should retain its one requirement");
    };
    let method = MethodId::new(InterfaceId::new(checked.module(), 0), 0);
    let occurrences = occurrence_selections(
        checked_definition(&checked, "use_abstract"),
        ResolvedTermName::Method(method),
    );
    let [occurrence] = occurrences.as_slice() else {
        panic!("the body should retain exactly one Convert.convert occurrence");
    };
    assert!(
        !checked.available_implementations().is_empty(),
        "the matching implementation must be available so abstract selection proves precedence"
    );
    assert_abstract_selection(occurrence, requirement.id, &[method], &Type::Int);
}

#[test]
fn higher_kinded_abstract_requirement_wins_before_a_matching_concrete_candidate() {
    let checked = check(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Construct<F : Type -> Type> {\n",
        "construct : Int -> F<Int>\n",
        "}\n\n",
        "impl Construct<Option> {\n",
        "construct value = Some(value)\n",
        "}\n\n",
        "relay : Option<Int> -> Option<Int> where Construct<Option>\n",
        "relay value = construct 42\n",
    ))
    .expect("the higher-kinded abstract requirement should satisfy the method occurrence");

    let scheme = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "relay")
        .expect("the constrained relay scheme should remain checked");
    let [requirement] = scheme.scheme.requirements.as_ref() else {
        panic!("the relay scheme should retain its higher-kinded requirement");
    };
    let method = MethodId::new(InterfaceId::new(checked.module(), 0), 0);
    let occurrences = occurrence_selections(
        checked_definition(&checked, "relay"),
        ResolvedTermName::Method(method),
    );
    let [occurrence] = occurrences.as_slice() else {
        panic!("the relay body should retain exactly one Construct.construct occurrence");
    };
    assert!(
        !checked.available_implementations().is_empty(),
        "the concrete Construct<Option> candidate must be available"
    );
    assert_abstract_selection(
        occurrence,
        requirement.id,
        &[method],
        requirement.argument(),
    );
}

#[test]
fn constrained_global_occurrence_retains_one_abstract_selection_per_requirement_in_source_order() {
    let checked = check(concat!(
        "interface Left<A> {\nleft : A -> A\n}\n\n",
        "interface Right<A> {\nright : A -> A\n}\n\n",
        "source : A -> A where Left<A>, Right<A>\n",
        "source value = right (left value)\n\n",
        "consumer : Int -> Int where Left<Int>, Right<Int>\n",
        "consumer value = source value\n",
    ))
    .expect("the constrained global call should reuse both caller requirements");

    let source = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "source")
        .expect("the called constrained scheme should be retained");
    let consumer = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "consumer")
        .expect("the caller constrained scheme should be retained");
    let [left_requirement, right_requirement] = consumer.scheme.requirements.as_ref() else {
        panic!("the caller should retain both requirements in source order");
    };
    let occurrences = occurrence_selections(
        checked_definition(&checked, "consumer"),
        ResolvedTermName::Global(source.binder),
    );
    let [occurrence] = occurrences.as_slice() else {
        panic!("the caller should retain one source occurrence");
    };
    let [left_slot, right_slot] = occurrence.evidence.as_ref() else {
        panic!("the constrained occurrence should own two ordered evidence slots");
    };
    let left = left_slot
        .selection()
        .expect("the first requirement slot should be selected");
    let right = right_slot
        .selection()
        .expect("the second requirement slot should be selected");
    let left_method = MethodId::new(InterfaceId::new(checked.module(), 0), 0);
    let right_method = MethodId::new(InterfaceId::new(checked.module(), 1), 0);
    assert_eq!(
        left.node(left.root()),
        Some(EvidenceNode::Abstract {
            requirement: left_requirement.id,
            methods: &[left_method],
        })
    );
    assert_eq!(
        right.node(right.root()),
        Some(EvidenceNode::Abstract {
            requirement: right_requirement.id,
            methods: &[right_method],
        })
    );
}

#[test]
fn concrete_candidate_retains_impl_substitution_prerequisite_and_ordered_method_identity() {
    let checked = check(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Equal<A> {\nequal : (A, A) -> Bool\nidentity : A -> A\n}\n\n",
        "interface Show<A> {\nshow : A -> Int\n}\n\n",
        "impl Equal<Int> {\nequal pair = true\nidentity value = value\n}\n\n",
        "impl Show<Int> {\nshow value = 0\n}\n\n",
        "impl Equal<Option<A>> where Equal<A>, Show<A> {\n",
        "equal pair = false\nidentity value = value\n}\n\n",
        "compare : (Option<Int>, Option<Int>) -> Bool\n",
        "compare pair = equal pair\n",
    ))
    .expect("the concrete method body should select the generic implementation");

    let interface = InterfaceId::new(checked.module(), 0);
    let implementation = ImplId::new(checked.module(), 2);
    let method = MethodId::new(interface, 0);
    let identity = MethodId::new(interface, 1);
    let show = MethodId::new(InterfaceId::new(checked.module(), 1), 0);
    let [head_parameter] = checked.implementation_facts()[2].head_parameters.as_ref() else {
        panic!("the generic implementation should retain one head parameter");
    };
    let occurrences = occurrence_selections(
        checked_definition(&checked, "compare"),
        ResolvedTermName::Method(method),
    );
    let [occurrence] = occurrences.as_slice() else {
        panic!("the body should retain exactly one Equal.equal occurrence");
    };
    let selection = selection_for_occurrence(occurrence);
    assert_eq!(selection.node_count(), 3);
    let EvidenceNode::Implementation {
        implementation: actual_implementation,
        substitution,
        prerequisites,
        methods,
    } = selection
        .node(selection.root())
        .expect("the concrete selection should retain its root node")
    else {
        panic!("the concrete occurrence should select an implementation");
    };
    assert_eq!(actual_implementation, implementation);
    let [substitution] = substitution else {
        panic!("the generic implementation should retain its one substitution");
    };
    assert_eq!(substitution.parameter(), head_parameter.id);
    assert_eq!(substitution.argument(), &Type::Int);
    let [equal_prerequisite, show_prerequisite] = prerequisites else {
        panic!("the generic implementation should retain both prerequisites in source order");
    };
    assert_eq!(
        methods,
        &[
            ImplMethodId::new(implementation, method),
            ImplMethodId::new(implementation, identity),
        ]
    );

    let EvidenceNode::Implementation {
        implementation: prerequisite_implementation,
        substitution: prerequisite_substitution,
        prerequisites: nested_prerequisites,
        methods: prerequisite_methods,
    } = selection
        .node(*equal_prerequisite)
        .expect("the first prerequisite selection node should be retained")
    else {
        panic!("the first prerequisite should select Equal<Int>");
    };
    assert_eq!(
        prerequisite_implementation,
        ImplId::new(checked.module(), 0)
    );
    assert!(prerequisite_substitution.is_empty());
    assert!(nested_prerequisites.is_empty());
    assert_eq!(
        prerequisite_methods,
        &[
            ImplMethodId::new(ImplId::new(checked.module(), 0), method),
            ImplMethodId::new(ImplId::new(checked.module(), 0), identity),
        ]
    );

    let EvidenceNode::Implementation {
        implementation: show_implementation,
        substitution: show_substitution,
        prerequisites: show_nested_prerequisites,
        methods: show_methods,
    } = selection
        .node(*show_prerequisite)
        .expect("the second prerequisite selection node should be retained")
    else {
        panic!("the second prerequisite should select Show<Int>");
    };
    assert_eq!(show_implementation, ImplId::new(checked.module(), 1));
    assert!(show_substitution.is_empty());
    assert!(show_nested_prerequisites.is_empty());
    assert_eq!(
        show_methods,
        &[ImplMethodId::new(ImplId::new(checked.module(), 1), show)]
    );
}

#[test]
fn higher_kinded_concrete_candidate_retains_ordered_substitution_and_evidence() {
    let checked = check(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "type Wrapped<F : Type -> Type, A> = Wrapped(F<A>)\n\n",
        "interface Construct<F : Type -> Type> {\n",
        "construct : Int -> F<Int>\n",
        "}\n\n",
        "interface Show<A> {\nshow : A -> Int\n}\n\n",
        "interface Extract<A> {\nextract : A -> Int\nretain : A -> A\n}\n\n",
        "impl Construct<Option> {\nconstruct value = Some(value)\n}\n\n",
        "impl Show<Int> {\nshow value = value\n}\n\n",
        "impl<F : Type -> Type, A : Type> Extract<Wrapped<F, A>> ",
        "where Construct<F>, Show<A> {\n",
        "extract value = 0\n",
        "retain value = value\n",
        "}\n\n",
        "probe : Wrapped<Option, Int> -> Int\n",
        "probe value = extract value\n",
    ))
    .expect("the higher-kinded concrete candidate should satisfy the occurrence");

    let construct_interface = InterfaceId::new(checked.module(), 0);
    let show_interface = InterfaceId::new(checked.module(), 1);
    let extract_interface = InterfaceId::new(checked.module(), 2);
    let construct = MethodId::new(construct_interface, 0);
    let show = MethodId::new(show_interface, 0);
    let extract = MethodId::new(extract_interface, 0);
    let retain = MethodId::new(extract_interface, 1);
    let construct_implementation = ImplId::new(checked.module(), 0);
    let show_implementation = ImplId::new(checked.module(), 1);
    let extract_implementation = ImplId::new(checked.module(), 2);
    let [function_parameter, argument_parameter] =
        checked.implementation_facts()[2].head_parameters.as_ref()
    else {
        panic!("the generic implementation should retain F then A");
    };
    let occurrences = occurrence_selections(
        checked_definition(&checked, "probe"),
        ResolvedTermName::Method(extract),
    );
    let [occurrence] = occurrences.as_slice() else {
        panic!("the probe should retain exactly one Extract.extract occurrence");
    };
    let selection = selection_for_occurrence(occurrence);
    assert_eq!(selection.node_count(), 3);
    let EvidenceNode::Implementation {
        implementation,
        substitution,
        prerequisites,
        methods,
    } = selection
        .node(selection.root())
        .expect("the concrete selection should retain its root")
    else {
        panic!("the higher-kinded occurrence should select an implementation");
    };

    assert_eq!(implementation, extract_implementation);
    let [function_substitution, argument_substitution] = substitution else {
        panic!("the generic implementation should retain F then A substitutions");
    };
    assert_eq!(function_substitution.parameter(), function_parameter.id);
    assert_eq!(
        function_substitution.argument(),
        checked.implementation_facts()[0].argument(),
        "F should match the bare Option constructor"
    );
    assert_eq!(argument_substitution.parameter(), argument_parameter.id);
    assert_eq!(argument_substitution.argument(), &Type::Int);
    assert_eq!(
        methods,
        &[
            ImplMethodId::new(extract_implementation, extract),
            ImplMethodId::new(extract_implementation, retain),
        ]
    );

    let [construct_prerequisite, show_prerequisite] = prerequisites else {
        panic!("the selected implementation should retain Construct then Show evidence");
    };
    assert_eq!(
        selection.node(*construct_prerequisite),
        Some(EvidenceNode::Implementation {
            implementation: construct_implementation,
            substitution: &[],
            prerequisites: &[],
            methods: &[ImplMethodId::new(construct_implementation, construct)],
        })
    );
    assert_eq!(
        selection.node(*show_prerequisite),
        Some(EvidenceNode::Implementation {
            implementation: show_implementation,
            substitution: &[],
            prerequisites: &[],
            methods: &[ImplMethodId::new(show_implementation, show)],
        })
    );
}

#[test]
fn polymorphic_implementation_method_selects_exact_current_impl_and_retains_ordered_prerequisites()
{
    let checked = check(concat!(
        "interface First<A> {\nfirst : A -> A\n}\n\n",
        "interface Second<A> {\nsecond : A -> A\n}\n\n",
        "interface Repeat<A> {\nrepeat<Item> : (A, Item) -> A\n}\n\n",
        "impl Repeat<Int> where First<Int>, Second<Int> {\n",
        "repeat (value, item) = repeat((value, item))\n",
        "}\n",
    ))
    .expect("the implementation method should use its exact current implementation evidence");

    let implementation = ImplId::new(checked.module(), 0);
    let repeat = MethodId::new(InterfaceId::new(checked.module(), 2), 0);
    let first = MethodId::new(InterfaceId::new(checked.module(), 0), 0);
    let second = MethodId::new(InterfaceId::new(checked.module(), 1), 0);
    let [first_requirement, second_requirement] =
        checked.implementation_facts()[0].prerequisites.as_ref()
    else {
        panic!("the current implementation should retain its ordered prerequisites");
    };
    let [method_parameter] = checked.interface_facts()[2].methods[0].type_parameters() else {
        panic!("the polymorphic method should retain one rigid local parameter");
    };
    let occurrences = implementation_occurrence_selections(
        &checked.implementations()[0],
        ResolvedTermName::Method(repeat),
    );
    let [occurrence] = occurrences.as_slice() else {
        panic!("the implementation method should retain one recursive Repeat.repeat occurrence");
    };
    let selection = selection_for_occurrence(occurrence);
    let EvidenceNode::Implementation {
        implementation: actual_implementation,
        substitution,
        prerequisites,
        methods,
    } = selection
        .node(selection.root())
        .expect("the exact current implementation selection should retain its root")
    else {
        panic!("the recursive method occurrence should select its current implementation");
    };
    assert_eq!(actual_implementation, implementation);
    assert_eq!(selection.argument(), &Type::Int);
    assert_eq!(
        occurrence.evidence[0].method_arguments(),
        &[Type::Variable(method_parameter.id)]
    );
    assert!(substitution.is_empty());
    assert_eq!(methods, &[ImplMethodId::new(implementation, repeat)]);
    let [first_prerequisite, second_prerequisite] = prerequisites else {
        panic!(
            "current implementation evidence should retain both prerequisites in declaration order"
        );
    };
    assert_eq!(
        selection.node(*first_prerequisite),
        Some(EvidenceNode::Abstract {
            requirement: first_requirement.id,
            methods: &[first],
        })
    );
    assert_eq!(
        selection.node(*second_prerequisite),
        Some(EvidenceNode::Abstract {
            requirement: second_requirement.id,
            methods: &[second],
        })
    );
}

#[test]
fn link_modules_retains_the_checked_occurrences_evidence_selection() {
    let fixture = SelectionFixture::create(concat!(
        "import dependency as Dependency\n",
        "import dependency (impl Render)\n",
        "main : Unit -> Int\n",
        "main () = Dependency.render(42)\n",
    ));
    fixture.write(
        "dependency.ash",
        concat!(
            "pub interface Render<A> {\nrender : A -> Int\n}\n\n",
            "pub impl Render<Int> {\nrender value = value\n}\n",
        ),
    );
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("selection fixture graph should load");
    let checked = check_graph(&graph).expect("the imported concrete implementation should check");
    let entry = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .expect("the checked graph should retain its entry module");
    let dependency = graph
        .modules()
        .iter()
        .find(|module| {
            Path::new(module.source().display_path()).file_name() == Some("dependency.ash".as_ref())
        })
        .expect("the fixture graph should retain the dependency module");
    let render = MethodId::new(InterfaceId::new(dependency.id(), 0), 0);
    let occurrence = occurrence_selections(
        checked_definition(entry, "main"),
        ResolvedTermName::Method(render),
    )
    .pop()
    .expect("the entry definition should retain its imported Render.render occurrence");
    let before_link = selection_for_occurrence(occurrence).clone();
    let linked = link_modules(checked, graph.entry())
        .expect("checked modules should link without reselection");
    let linked = validate_interface_evidence(linked)
        .expect("linked checked evidence should authenticate without reselection");
    let mut final_elaborator = Elaborator::for_module_program(&linked)
        .expect("the linked checked namespace should reserve");
    assert_eq!(
        final_elaborator.synthesize(linked.result(), &TypeContext::new()),
        Err(TypeError::Internal(ElaborationFailure::InvalidState)),
        "final synthesis must not admit the public raw-expression path",
    );
    let entry_group = linked
        .groups()
        .iter()
        .find(|group| group.module() == graph.entry())
        .expect("the linked program should retain its entry checked group");
    let linked_occurrence = occurrence_selections(
        entry_group
            .definitions()
            .iter()
            .find(|definition| match definition.kind() {
                ResolvedDefinitionKind::Equational(global) => {
                    global.interface.name.spelling == "main"
                }
                ResolvedDefinitionKind::InlineOperational(global) => {
                    global.header.name.spelling == "main"
                }
            })
            .expect("the linked entry group should retain main's checked definition"),
        ResolvedTermName::Method(render),
    )
    .pop()
    .expect("the linked definition should retain its same Render.render occurrence");
    let after_link = selection_for_occurrence(linked_occurrence);

    assert_eq!(before_link.root(), after_link.root());
    assert!(
        before_link.shares_plan_with(after_link),
        "linking must move the occurrence-owned selection into the checked group"
    );
}

#[test]
fn absent_candidate_reports_constraint_unsatisfied() {
    let error = check(concat!(
        "interface Render<A> {\nrender : A -> Int\n}\n\n",
        "render_bool : Bool -> Int\nrender_bool value = render value\n",
    ))
    .expect_err("an unavailable interface implementation should reject the method occurrence");

    assert_eq!(interface_reason(error), "constraint.unsatisfied");
}

#[test]
fn rejects_public_global_obligation_instead_of_inferring_exported_requirement() {
    let error = check(concat!(
        "pub interface Render<A> {\nrender : A -> Int\n}\n\n",
        "pub render_bool : Bool -> Int\nrender_bool value = render value\n",
    ))
    .expect_err("a public global must not infer a missing exported requirement from its body");

    assert_eq!(interface_reason(error), "constraint.unsatisfied");
}

#[test]
fn undetermined_obligation_reports_constraint_ambiguous_without_type_guessing() {
    let error = check(concat!(
        "interface Render<A> {\nrender : A -> Int\n}\n\n",
        "impl Render<Int> {\nrender value = value\n}\n\n",
        "probe : Unit -> Unit\n",
        "probe () = {\nlet use = fn(value) {\nrender value\n}\n()\n}\n",
    ))
    .expect_err("an undetermined local obligation should not choose an implementation by guessing");

    assert_eq!(interface_reason(error), "constraint.ambiguous");
}

#[test]
fn polymorphic_method_with_unresolved_interface_argument_remains_constraint_ambiguous() {
    let error = check(concat!(
        "interface Make<I> {\nmake<A> : A -> I\n}\n\n",
        "probe : Unit -> Unit\n",
        "probe () = {\nlet _ = make(42)\n()\n}\n",
    ))
    .expect_err("an unresolved interface argument must own constraint ambiguity");

    assert_eq!(interface_reason(error), "constraint.ambiguous");
}

#[test]
fn polymorphic_method_occurrence_does_not_add_higher_order_matching() {
    let error = check(concat!(
        "interface Keep<I> {\n",
        "keep<F : Type -> Type, A> : (I, F<A>) -> I\n",
        "}\n\n",
        "probe : Int -> Int where Keep<Int>\n",
        "probe value = keep((value, value))\n",
    ))
    .expect_err("matching F<A> with Int would require a type lambda");

    assert_eq!(diagnostic_reason(error), "type.argument");
}

#[test]
fn direct_recursive_polymorphic_method_reuses_rigid_arguments() {
    let checked = check(concat!(
        "interface Repeat<I> {\nrepeat<A> : (I, A) -> A\n}\n\n",
        "impl Repeat<Int> {\n",
        "repeat (owner, value) = repeat((owner, value))\n",
        "}\n\n",
        "outside : Int -> Bool\n",
        "outside owner = repeat((owner, true))\n",
    ))
    .expect("direct recursion should reuse its rigid local method argument");
    let repeat = MethodId::new(InterfaceId::new(checked.module(), 0), 0);
    let [interface] = checked.interface_facts() else {
        panic!("the module should retain one interface");
    };
    let [method] = interface.methods.as_ref() else {
        panic!("the interface should retain one method");
    };
    let [method_parameter] = method.type_parameters() else {
        panic!("the method should retain one local type parameter");
    };
    let recursive = implementation_occurrence_selections(
        &checked.implementations()[0],
        ResolvedTermName::Method(repeat),
    );
    let outside = occurrence_selections(
        checked_definition(&checked, "outside"),
        ResolvedTermName::Method(repeat),
    );
    let [recursive] = recursive.as_slice() else {
        panic!("the implementation method should retain one direct recursive occurrence");
    };
    let [outside] = outside.as_slice() else {
        panic!("the ordinary global should retain one normally instantiated occurrence");
    };
    let [recursive_slot] = recursive.evidence.as_ref() else {
        panic!("the recursive occurrence should retain one interface obligation");
    };
    let [outside_slot] = outside.evidence.as_ref() else {
        panic!("the ordinary occurrence should retain one interface obligation");
    };

    assert_eq!(
        recursive_slot.method_arguments(),
        &[Type::Variable(method_parameter.id)]
    );
    assert_eq!(outside_slot.method_arguments(), &[Type::Bool]);
    let recursive_selection = selection_for_occurrence(recursive);
    let EvidenceNode::Implementation { implementation, .. } = recursive_selection
        .node(recursive_selection.root())
        .expect("direct recursion should retain exact-current evidence")
    else {
        panic!("direct recursion should select the exact current implementation");
    };
    assert_eq!(implementation, checked.implementation_facts()[0].id);
}

#[test]
fn identity_equal_abstract_prerequisite_dispatch_instantiates_method_locals_normally() {
    let checked = check(concat!(
        "interface Use<I> {\nuse<A> : (I, A) -> I\n}\n\n",
        "impl Use<Int> where Use<Int> {\n",
        "use (owner, ignored) = use((owner, 42))\n",
        "}\n\n",
        "main : Unit -> Unit\nmain () = ()\n",
    ))
    .expect("identity-equal abstract evidence should shadow exact-current dispatch");

    let use_method = MethodId::new(InterfaceId::new(checked.module(), 0), 0);
    let [method_parameter] = checked.interface_facts()[0].methods[0].type_parameters() else {
        panic!("the polymorphic method should retain one rigid local parameter");
    };
    let [requirement] = checked.implementation_facts()[0].prerequisites.as_ref() else {
        panic!("the implementation should retain its identity-equal prerequisite");
    };
    let occurrences = implementation_occurrence_selections(
        &checked.implementations()[0],
        ResolvedTermName::Method(use_method),
    );
    let [occurrence] = occurrences.as_slice() else {
        panic!("the implementation method should retain one prerequisite-dispatched occurrence");
    };
    let [slot] = occurrence.evidence.as_ref() else {
        panic!("the method occurrence should retain one interface obligation");
    };

    assert_eq!(slot.method_arguments(), &[Type::Int]);
    assert_ne!(
        slot.method_arguments(),
        &[Type::Variable(method_parameter.id)]
    );
    assert_abstract_selection(occurrence, requirement.id, &[use_method], &Type::Int);
}

#[test]
fn exact_current_polymorphic_recursion_retains_the_method_local_diagnostic() {
    let text = concat!(
        "interface Repeat<I> {\nrepeat<A> : (I, A) -> A\n}\n\n",
        "impl Repeat<Int> {\n",
        "repeat (owner, value) = repeat((owner, (value, value)))\n",
        "}\n",
    );
    let TypeError::Source(diagnostic) =
        check(text).expect_err("exact-current polymorphic recursion should be rejected")
    else {
        panic!("polymorphic recursion should retain a source diagnostic");
    };

    assert_eq!(diagnostic.reason.to_string(), "type.polymorphic-recursion");
    assert_eq!(diagnostic.expected.as_deref(), Some("A"));
    assert_eq!(diagnostic.found.as_deref(), Some("(A, A)"));
    assert_eq!(
        diagnostic.primary.message(),
        "this recursive call requires a different type instantiation"
    );
    assert!(
        diagnostic.related.iter().any(|label| {
            label.message() == "this recursive function is checked monomorphically"
        })
    );
}

#[test]
fn failed_body_rigidity_diagnostic_matches_the_same_recursive_application() {
    let text = concat!(
        "interface Repeat<I> {\nrepeat<A> : (I, A) -> A\n}\n\n",
        "impl Repeat<Int> {\n",
        "repeat (owner, value) = {\n",
        "let earlier = repeat((owner, (value, value)))\n",
        "repeat((owner, (value, value, value)))\n",
        "}\n",
        "}\n",
    );
    let final_call = text
        .rfind("repeat((owner, (value, value, value)))")
        .and_then(|offset| u32::try_from(offset).ok())
        .expect("the fixture should retain its representable final recursive application");
    let TypeError::Source(diagnostic) =
        check(text).expect_err("both polymorphic recursive applications should be rejected")
    else {
        panic!("polymorphic recursion should retain a source diagnostic");
    };

    assert_eq!(diagnostic.reason.to_string(), "type.polymorphic-recursion");
    assert!(
        diagnostic.primary.span().range().start() >= final_call,
        "the failed body must be correlated with the recursive application that caused it"
    );
}

#[test]
fn unrelated_selection_failure_does_not_mask_matching_polymorphic_recursion() {
    let text = concat!(
        "interface Missing<I> {\nmissing : I -> I\n}\n",
        "interface Repeat<I> {\nrepeat<A> : (I, A) -> A\n}\n",
        "impl Repeat<Int> {\n",
        "repeat (owner, value) = {\n",
        "let ignored = missing(owner)\n",
        "repeat((owner, (value, value)))\n",
        "}\n",
        "}\n",
        "main : Unit -> Unit\n",
        "main () = ()\n",
    );
    let TypeError::Source(diagnostic) = check(text).expect_err(
        "the matching exact-current recursion should be diagnosed before unrelated evidence",
    ) else {
        panic!("the matching recursive application should retain a source diagnostic");
    };

    assert_eq!(diagnostic.reason.to_string(), "type.polymorphic-recursion");
    assert_eq!(diagnostic.expected.as_deref(), Some("A"));
    assert_eq!(diagnostic.found.as_deref(), Some("(A, A)"));
}

#[test]
fn nested_same_method_calls_prefer_the_whole_failed_application() {
    let text = concat!(
        "interface Repeat<I> {\nrepeat<A> : (I, A) -> A\n}\n",
        "impl Repeat<Int> {\n",
        "repeat (owner, value) = repeat(repeat((owner, true)))\n",
        "}\n",
        "main : Unit -> Unit\n",
        "main () = ()\n",
    );
    let TypeError::Source(diagnostic) =
        check(text).expect_err("the nested exact-current call should reject polymorphic recursion")
    else {
        panic!("nested source geometry must never become an internal failure");
    };

    assert_eq!(diagnostic.reason.to_string(), "type.polymorphic-recursion");
    assert_eq!(diagnostic.expected.as_deref(), Some("A"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
}

#[test]
fn polymorphic_method_arguments_never_influence_candidate_selection() {
    let checked = check(concat!(
        "interface Choose<I> {\nchoose<A> : (I, A) -> I\n}\n\n",
        "impl Choose<Int> {\nchoose (owner, ignored) = owner\n}\n\n",
        "first : Int -> Int\nfirst owner = choose((owner, true))\n",
        "second : Int -> Int\nsecond owner = choose((owner, 42))\n",
    ))
    .expect("one concrete implementation should serve unrelated method instantiations");
    let choose = MethodId::new(InterfaceId::new(checked.module(), 0), 0);
    let mut occurrences = Vec::new();
    for spelling in ["first", "second"] {
        occurrences.extend(occurrence_selections(
            checked_definition(&checked, spelling),
            ResolvedTermName::Method(choose),
        ));
    }
    let [first, second] = occurrences.as_slice() else {
        panic!("the globals should retain two polymorphic method occurrences");
    };
    let first_selection = selection_for_occurrence(first);
    let second_selection = selection_for_occurrence(second);
    let EvidenceNode::Implementation {
        implementation: first_impl,
        ..
    } = first_selection
        .node(first_selection.root())
        .expect("the first occurrence should select concrete evidence")
    else {
        panic!("the first occurrence should select an implementation");
    };
    let EvidenceNode::Implementation {
        implementation: second_impl,
        ..
    } = second_selection
        .node(second_selection.root())
        .expect("the second occurrence should select concrete evidence")
    else {
        panic!("the second occurrence should select an implementation");
    };

    assert_eq!(first_impl, second_impl);
    assert_eq!(first.evidence[0].method_arguments(), &[Type::Bool]);
    assert_eq!(second.evidence[0].method_arguments(), &[Type::Int]);
}

#[test]
fn ordinary_candidate_search_does_not_refine_a_rigid_higher_kinded_goal() {
    let error = check(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "type Wrapped<F : Type -> Type> = Wrapped(F<Int>)\n\n",
        "interface Construct<F : Type -> Type> {\nconstruct : Int -> F<Int>\n}\n\n",
        "impl Construct<Option> {\nconstruct value = Some(value)\n}\n\n",
        "interface Use<A> {\nuse : A -> A\n}\n\n",
        "impl<F : Type -> Type> Use<Wrapped<F>> {\n",
        "use value = Wrapped(construct 42)\n",
        "}\n",
    ))
    .expect_err("Construct<Option> must not refine the rigid implementation parameter F");

    assert_eq!(interface_reason(error), "constraint.unsatisfied");
}

#[test]
fn higher_kinded_prerequisite_cycle_is_preserved_through_a_method_occurrence() {
    let error = check(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Construct<F : Type -> Type> {\nconstruct : Int -> F<Int>\n}\n\n",
        "impl Construct<Option> where Construct<Option> {\n",
        "construct value = Some(value)\n",
        "}\n\n",
        "probe : Unit -> Option<Int>\n",
        "probe () = construct 42\n",
    ))
    .expect_err("the selected higher-kinded prerequisite must re-enter the active goal");

    assert_eq!(interface_reason(error), "constraint.cycle");
}

#[test]
fn recursive_constrained_global_reuses_its_declared_abstract_evidence() {
    let checked = check(concat!(
        "interface Step<A> {\nstep : A -> A\n}\n\n",
        "loop : Int -> Int where Step<Int>\n",
        "loop value = step (loop value)\n",
    ))
    .expect("the recursive constrained global should check with its declared evidence");

    let scheme = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "loop")
        .expect("the recursive global scheme should remain checked");
    let [requirement] = scheme.scheme.requirements.as_ref() else {
        panic!("the recursive global should retain its one requirement");
    };
    let method = MethodId::new(InterfaceId::new(checked.module(), 0), 0);
    let definition = checked_definition(&checked, "loop");
    let method_occurrences = occurrence_selections(definition, ResolvedTermName::Method(method));
    let [method_occurrence] = method_occurrences.as_slice() else {
        panic!("the recursive body should retain one Step.step occurrence");
    };
    let recursive_occurrences =
        occurrence_selections(definition, ResolvedTermName::Global(scheme.binder));
    let [recursive_occurrence] = recursive_occurrences.as_slice() else {
        panic!("the recursive body should retain one loop occurrence");
    };
    assert_abstract_selection(method_occurrence, requirement.id, &[method], &Type::Int);
    assert_abstract_selection(recursive_occurrence, requirement.id, &[method], &Type::Int);
}

#[test]
fn earlier_implementation_body_error_precedes_later_global_body_error() {
    let error = check(concat!(
        "interface Convert<A> {\nconvert : A -> A\n}\n\n",
        "impl Convert<Int> {\nconvert value = true\n}\n\n",
        "later : Bool -> Bool\nlater value = convert value\n",
    ))
    .expect_err("the first invalid body in cross-family source order should reject the module");

    assert_eq!(diagnostic_reason(error), "type.definition-result");
}

#[test]
fn earlier_global_body_error_precedes_later_implementation_body_error() {
    let error = check(concat!(
        "interface Convert<A> {\nconvert : A -> A\n}\n\n",
        "earlier : Unit -> Int\nearlier () = true + 1\n\n",
        "impl Convert<Int> {\nconvert value = true\n}\n",
    ))
    .expect_err("the first invalid body in cross-family source order should reject the module");

    assert_eq!(diagnostic_reason(error), "type.operator-operand");
}
