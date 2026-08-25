//! Resolution and checking evidence for independent library import channels.

use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{TypeError, check_module},
    interface::InterfaceReason,
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveReason, resolve_module},
    resolved::{ImportedTypeAccess, ResolvedDefinitionKind, ResolvedExprKind, ResolvedTermName},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleTree(PathBuf);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-library-imports-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("library import fixture should be creatable: {error}"),
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

fn load(tree: &ModuleTree, entry: &str, dependencies: &[(&str, &str)]) -> ModuleGraph {
    let entry = tree.write("entry.ash", entry);
    for (path, source) in dependencies {
        tree.write(path, source);
    }
    load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture graph should load")
}

fn module_named<'a>(graph: &'a ModuleGraph, file_name: &str) -> &'a LoadedModule {
    graph
        .modules()
        .iter()
        .find(|module| {
            Path::new(module.source().display_path()).file_name() == Some(file_name.as_ref())
        })
        .expect("fixture module should be present")
}

fn resolve_entry_error(graph: &ModuleGraph) -> ash::resolve::ResolveError {
    let entry = module_named(graph, "entry.ash");
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency: &&ash::resolved::CheckedModule| {
                        dependency.module() == edge.target()
                    })
                    .expect("dependencies should check before their importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the dependency summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies);
        if module.id() == entry.id() {
            return resolved.expect_err("the entry fixture should fail resolution");
        }
        checked.push(
            check_module(resolved.expect("a dependency fixture should resolve"))
                .expect("a dependency fixture should check"),
        );
    }
    panic!("the graph should contain its entry module");
}

fn resolve_entry(graph: &ModuleGraph) -> ash::resolved::ResolvedModule {
    let entry = module_named(graph, "entry.ash");
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency: &&ash::resolved::CheckedModule| {
                        dependency.module() == edge.target()
                    })
                    .expect("dependencies should check before their importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the dependency summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the successful entry fixture should resolve");
        if module.id() == entry.id() {
            return resolved;
        }
        checked.push(check_module(resolved).expect("a dependency fixture should check"));
    }
    panic!("the graph should contain its entry module");
}

#[test]
fn name_only_import_does_not_select_implementation() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import equality (Equal, equal)\n\n",
            "main : Unit -> Bool\n",
            "main () = equal(1, 1)\n",
        ),
        &[(
            "equality.ash",
            concat!(
                "pub interface Equal<A> {\n",
                "equal : (A, A) -> Bool\n",
                "}\n\n",
                "pub impl Equal<Int> {\n",
                "equal (left, right) = left == right\n",
                "}\n",
            ),
        )],
    );
    let equality = module_named(&graph, "equality.ash");
    let equality_checked = check_module(
        resolve_module(equality, &[]).expect("the equality dependency should resolve"),
    )
    .expect("the equality dependency should check");
    let [interface] = equality_checked.interface_facts() else {
        panic!("the dependency should publish one interface fact");
    };
    let [implementation] = equality_checked.implementation_facts() else {
        panic!("the dependency should publish one implementation fact");
    };
    let entry = module_named(&graph, "entry.ash");
    let [edge] = entry.dependencies() else {
        panic!("the entry should have one direct dependency");
    };
    let dependency = DependencyExports::new(edge, equality_checked.exports())
        .expect("the entry edge should authenticate the dependency summary");
    let resolved =
        resolve_module(entry, &[dependency]).expect("the name-only import should resolve");
    let retained_interface = resolved.imported_facts().interface(interface.id).is_some();
    let retained_implementation = resolved
        .imported_facts()
        .implementation(implementation.id)
        .is_some();

    let error = check_module(resolved)
        .expect_err("a name-only import should not satisfy the method obligation");
    let TypeError::Interface(diagnostic) = error else {
        panic!("the method occurrence should retain an interface diagnostic");
    };
    let occurrence_start = entry
        .source()
        .text()
        .rfind("equal")
        .expect("the entry should contain the method occurrence");

    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert_eq!(diagnostic.reason.to_string(), "constraint.unsatisfied");
    assert_eq!(diagnostic.primary.span().source(), entry.source().id());
    assert_eq!(
        diagnostic.primary.span().range().start(),
        u32::try_from(occurrence_start).expect("the fixture offset should fit")
    );
    assert_eq!(diagnostic.primary.span().range().end(), {
        u32::try_from(occurrence_start + "equal".len()).expect("the fixture offset should fit")
    });
    assert!(retained_interface);
    assert!(!retained_implementation);
}

#[test]
fn implementation_only_import_selects_evidence_without_binding_names() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import equality as Equality\n",
            "import equality (impl Equal)\n\n",
            "type Equal = LocalEqual\n\n",
            "equal : Bool -> Bool\n",
            "equal value = value\n\n",
            "main : Unit -> Bool\n",
            "main () = Equality.equal(1, 1)\n",
        ),
        &[(
            "equality.ash",
            concat!(
                "pub interface Equal<A> {\n",
                "equal : (A, A) -> Bool\n",
                "}\n\n",
                "pub impl Equal<Int> {\n",
                "equal (left, right) = left == right\n",
                "}\n",
            ),
        )],
    );
    let equality = module_named(&graph, "equality.ash");
    let equality_checked = check_module(
        resolve_module(equality, &[]).expect("the equality dependency should resolve"),
    )
    .expect("the equality dependency should check");
    let [defining_interface] = equality_checked.interface_facts() else {
        panic!("the dependency should publish one interface fact");
    };
    let [defining_implementation] = equality_checked.implementation_facts() else {
        panic!("the dependency should publish one implementation fact");
    };
    let expected_method = defining_interface.methods[0].id;
    let expected_implementation = defining_implementation.id;
    let expected_implementation_method = defining_implementation.methods[0].id;
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| {
            DependencyExports::new(edge, equality_checked.exports())
                .expect("the entry edges should authenticate the dependency summary")
        })
        .collect::<Vec<_>>();
    let resolved = resolve_module(entry, &dependencies)
        .expect("the implementation selector should bind no unqualified names");
    let imported = resolved
        .imported_facts()
        .implementation(expected_implementation)
        .expect("the implementation selector should retain its matching public fact");
    let ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[1].kind else {
        panic!("the entry should retain its main equation");
    };
    let ResolvedExprKind::Apply(application) = &main.equations[0].body.kind else {
        panic!("main should apply the qualified method");
    };
    let ResolvedExprKind::Occurrence(occurrence) = &application.function.kind else {
        panic!("main should retain the qualified method occurrence");
    };
    let resolved_method = occurrence.term;
    let imported_implementation = imported.id;
    let imported_method = imported.methods[0].id;

    let checked = check_module(resolved)
        .expect("the selected implementation should satisfy the qualified method call");

    assert_eq!(resolved_method, ResolvedTermName::Method(expected_method));
    assert_eq!(imported_implementation, expected_implementation);
    assert_eq!(imported_method, expected_implementation_method);
    assert_eq!(checked.available_implementations().len(), 1);
    assert_eq!(
        checked.available_implementations()[0].id(),
        expected_implementation
    );
}

#[test]
fn implementation_selector_rejects_an_unavailable_interface() {
    for (selected, dependency) in [
        (
            "Missing",
            "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n",
        ),
        (
            "Private",
            "interface Private<A> {\nprivate : (A, A) -> Bool\n}\n",
        ),
    ] {
        let tree = ModuleTree::create();
        let graph = load(
            &tree,
            &format!("import dependency (impl {selected})\n"),
            &[("dependency.ash", dependency)],
        );

        let error = resolve_entry_error(&graph);

        assert_eq!(error.reason, ResolveReason::UnavailableExport, "{selected}");
        assert_eq!(
            error.diagnostic().primary.span().source(),
            module_named(&graph, "entry.ash").source().id(),
            "{selected}"
        );
    }
}

#[test]
fn implementation_selector_rejects_a_public_nominal() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency (impl Nominal)\n",
        &[("dependency.ash", "pub type Nominal = Nominal\n")],
    );

    let error = resolve_entry_error(&graph);

    assert_eq!(error.reason, ResolveReason::InterfaceKind);
    assert_eq!(error.reason.to_string(), "resolve.interface-kind");
}

#[test]
fn public_targeted_import_reexports_each_selected_name_namespace() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import facade (facade_answer, FacadeChoice, FacadeFirst, FacadeSecond, ",
            "FacadeToken, FacadeComparable, facade_compare, impl FacadeComparable)\n\n",
            "use_choice : Unit -> FacadeChoice\n",
            "use_choice () = FacadeFirst(1)\n\n",
            "keep_token : FacadeToken -> FacadeToken\n",
            "keep_token token = token\n\n",
            "compare : (Int, Int) -> Bool\n",
            "compare pair = facade_compare pair\n\n",
            "main : Unit -> Int\n",
            "main () = facade_answer(())\n",
        ),
        &[
            (
                "base.ash",
                concat!(
                    "pub type Choice =\n",
                    "First(Int)\n",
                    "| Second(Int)\n\n",
                    "pub opaque type Token = Token(Int)\n\n",
                    "pub interface Comparable<A> {\n",
                    "compare : (A, A) -> Bool\n",
                    "}\n\n",
                    "pub impl Comparable<Int> {\n",
                    "compare (left, right) = left == right\n",
                    "}\n\n",
                    "pub answer : Unit -> Int\n",
                    "answer () = 42\n",
                ),
            ),
            (
                "facade.ash",
                concat!(
                    "pub import base (answer as facade_answer, Choice as FacadeChoice, ",
                    "First as FacadeFirst, Second as FacadeSecond, Token as FacadeToken, ",
                    "Comparable as FacadeComparable, compare as facade_compare, ",
                    "impl Comparable)\n",
                ),
            ),
        ],
    );

    let base = module_named(&graph, "base.ash");
    let base_checked =
        check_module(resolve_module(base, &[]).expect("the defining module should resolve"))
            .expect("the defining module should check");
    let expected_global = base_checked.schemes()[0].binder;
    let [choice, token] = base_checked.registry().nominals() else {
        panic!("the defining module should retain both nominal declarations");
    };
    let expected_choice = choice.id;
    let [expected_first, expected_second] = choice.constructors.as_ref() else {
        panic!("the transparent nominal should retain both constructors");
    };
    let expected_token = token.id;
    let [interface] = base_checked.interface_facts() else {
        panic!("the defining module should retain one interface fact");
    };
    let expected_interface = interface.id;
    let [method] = interface.methods.as_ref() else {
        panic!("the defining interface should retain one method fact");
    };
    let expected_method = method.id;
    let [implementation] = base_checked.implementation_facts() else {
        panic!("the defining module should retain one implementation fact");
    };
    let expected_implementation = implementation.id;

    let facade = module_named(&graph, "facade.ash");
    let [facade_edge] = facade.dependencies() else {
        panic!("the facade should have one dependency");
    };
    let facade_dependency = DependencyExports::new(facade_edge, base_checked.exports())
        .expect("the facade edge should authenticate the base summary");
    let facade_resolved =
        resolve_module(facade, &[facade_dependency]).expect("the public import should resolve");
    let candidate = facade_resolved.export_candidate();
    assert_eq!(
        candidate.term("facade_answer").map(|term| term.binder),
        Some(expected_global),
    );
    assert_eq!(
        candidate.nominal("FacadeChoice").map(|nominal| nominal.id),
        Some(expected_choice),
    );
    assert_eq!(
        candidate
            .constructor("FacadeFirst")
            .map(|constructor| constructor.id),
        Some(*expected_first),
    );
    assert_eq!(
        candidate
            .constructor("FacadeSecond")
            .map(|constructor| constructor.id),
        Some(*expected_second),
    );
    assert_eq!(
        candidate.nominal("FacadeToken").map(|nominal| nominal.id),
        Some(expected_token),
    );
    assert_eq!(
        candidate
            .interface("FacadeComparable")
            .map(|interface| interface.id),
        Some(expected_interface),
    );
    assert_eq!(
        candidate.method("facade_compare").map(|method| method.id),
        Some(expected_method),
    );
    assert_eq!(
        facade_resolved
            .imported_facts()
            .implementation(expected_implementation)
            .map(|fact| fact.id),
        Some(expected_implementation),
        "the public implementation selector should remain locally effective",
    );
    let facade_checked =
        check_module(facade_resolved).expect("the name-only facade should check without bodies");
    assert_eq!(facade_checked.exports().module(), facade.id());
    assert_eq!(expected_global.module(), Some(base.id()));
    assert_eq!(expected_choice.module(), base.id());
    assert_eq!(expected_first.owner().module(), base.id());
    assert_eq!(expected_second.owner().module(), base.id());
    assert_eq!(expected_token.module(), base.id());
    assert_eq!(expected_interface.module(), base.id());
    assert_eq!(expected_method.interface(), expected_interface);
    assert_eq!(expected_method.interface().module(), base.id());
    assert_eq!(
        facade_checked.available_implementations()[0].id(),
        expected_implementation,
        "Task 4 should retain the selected implementation only in the facade environment",
    );

    let entry = module_named(&graph, "entry.ash");
    let [entry_edge] = entry.dependencies() else {
        panic!("the entry should have one dependency");
    };
    let entry_dependency = DependencyExports::new(entry_edge, facade_checked.exports())
        .expect("the entry edge should authenticate the facade summary");
    let entry_resolved = resolve_module(entry, &[entry_dependency])
        .expect("the facade's selected public spellings should resolve");

    assert_eq!(
        entry_resolved
            .imported_facts()
            .global(expected_global)
            .map(|fact| fact.binder),
        Some(expected_global),
    );
    assert_eq!(
        entry_resolved
            .imported_facts()
            .nominal(expected_choice)
            .map(|fact| fact.id),
        Some(expected_choice),
    );
    assert_eq!(
        entry_resolved
            .imported_facts()
            .constructor(*expected_first)
            .map(|fact| fact.id),
        Some(*expected_first),
    );
    assert_eq!(
        entry_resolved
            .imported_facts()
            .constructor(*expected_second)
            .map(|fact| fact.id),
        Some(*expected_second),
    );
    assert_eq!(
        entry_resolved
            .imported_facts()
            .nominal(expected_token)
            .map(|fact| fact.id),
        Some(expected_token),
    );
    let imported_interface = entry_resolved
        .imported_facts()
        .interface(expected_interface)
        .expect("the facade should retain the original interface identity");
    assert_eq!(imported_interface.id, expected_interface);
    assert_eq!(imported_interface.methods[0].id, expected_method);
    assert!(
        entry_resolved
            .imported_facts()
            .implementation(expected_implementation)
            .is_none(),
        "Task 4 must not publish the facade's imported implementation fact",
    );
}

#[test]
fn name_reexports_preserve_privacy_opacity_and_identity() {
    for (entry, dependency, reason) in [
        (
            "pub import base (private_value)\n",
            concat!("private_value : Unit -> Int\n", "private_value () = 0\n",),
            ResolveReason::UnavailableExport,
        ),
        (
            "pub import base (Seal)\n",
            "pub opaque type Token = Seal(Int)\n",
            ResolveReason::OpaqueConstructor,
        ),
    ] {
        let tree = ModuleTree::create();
        let graph = load(&tree, entry, &[("base.ash", dependency)]);
        let error = resolve_entry_error(&graph);

        assert_eq!(error.reason, reason);
        assert_eq!(
            error.diagnostic().primary.span().source(),
            module_named(&graph, "entry.ash").source().id(),
        );
    }

    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import outer (PublicToken)\n\n",
            "keep : PublicToken -> PublicToken\n",
            "keep token = token\n",
        ),
        &[
            ("base.ash", "pub opaque type Token = Token(Int)\n"),
            ("inner.ash", "pub import base (Token as WrappedToken)\n"),
            (
                "outer.ash",
                "pub import inner (WrappedToken as PublicToken)\n",
            ),
        ],
    );
    let base = module_named(&graph, "base.ash");
    let token = resolve_module(base, &[])
        .expect("the opaque base should resolve")
        .registry()
        .nominals()[0]
        .id;
    let mut checked = Vec::new();
    let mut entry_resolved = None;
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency: &&ash::resolved::CheckedModule| {
                        dependency.module() == edge.target()
                    })
                    .expect("each facade dependency should check first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("each facade summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved =
            resolve_module(module, &dependencies).expect("both opaque facades should resolve");
        if module.id() == graph.entry() {
            entry_resolved = Some(resolved);
            break;
        }
        checked.push(check_module(resolved).expect("each opaque dependency should check"));
    }
    let entry_resolved = entry_resolved.expect("the graph should retain its entry");
    let imported_token = entry_resolved
        .imported_facts()
        .nominal(token)
        .expect("the opaque identity should cross both facades");
    assert_eq!(imported_token.id, token);
    assert_eq!(imported_token.access, ImportedTypeAccess::Opaque);
    assert!(imported_token.constructors.is_empty());

    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import outer (PublicToken)\n\n",
            "main : Unit -> PublicToken\n",
            "main () = PublicToken(1)\n",
        ),
        &[
            ("base.ash", "pub opaque type Token = Token(Int)\n"),
            ("inner.ash", "pub import base (Token as WrappedToken)\n"),
            (
                "outer.ash",
                "pub import inner (WrappedToken as PublicToken)\n",
            ),
        ],
    );
    let error = resolve_entry_error(&graph);
    assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
    assert_eq!(error.diagnostic().found.as_deref(), Some("PublicToken"));

    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import facade as Facade\n\n",
            "name_hidden : Facade.Hidden -> Facade.Hidden\n",
            "name_hidden value = value\n",
        ),
        &[
            (
                "base.ash",
                concat!(
                    "type Hidden = Hidden(Int)\n\n",
                    "pub make : Int -> Hidden\n",
                    "make value = Hidden(value)\n\n",
                    "pub read : Hidden -> Int\n",
                    "read (Hidden value) = value\n",
                ),
            ),
            (
                "facade.ash",
                "pub import base (make as facade_make, read as facade_read)\n",
            ),
        ],
    );
    let error = resolve_entry_error(&graph);
    assert_eq!(error.reason, ResolveReason::UnavailableExport);
    assert_eq!(error.diagnostic().found.as_deref(), Some("Hidden"));

    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import facade (first_answer, second_answer)\n\n",
            "first : Unit -> Int\n",
            "first () = first_answer(())\n\n",
            "second : Unit -> Int\n",
            "second () = second_answer(())\n",
        ),
        &[
            ("base.ash", "pub answer : Unit -> Int\nanswer () = 42\n"),
            (
                "facade.ash",
                concat!(
                    "pub import base (answer as first_answer, ",
                    "answer as second_answer)\n",
                ),
            ),
        ],
    );
    let base = module_named(&graph, "base.ash");
    let base_checked = check_module(resolve_module(base, &[]).expect("the base should resolve"))
        .expect("the base should check");
    let expected_binder = base_checked.schemes()[0].binder;
    let facade = module_named(&graph, "facade.ash");
    let [facade_edge] = facade.dependencies() else {
        panic!("the alias facade should have one dependency");
    };
    let facade_dependency = DependencyExports::new(facade_edge, base_checked.exports())
        .expect("the alias facade edge should authenticate its summary");
    let facade_checked = check_module(
        resolve_module(facade, &[facade_dependency]).expect("both aliases should resolve"),
    )
    .expect("the alias facade should check");
    assert!(
        facade_checked.schemes().is_empty(),
        "re-export aliases must not synthesize facade declarations",
    );
    let entry = module_named(&graph, "entry.ash");
    let [entry_edge] = entry.dependencies() else {
        panic!("the alias entry should have one dependency");
    };
    let entry_dependency = DependencyExports::new(entry_edge, facade_checked.exports())
        .expect("the alias entry edge should authenticate its summary");
    let entry_resolved =
        resolve_module(entry, &[entry_dependency]).expect("both facade aliases should resolve");
    assert_eq!(
        entry_resolved
            .imported_facts()
            .global(expected_binder)
            .map(|fact| fact.binder),
        Some(expected_binder),
    );
    for definition in entry_resolved.definitions() {
        let ResolvedDefinitionKind::Equational(global) = &definition.kind else {
            panic!("the alias fixture should retain equational definitions");
        };
        let ResolvedExprKind::Apply(application) = &global.equations[0].body.kind else {
            panic!("each alias fixture body should apply its imported global");
        };
        let ResolvedExprKind::Occurrence(occurrence) = &application.function.kind else {
            panic!("each alias should resolve to an occurrence");
        };
        assert_eq!(occurrence.term, ResolvedTermName::Global(expected_binder),);
    }

    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import facade (private_answer)\n",
        &[
            ("base.ash", "pub answer : Unit -> Int\nanswer () = 42\n"),
            ("facade.ash", "import base (answer as private_answer)\n"),
        ],
    );
    let error = resolve_entry_error(&graph);
    assert_eq!(error.reason, ResolveReason::UnavailableExport);
    assert_eq!(error.diagnostic().found.as_deref(), Some("private_answer"));
}

#[test]
fn opaque_constructor_family_withholding_crosses_nominal_only_facades() {
    for (facades, entry) in [
        (
            &[("facade.ash", "pub import base (Token as PublicToken)\n")][..],
            "import facade (Seal)\n",
        ),
        (
            &[
                ("inner.ash", "pub import base (Token as WrappedToken)\n"),
                (
                    "outer.ash",
                    "pub import inner (WrappedToken as PublicToken)\n",
                ),
            ][..],
            "import outer (Seal)\n",
        ),
        (
            &[("facade.ash", "pub import base (Token as PublicToken)\n")][..],
            concat!(
                "import facade as Facade\n\n",
                "main : Unit -> Facade.PublicToken\n",
                "main () = Facade.Seal(1)\n",
            ),
        ),
        (
            &[
                ("inner.ash", "pub import base (Token as WrappedToken)\n"),
                (
                    "outer.ash",
                    "pub import inner (WrappedToken as PublicToken)\n",
                ),
            ][..],
            concat!(
                "import outer as Outer\n\n",
                "main : Unit -> Outer.PublicToken\n",
                "main () = Outer.Seal(1)\n",
            ),
        ),
    ] {
        let tree = ModuleTree::create();
        let mut dependencies = vec![("base.ash", "pub opaque type Token = Seal(Int)\n")];
        dependencies.extend_from_slice(facades);
        let graph = load(&tree, entry, &dependencies);

        let error = resolve_entry_error(&graph);
        let diagnostic = error.diagnostic();
        let base = module_named(&graph, "base.ash");
        let seal_start = base
            .source()
            .text()
            .find("Seal")
            .expect("the defining constructor spelling should exist");

        assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
        assert_eq!(diagnostic.found.as_deref(), Some("Seal"));
        assert_eq!(
            diagnostic.primary.message(),
            "this constructor belongs to an opaque type",
        );
        assert_eq!(
            diagnostic.primary.span().source(),
            module_named(&graph, "entry.ash").source().id(),
        );
        assert_eq!(
            usize::try_from(diagnostic.primary.span().range().start())
                .expect("the selected constructor offset should fit"),
            entry
                .rfind("Seal")
                .expect("the selected constructor spelling should exist"),
        );
        assert_eq!(diagnostic.related.len(), 1);
        assert_eq!(
            diagnostic.related[0].message(),
            "the inaccessible declaration is here",
        );
        assert_eq!(diagnostic.related[0].span().source(), base.source().id());
        assert_eq!(
            usize::try_from(diagnostic.related[0].span().range().start())
                .expect("the constructor offset should fit"),
            seal_start,
        );
    }
}

#[test]
fn method_only_reexport_and_imported_scheme_retain_hidden_interface_closure() {
    for (facade_selection, entry_name, exported_global) in [
        ("equal as facade_equal", "facade_equal", false),
        ("same as facade_same", "facade_same", true),
    ] {
        let tree = ModuleTree::create();
        let graph = load(
            &tree,
            &format!(
                concat!(
                    "import facade ({})\n",
                    "import base (impl Equal)\n\n",
                    "main : Unit -> Bool\n",
                    "main () = {}(1, 1)\n",
                ),
                entry_name, entry_name,
            ),
            &[
                (
                    "base.ash",
                    concat!(
                        "pub interface Equal<A> {\n",
                        "equal : (A, A) -> Bool\n",
                        "}\n\n",
                        "pub impl Equal<Int> {\n",
                        "equal (left, right) = left == right\n",
                        "}\n\n",
                        "pub same : (A, A) -> Bool where Equal<A>\n",
                        "same pair = equal pair\n",
                    ),
                ),
                (
                    "facade.ash",
                    &format!("pub import base ({facade_selection})\n"),
                ),
            ],
        );
        let mut checked = Vec::new();
        let mut base_interface = None;
        let mut base_global = None;
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|dependency: &&ash::resolved::CheckedModule| {
                            dependency.module() == edge.target()
                        })
                        .expect("hidden-closure dependencies should check first");
                    DependencyExports::new(edge, dependency.exports())
                        .expect("hidden-closure summaries should authenticate their edges")
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies)
                .expect("the hidden-closure fixture should resolve");
            if Path::new(module.source().display_path()).file_name() == Some("entry.ash".as_ref()) {
                let expected_interface = base_interface.expect("base should check before entry");
                assert!(
                    resolved
                        .imported_facts()
                        .interface(expected_interface)
                        .is_some()
                );
                if exported_global {
                    assert!(
                        resolved
                            .imported_facts()
                            .global(base_global.expect("base should retain the constrained global"))
                            .is_some(),
                    );
                }
            }
            let module_checked = check_module(resolved)
                .expect("method-only and constrained-global closure should both check");
            if Path::new(module.source().display_path()).file_name() == Some("base.ash".as_ref()) {
                base_interface = Some(module_checked.interface_facts()[0].id);
                base_global = Some(module_checked.schemes()[0].binder);
            }
            checked.push(module_checked);
        }
    }
}

#[test]
fn partial_transparent_name_reexports_retain_hidden_constructor_family() {
    for (entry, inner, outer) in [
        (
            "import outer (PublicChoice)\n",
            "pub import base (Choice as InnerChoice)\n",
            "pub import inner (InnerChoice as PublicChoice)\n",
        ),
        (
            "import outer (PublicFirst)\n",
            "pub import base (First as InnerFirst)\n",
            "pub import inner (InnerFirst as PublicFirst)\n",
        ),
    ] {
        let tree = ModuleTree::create();
        let graph = load(
            &tree,
            entry,
            &[
                (
                    "base.ash",
                    "pub type Choice =\nFirst(Int)\n| Second(Bool)\n",
                ),
                ("inner.ash", inner),
                ("outer.ash", outer),
            ],
        );
        let base = module_named(&graph, "base.ash");
        let base_resolved = resolve_module(base, &[]).expect("the family base should resolve");
        let [choice] = base_resolved.registry().nominals() else {
            panic!("the family base should retain one nominal");
        };
        let expected_choice = choice.id;
        let [expected_first, expected_second] = choice.constructors.as_ref() else {
            panic!("the family base should retain both constructors");
        };

        let resolved = resolve_entry(&graph);
        let imported_choice = resolved
            .imported_facts()
            .nominal(expected_choice)
            .expect("the selected name should retain its defining owner metadata");
        assert_eq!(imported_choice.id, expected_choice);
        assert_eq!(imported_choice.access, ImportedTypeAccess::Transparent);
        assert_eq!(
            imported_choice.constructors.as_ref(),
            [*expected_first, *expected_second]
        );
        assert_eq!(
            resolved
                .imported_facts()
                .constructor(*expected_first)
                .map(|constructor| constructor.id),
            Some(*expected_first),
        );
        assert_eq!(
            resolved
                .imported_facts()
                .constructor(*expected_second)
                .map(|constructor| constructor.id),
            Some(*expected_second),
        );

        let hidden_tree = ModuleTree::create();
        let hidden_graph = load(
            &hidden_tree,
            "import outer (Second)\n",
            &[
                (
                    "base.ash",
                    "pub type Choice =\nFirst(Int)\n| Second(Bool)\n",
                ),
                ("inner.ash", inner),
                ("outer.ash", outer),
            ],
        );
        let error = resolve_entry_error(&hidden_graph);
        assert_eq!(error.reason, ResolveReason::UnavailableExport);
        assert_eq!(error.diagnostic().found.as_deref(), Some("Second"));
    }
}
