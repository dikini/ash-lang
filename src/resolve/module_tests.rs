use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use crate::{
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolved::{
        BinderId, ExportSummary, ExportedTypeAccess, ImportedNominalFactRef, ImportedTypeAccess,
        ResolvedDefinitionKind, ResolvedExprKind, ResolvedModule, ResolvedPatternKind,
        ResolvedTypeVariable,
    },
    source::Origin,
    types::{ConstructorId, NominalTypeId, Type, TypeVariableId, TypeWorkBudget},
};

use super::{DependencyExports, ResolveError, ResolveReason, Resolver, resolve_module};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-resolve-module-unit-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("test tree should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be creatable");
        }
        fs::write(&path, text).expect("fixture should be writable");
        path
    }
}

impl Drop for TempTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn load(tree: &TempTree, entry_text: &str, dependencies: &[(&str, &str)]) -> ModuleGraph {
    let entry = tree.write("entry.ash", entry_text);
    for (path, text) in dependencies {
        tree.write(path, text);
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

fn resolve_with(
    module: &LoadedModule,
    summaries: &[&ExportSummary],
) -> Result<ResolvedModule, ResolveError> {
    assert_eq!(module.dependencies().len(), summaries.len());
    let dependencies = module
        .dependencies()
        .iter()
        .zip(summaries)
        .map(|(edge, summary)| {
            DependencyExports::new(edge, summary).expect("summary should match its import edge")
        })
        .collect::<Vec<_>>();
    resolve_module(module, &dependencies)
}

#[test]
fn reordered_dependency_pairs_are_rejected_before_scope_installation() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first as First\nimport second as Second\n",
        &[("first.ash", ""), ("second.ash", "")],
    );
    let importer = module_named(&graph, "entry.ash");
    let first = module_named(&graph, "first.ash");
    let second = module_named(&graph, "second.ash");
    let first_summary = ExportSummary::test_fixture(first.id(), vec![], vec![], vec![], vec![]);
    let second_summary = ExportSummary::test_fixture(second.id(), vec![], vec![], vec![], vec![]);
    let mut dependencies = importer
        .dependencies()
        .iter()
        .zip([&first_summary, &second_summary])
        .map(|(edge, summary)| DependencyExports::new(edge, summary).expect("matching summary"))
        .collect::<Vec<_>>();
    dependencies.swap(0, 1);

    let error = resolve_module(importer, &dependencies)
        .expect_err("source import order must authenticate dependency pairs");

    assert_eq!(error.reason, ResolveReason::InternalState);
}

fn equational(module: &ResolvedModule, index: usize) -> &crate::resolved::ResolvedEquationalGlobal {
    let ResolvedDefinitionKind::Equational(definition) = &module.definitions()[index].kind else {
        panic!("expected an equational definition");
    };
    definition
}

fn nominal_function_parts(ty: &Type) -> (NominalTypeId, NominalTypeId) {
    let Type::Function(domain, codomain) = ty else {
        panic!("expected a function type");
    };
    let Type::Nominal(domain) = domain.as_ref() else {
        panic!("expected a nominal domain");
    };
    let Type::Nominal(codomain) = codomain.as_ref() else {
        panic!("expected a nominal codomain");
    };
    (*domain, *codomain)
}

#[test]
fn qualified_import_resolves_term_type_and_constructor_identities() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Dep.Box -> Dep.Box\n",
            "main Dep.Box = Dep.answer\n",
        ),
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let binder = BinderId::resolved(dependency.id(), 7);
    let nominal = NominalTypeId::new(dependency.id(), 3);
    let constructor = ConstructorId::new(nominal, 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![("answer", binder, Type::Unit, origin.clone())],
        vec![(
            "Box",
            nominal,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Box", constructor, None, origin)],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary]).expect("qualified imports should resolve");
    let definition = equational(&resolved, 0);
    assert_eq!(
        nominal_function_parts(&definition.interface.annotation.ty),
        (nominal, nominal)
    );
    assert!(matches!(
        definition.equations[0].patterns[0].kind,
        ResolvedPatternKind::Constructor {
            constructor: found,
            ..
        } if found == constructor
    ));
    assert!(matches!(
        definition.equations[0].body.kind,
        ResolvedExprKind::Occurrence(ref occurrence)
            if occurrence.global_binder() == Some(binder)
    ));
}

#[test]
fn targeted_import_rename_preserves_the_exported_binder_identity() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (answer as renamed)\nmain : Unit -> Unit\nmain () = renamed\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let binder = BinderId::resolved(dependency.id(), 9);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "answer",
            binder,
            Type::Unit,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary]).expect("the rename should resolve");
    assert!(matches!(
        equational(&resolved, 0).equations[0].body.kind,
        ResolvedExprKind::Occurrence(ref occurrence)
            if occurrence.spelling == "renamed"
                && occurrence.global_binder() == Some(binder)
    ));
}

#[test]
fn one_targeted_selector_imports_same_spelled_type_and_constructor() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Box)\nmain : Unit -> Box\nmain () = Box\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Box",
            nominal,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Box", constructor, None, origin)],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary]).expect("both namespaces should resolve");
    let definition = equational(&resolved, 0);
    let Type::Function(_, codomain) = &definition.interface.annotation.ty else {
        panic!("expected a function type");
    };
    assert_eq!(codomain.as_ref(), &Type::Nominal(nominal));
    assert!(matches!(
        definition.equations[0].body.kind,
        ResolvedExprKind::Constructor(ref occurrence) if occurrence.constructor == constructor
    ));
}

#[test]
fn duplicate_targeted_selector_is_an_import_conflict() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (answer, answer)\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "answer",
            BinderId::resolved(dependency.id(), 0),
            Type::Unit,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary]).expect_err("the duplicate should conflict");
    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn bindings_from_distinct_imports_cannot_silently_shadow() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first (answer)\nimport second (answer)\n",
        &[("first.ash", ""), ("second.ash", "")],
    );
    let importer = module_named(&graph, "entry.ash");
    let first = module_named(&graph, "first.ash");
    let second = module_named(&graph, "second.ash");
    let first_summary = ExportSummary::test_fixture(
        first.id(),
        vec![(
            "answer",
            BinderId::resolved(first.id(), 0),
            Type::Unit,
            Origin::Source(first.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );
    let second_summary = ExportSummary::test_fixture(
        second.id(),
        vec![(
            "answer",
            BinderId::resolved(second.id(), 0),
            Type::Unit,
            Origin::Source(second.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&first_summary, &second_summary])
        .expect_err("the second import should conflict");
    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn targeted_term_and_constructor_cannot_share_a_renamed_expression_spelling() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first (answer as Clash)\nimport second (Some as Clash)\n",
        &[("first.ash", ""), ("second.ash", "")],
    );
    let importer = module_named(&graph, "entry.ash");
    let first = module_named(&graph, "first.ash");
    let second = module_named(&graph, "second.ash");
    let first_summary = ExportSummary::test_fixture(
        first.id(),
        vec![(
            "answer",
            BinderId::resolved(first.id(), 0),
            Type::Unit,
            Origin::Source(first.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );
    let nominal = NominalTypeId::new(second.id(), 0);
    let second_summary = ExportSummary::test_fixture(
        second.id(),
        vec![],
        vec![],
        vec![(
            "Some",
            ConstructorId::new(nominal, 0),
            None,
            Origin::Source(second.surface().span),
        )],
        vec![],
    );

    let error = resolve_with(importer, &[&first_summary, &second_summary])
        .expect_err("term and constructor imports must not shadow in expression scope");
    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn targeted_term_cannot_shadow_a_local_constructor() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (answer as Some)\ntype Option = Some\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "answer",
            BinderId::resolved(dependency.id(), 0),
            Type::Unit,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary])
        .expect_err("an imported term must not shadow a local constructor");
    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn targeted_import_cannot_shadow_a_local_global() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (main)\nmain : Unit -> Unit\nmain value = value\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "main",
            BinderId::resolved(dependency.id(), 0),
            Type::Unit,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary]).expect_err("the local should conflict");
    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn local_interface_cannot_shadow_a_qualified_module_alias() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Equal\ninterface Equal<A> {\nequal : A -> Bool\n}\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(dependency.id(), vec![], vec![], vec![], vec![]);

    let error = resolve_with(importer, &[&summary])
        .expect_err("a local interface must not shadow a qualified module alias");

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn local_interface_cannot_shadow_a_targeted_nominal() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Equal)\ninterface Equal<A> {\nequal : A -> Bool\n}\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Equal",
            NominalTypeId::new(dependency.id(), 0),
            ExportedTypeAccess::Transparent,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary])
        .expect_err("a local interface must not shadow a targeted nominal");

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn local_method_cannot_shadow_a_targeted_global_term() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (equal)\ninterface Equal<A> {\nequal : A -> Bool\n}\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "equal",
            BinderId::resolved(dependency.id(), 0),
            Type::Unit,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary])
        .expect_err("a local method must not shadow a targeted global term");

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn local_method_cannot_shadow_a_targeted_constructor_under_a_lowercase_rename() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Some as equal)\ninterface Equal<A> {\nequal : A -> Bool\n}\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Option",
            nominal,
            ExportedTypeAccess::Transparent,
            Origin::Source(dependency.surface().span),
        )],
        vec![(
            "Some",
            ConstructorId::new(nominal, 0),
            None,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
    );

    let error = resolve_with(importer, &[&summary])
        .expect_err("a local method must not shadow a targeted renamed constructor");

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn imported_non_interface_targets_report_interface_kind() {
    for (entry, label) in [
        (
            "import dependency (Make)\nvalue : Unit -> Bool where Make<Int>\nvalue () = true\n",
            "targeted constructor",
        ),
        (
            "import dependency as Dep\nvalue : Unit -> Bool where Dep.Make<Int>\nvalue () = true\n",
            "qualified constructor",
        ),
        (
            "import dependency as Dep\nvalue : Unit -> Bool where Dep<Int>\nvalue () = true\n",
            "unqualified module alias",
        ),
    ] {
        let tree = TempTree::create();
        let graph = load(&tree, entry, &[("dependency.ash", "")]);
        let dependency = module_named(&graph, "dependency.ash");
        let importer = module_named(&graph, "entry.ash");
        let nominal = NominalTypeId::new(dependency.id(), 0);
        let origin = Origin::Source(dependency.surface().span);
        let summary = ExportSummary::test_fixture(
            dependency.id(),
            vec![],
            vec![(
                "Carrier",
                nominal,
                ExportedTypeAccess::Transparent,
                origin.clone(),
            )],
            vec![("Make", ConstructorId::new(nominal, 0), None, origin)],
            vec![],
        );

        let error = resolve_with(importer, &[&summary])
            .expect_err("a resolved non-interface target should fail its sort check");

        assert_eq!(error.reason, ResolveReason::InterfaceKind, "{label}");
    }
}

#[test]
fn local_interface_and_nominal_report_a_duplicate_type() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "type Equal = Equal\n\ninterface Equal<A> {\nequal : A -> Bool\n}\n",
        &[],
    );
    let importer = module_named(&graph, "entry.ash");

    let error = resolve_with(importer, &[])
        .expect_err("a local interface and nominal cannot share a type namespace name");

    assert_eq!(error.reason, ResolveReason::DuplicateType);
}

#[test]
fn local_method_and_global_report_a_duplicate_global() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "interface Equal<A> {\nequal : A -> Bool\n}\n\nequal : Unit -> Bool\nequal () = true\n",
        &[],
    );
    let importer = module_named(&graph, "entry.ash");

    let error = resolve_with(importer, &[])
        .expect_err("a local method and global cannot share a term namespace name");

    assert_eq!(error.reason, ResolveReason::DuplicateGlobal);
}

#[test]
fn a_renamed_imported_type_does_not_conflict_with_a_local_global() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Token as token)\n",
            "token : Unit -> Unit\n",
            "token value = value\n",
        ),
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Token",
            nominal,
            ExportedTypeAccess::Transparent,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
    );

    resolve_with(importer, &[&summary])
        .expect("the nominal and expression namespaces should remain distinct");
}

#[test]
fn qualified_import_charges_withheld_namespace_retention() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Dependency\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary =
        ExportSummary::test_fixture(dependency.id(), vec![], vec![], vec![], vec!["private"]);
    let dependencies = importer
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, &summary).expect("matching summary"))
        .collect::<Vec<_>>();
    let mut resolver = Resolver::with_type_work(importer.id(), TypeWorkBudget::with_limit(2));

    let error = resolver
        .install_imports(importer.surface(), &dependencies)
        .expect_err("three withheld namespace entries should exceed two retained units");

    assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
    assert!(resolver.module_aliases.is_empty());
}

#[test]
fn selecting_a_withheld_private_spelling_reports_unavailable_export() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (secret)\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![],
        vec![],
        vec![],
        vec!["secret"],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary]).expect_err("private export should fail");
    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn diamond_consumers_preserve_one_shared_binder_and_nominal_identity() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import left as Left\nimport right as Right\n",
        &[
            (
                "left.ash",
                concat!(
                    "import shared as Shared\n",
                    "left : Shared.Token -> Shared.Token\n",
                    "left value = Shared.identity\n",
                ),
            ),
            (
                "right.ash",
                concat!(
                    "import shared as Shared\n",
                    "right : Shared.Token -> Shared.Token\n",
                    "right value = Shared.identity\n",
                ),
            ),
            ("shared.ash", ""),
        ],
    );
    let shared = module_named(&graph, "shared.ash");
    let left = module_named(&graph, "left.ash");
    let right = module_named(&graph, "right.ash");
    let binder = BinderId::resolved(shared.id(), 4);
    let nominal = NominalTypeId::new(shared.id(), 2);
    let origin = Origin::Source(shared.surface().span);
    let summary = ExportSummary::test_fixture(
        shared.id(),
        vec![("identity", binder, Type::Unit, origin.clone())],
        vec![("Token", nominal, ExportedTypeAccess::Opaque, origin)],
        vec![],
        vec![],
    );

    let left_resolved = resolve_with(left, &[&summary]).expect("left should resolve");
    let right_resolved = resolve_with(right, &[&summary]).expect("right should resolve");
    let left_definition = equational(&left_resolved, 0);
    let right_definition = equational(&right_resolved, 0);

    assert_eq!(
        nominal_function_parts(&left_definition.interface.annotation.ty),
        (nominal, nominal)
    );
    assert_eq!(
        nominal_function_parts(&right_definition.interface.annotation.ty),
        (nominal, nominal)
    );
    assert!(matches!(
        left_definition.equations[0].body.kind,
        ResolvedExprKind::Occurrence(ref occurrence)
            if occurrence.global_binder() == Some(binder)
    ));
    assert!(matches!(
        right_definition.equations[0].body.kind,
        ResolvedExprKind::Occurrence(ref occurrence)
            if occurrence.global_binder() == Some(binder)
    ));
}

fn opaque_nominal_summary(
    dependency: &LoadedModule,
    nominal_spelling: &str,
    opaque_constructors: Vec<&str>,
) -> ExportSummary {
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let origin = Origin::Source(dependency.surface().span);
    ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![],
        vec![(
            nominal_spelling,
            nominal,
            ExportedTypeAccess::Opaque,
            origin.clone(),
        )],
        vec![],
        vec![],
        opaque_constructors
            .into_iter()
            .map(|spelling| (spelling, origin.clone()))
            .collect(),
        vec![],
    )
}

#[test]
fn targeted_import_of_an_opaque_constructor_reports_opaque_access() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Seal)\n",
        &[("dependency.ash", "pub opaque type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = opaque_nominal_summary(dependency, "Token", vec!["Seal"]);

    let error = resolve_with(importer, &[&summary])
        .expect_err("an opaque constructor cannot be imported by name");

    assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
}

#[test]
fn qualified_construction_of_an_opaque_type_reports_opaque_access() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Unit -> Dep.Token\n",
            "main () = Dep.Seal(1)\n",
        ),
        &[("dependency.ash", "pub opaque type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = opaque_nominal_summary(dependency, "Token", vec!["Seal"]);

    let error = resolve_with(importer, &[&summary])
        .expect_err("qualified construction must not inspect an opaque type");

    assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().source(),
        dependency.surface().span.source()
    );
}

#[test]
fn qualified_pattern_on_an_opaque_type_reports_opaque_access() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Dep.Token -> Unit\n",
            "main Dep.Seal(_) = ()\n",
        ),
        &[("dependency.ash", "pub opaque type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = opaque_nominal_summary(dependency, "Token", vec!["Seal"]);

    let error = resolve_with(importer, &[&summary])
        .expect_err("qualified matching must not inspect an opaque type");

    assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
}

#[test]
fn a_private_type_name_remains_unavailable_to_a_qualified_importer() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Dep.Hidden -> Unit\n",
            "main _ = ()\n",
        ),
        &[("dependency.ash", "type Hidden = Hidden(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary =
        ExportSummary::test_fixture(dependency.id(), vec![], vec![], vec![], vec!["Hidden"]);

    let error = resolve_with(importer, &[&summary])
        .expect_err("a private type name must not enter the qualified namespace");

    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn a_public_opaque_type_name_is_available_to_a_qualified_importer() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Dep.Token -> Dep.Token\n",
            "main value = value\n",
        ),
        &[("dependency.ash", "pub opaque type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let summary = opaque_nominal_summary(dependency, "Token", vec!["Seal"]);

    let resolved =
        resolve_with(importer, &[&summary]).expect("an opaque nominal name should be usable");

    assert_eq!(
        nominal_function_parts(&equational(&resolved, 0).interface.annotation.ty),
        (nominal, nominal)
    );
}

#[test]
fn a_public_transparent_constructor_is_available_in_terms_and_patterns() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Dep.Token -> Dep.Token\n",
            "main Dep.Seal(value) = Dep.Seal(value)\n",
        ),
        &[("dependency.ash", "pub type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Token",
            nominal,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Seal", constructor, Some(Type::Int), origin)],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary])
        .expect("a transparent constructor should resolve in terms and patterns");
    let definition = equational(&resolved, 0);

    assert!(matches!(
        definition.equations[0].patterns[0].kind,
        ResolvedPatternKind::Constructor {
            constructor: found,
            ..
        } if found == constructor
    ));
    let ResolvedExprKind::Apply(application) = &definition.equations[0].body.kind else {
        panic!("expected a constructor application");
    };
    assert!(matches!(
        application.function.kind,
        ResolvedExprKind::Constructor(ref occurrence) if occurrence.constructor == constructor
    ));
}

#[test]
fn targeting_only_a_transparent_constructor_retains_its_owner_metadata() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Seal)\n",
            "main : Unit -> Unit\n",
            "main () = Seal(1)\n",
        ),
        &[("dependency.ash", "pub type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Token",
            nominal,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Seal", constructor, Some(Type::Int), origin)],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary])
        .expect("a targeted constructor should retain its semantic owner");

    assert!(resolved.imported_facts().nominal(nominal).is_some());
    assert!(resolved.imported_facts().constructor(constructor).is_some());
}

#[test]
fn same_spelled_opaque_type_imports_but_its_constructor_remains_inaccessible() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Token)\n",
            "main : Unit -> Token\n",
            "main () = Token\n",
        ),
        &[("dependency.ash", "pub opaque type Token = Token\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![],
        vec![("Token", nominal, ExportedTypeAccess::Opaque, origin.clone())],
        vec![],
        vec![],
        vec![("Token", origin)],
        vec![],
    );

    let error = resolve_with(importer, &[&summary])
        .expect_err("the selector imports the type but not its opaque constructor");

    assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
}

fn hidden_scheme_summary(
    dependency: &LoadedModule,
    term_spelling: &str,
    hidden_spelling: &str,
    declaration: u32,
) -> (ExportSummary, NominalTypeId) {
    let hidden = NominalTypeId::new(dependency.id(), declaration);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![(
            term_spelling,
            BinderId::resolved(dependency.id(), declaration),
            Type::Function(Box::new(Type::Unit), Box::new(Type::Nominal(hidden))),
            origin.clone(),
        )],
        vec![],
        vec![],
        vec![hidden_spelling],
        vec![],
        vec![(hidden_spelling, hidden, 0, true, origin)],
    );
    (summary, hidden)
}

#[test]
fn a_hidden_nominal_in_a_public_scheme_is_retained_without_becoming_nameable() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (make)\n",
            "main : Unit -> Unit\n",
            "main () = make\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "type Hidden = Hidden(Int)\n",
                "pub make : Unit -> Hidden\n",
                "make () = Hidden(1)\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let (summary, hidden) = hidden_scheme_summary(dependency, "make", "Hidden", 0);

    let resolved = resolve_with(importer, &[&summary])
        .expect("the public term should carry its hidden nominal identity");

    let hidden_fact = resolved
        .imported_facts()
        .nominal(hidden)
        .expect("the hidden identity should remain available to checking");
    assert_eq!(
        hidden_fact.display_name("Dependency"),
        "Dependency.<private Hidden>"
    );
    assert!(summary.nominal("Hidden").is_none());

    let naming_tree = TempTree::create();
    let naming_graph = load(
        &naming_tree,
        concat!(
            "import dependency as Dep\n",
            "name_hidden : Dep.Hidden -> Unit\n",
            "name_hidden _ = ()\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "type Hidden = Hidden(Int)\n",
                "pub make : Unit -> Hidden\n",
                "make () = Hidden(1)\n",
            ),
        )],
    );
    let naming_dependency = module_named(&naming_graph, "dependency.ash");
    let naming_importer = module_named(&naming_graph, "entry.ash");
    let (naming_summary, _) = hidden_scheme_summary(naming_dependency, "make", "Hidden", 0);
    let error = resolve_with(naming_importer, &[&naming_summary])
        .expect_err("hidden metadata must not add a source type binding");

    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn a_public_transparent_nominal_in_a_targeted_term_scheme_is_hidden() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (make)\nmain : Unit -> Unit\nmain () = ()\n",
        &[(
            "dependency.ash",
            "pub type Choice =\nFirst\n| Second\npub make : Unit -> Choice\nmake () = First\n",
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let choice = NominalTypeId::new(dependency.id(), 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "make",
            BinderId::resolved(dependency.id(), 0),
            Type::Function(Box::new(Type::Unit), Box::new(Type::Nominal(choice))),
            origin.clone(),
        )],
        vec![("Choice", choice, ExportedTypeAccess::Transparent, origin)],
        vec![],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary])
        .expect("a targeted term should retain its transparent nominal identity");
    let fact = resolved
        .imported_facts()
        .nominal(choice)
        .expect("the scheme nominal should be retained");

    assert_eq!(fact.access, ImportedTypeAccess::Hidden);
    assert!(fact.constructors.is_empty());
}

#[test]
fn scheme_only_nominal_retention_charges_only_hidden_metadata() {
    let tree = TempTree::create();
    let graph = load(&tree, "", &[]);
    let module = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(module.id(), 0);
    let constructors = (0..32)
        .map(|index| ConstructorId::new(nominal, index))
        .collect::<Vec<_>>();
    let origin = Origin::Source(module.surface().span);
    let mut exact = Resolver::with_type_work(module.id(), TypeWorkBudget::with_limit(0));

    exact
        .retain_scheme_nominal_fact(
            ImportedNominalFactRef {
                id: nominal,
                parameter_count: 0,
                parameters: &[],
                constructors: &constructors,
                access: ImportedTypeAccess::Transparent,
                display_spelling: Some("Wide"),
                display_is_private: false,
                origin: &origin,
            },
            module.surface().span,
        )
        .expect("unretained constructors must not consume hidden-metadata work");
    assert!(
        exact
            .imported
            .nominal(nominal)
            .is_some_and(|fact| fact.constructors.is_empty())
    );

    let parameter = ResolvedTypeVariable {
        id: TypeVariableId::resolved(module.id(), 0),
        spelling: "A".to_owned(),
        origin: origin.clone(),
    };
    let mut short = Resolver::with_type_work(module.id(), TypeWorkBudget::with_limit(0));
    let error = short
        .retain_scheme_nominal_fact(
            ImportedNominalFactRef {
                id: nominal,
                parameter_count: 1,
                parameters: std::slice::from_ref(&parameter),
                constructors: &constructors,
                access: ImportedTypeAccess::Transparent,
                display_spelling: Some("Wide"),
                display_is_private: false,
                origin: &origin,
            },
            module.surface().span,
        )
        .expect_err("one retained parameter must consume one hidden-metadata unit");

    assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
}

#[test]
fn hidden_nominals_from_distinct_dependencies_retain_distinct_identities() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first as First\nimport second as Second\n",
        &[
            (
                "first.ash",
                "type Hidden = Hidden\npub make : Unit -> Hidden\nmake () = Hidden\n",
            ),
            (
                "second.ash",
                "type Hidden = Hidden\npub make : Unit -> Hidden\nmake () = Hidden\n",
            ),
        ],
    );
    let importer = module_named(&graph, "entry.ash");
    let first = module_named(&graph, "first.ash");
    let second = module_named(&graph, "second.ash");
    let (first_summary, first_hidden) = hidden_scheme_summary(first, "make", "Hidden", 0);
    let (second_summary, second_hidden) = hidden_scheme_summary(second, "make", "Hidden", 0);

    let resolved = resolve_with(importer, &[&first_summary, &second_summary])
        .expect("both hidden nominal facts should survive import installation");

    assert_ne!(first_hidden, second_hidden);
    assert!(resolved.imported_facts().nominal(first_hidden).is_some());
    assert!(resolved.imported_facts().nominal(second_hidden).is_some());
}

#[test]
fn direct_nominal_access_upgrades_the_same_identity_reached_hidden_in_either_import_order() {
    for entry_text in [
        "import carrier as Carrier\nimport owner as Owner\n",
        "import owner as Owner\nimport carrier as Carrier\n",
    ] {
        let tree = TempTree::create();
        let graph = load(
            &tree,
            entry_text,
            &[
                ("carrier.ash", "import owner as Owner\n"),
                ("owner.ash", "pub type Token = Token\n"),
            ],
        );
        let importer = module_named(&graph, "entry.ash");
        let carrier = module_named(&graph, "carrier.ash");
        let owner = module_named(&graph, "owner.ash");
        let token = NominalTypeId::new(owner.id(), 0);
        let owner_origin = Origin::Source(owner.surface().span);
        let carrier_summary = ExportSummary::test_fixture_with_access(
            carrier.id(),
            vec![(
                "carry",
                BinderId::resolved(carrier.id(), 0),
                Type::Function(
                    Box::new(Type::Nominal(token)),
                    Box::new(Type::Nominal(token)),
                ),
                Origin::Source(carrier.surface().span),
            )],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![("Token", token, 0, false, owner_origin.clone())],
        );
        let owner_summary = ExportSummary::test_fixture(
            owner.id(),
            vec![],
            vec![(
                "Token",
                token,
                ExportedTypeAccess::Transparent,
                owner_origin,
            )],
            vec![],
            vec![],
        );
        let summaries = if entry_text.starts_with("import carrier") {
            vec![&carrier_summary, &owner_summary]
        } else {
            vec![&owner_summary, &carrier_summary]
        };

        let resolved = resolve_with(importer, &summaries)
            .expect("access should merge by identity rather than first route");
        let fact = resolved
            .imported_facts()
            .nominal(token)
            .expect("the shared identity should be retained");

        assert_eq!(fact.access, ImportedTypeAccess::Transparent);
        assert_eq!(fact.display_spelling.as_deref(), Some("Token"));
    }
}

#[test]
fn withheld_type_and_constructor_facts_with_one_spelling_keep_their_namespaces() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Dep\nmain : Dep.Foo -> Unit\nmain _ = ()\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![],
        vec![],
        vec![],
        vec!["Foo"],
        vec![("Foo", Origin::Source(dependency.surface().span))],
        vec![],
    );

    let type_error = resolve_with(importer, &[&summary])
        .expect_err("the private nominal must remain unavailable");
    assert_eq!(type_error.reason, ResolveReason::UnavailableExport);

    let expression_tree = TempTree::create();
    let expression_graph = load(
        &expression_tree,
        "import dependency as Dep\nmain : Unit -> Unit\nmain () = Dep.Foo\n",
        &[("dependency.ash", "")],
    );
    let expression_dependency = module_named(&expression_graph, "dependency.ash");
    let expression_importer = module_named(&expression_graph, "entry.ash");
    let expression_summary = ExportSummary::test_fixture_with_access(
        expression_dependency.id(),
        vec![],
        vec![],
        vec![],
        vec!["Foo"],
        vec![("Foo", Origin::Source(expression_dependency.surface().span))],
        vec![],
    );

    let constructor_error = resolve_with(expression_importer, &[&expression_summary])
        .expect_err("the opaque constructor must retain its own denial");
    assert_eq!(constructor_error.reason, ResolveReason::OpaqueConstructor);
}

#[test]
fn a_local_constructor_wins_over_a_targeted_opaque_marker_with_the_same_spelling() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Token as Clash)\n",
            "type Local = Clash\n",
            "main : Local -> Local\n",
            "main Clash = Clash\n",
        ),
        &[("dependency.ash", "pub opaque type Token = Token\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = opaque_nominal_summary(dependency, "Token", vec!["Token"]);

    resolve_with(importer, &[&summary])
        .expect("an accessible local constructor must take precedence over a denial marker");
}

#[test]
fn targeted_public_constructor_does_not_block_a_same_spelled_type_parameter() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Foo)\nmain : Foo -> Unit\nmain _ = ()\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let owner = NominalTypeId::new(dependency.id(), 1);
    let constructor = ConstructorId::new(owner, 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Bar",
            owner,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Foo", constructor, None, origin)],
        vec!["Foo"],
    );

    let resolved = resolve_with(importer, &[&summary])
        .expect("withheld diagnostic metadata must not bind the type namespace");
    let definition = equational(&resolved, 0);

    assert_eq!(definition.interface.type_parameters.len(), 1);
    assert!(matches!(
        definition.interface.annotation.ty,
        Type::Function(ref domain, _) if matches!(domain.as_ref(), Type::Variable(_))
    ));
}
