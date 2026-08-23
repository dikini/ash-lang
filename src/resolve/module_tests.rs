use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use crate::{
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolved::{
        BinderId, ExportSummary, ExportedTypeAccess, ResolvedDefinitionKind, ResolvedExprKind,
        ResolvedModule, ResolvedPatternKind,
    },
    source::Origin,
    types::{ConstructorId, NominalTypeId, Type},
};

use super::{DependencyExports, ResolveError, ResolveReason, resolve_module};

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
        ResolvedExprKind::Occurrence(ref occurrence) if occurrence.binder == binder
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
            if occurrence.spelling == "renamed" && occurrence.binder == binder
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
fn selecting_a_withheld_private_spelling_reports_unavailable_export() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (secret)\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary =
        ExportSummary::test_fixture(dependency.id(), vec![], vec![], vec![], vec!["secret"]);

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
        ResolvedExprKind::Occurrence(ref occurrence) if occurrence.binder == binder
    ));
    assert!(matches!(
        right_definition.equations[0].body.kind,
        ResolvedExprKind::Occurrence(ref occurrence) if occurrence.binder == binder
    ));
}
