use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, run_path},
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveReason, resolve_module},
    resolved::{Binder, ResolvedDefinition, ResolvedDefinitionKind, ResolvedModule},
    types::TYPE_WORK_LIMIT,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-module-resolution-{}-{id}", std::process::id()));
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

fn resolve_leaf(module: &LoadedModule) -> ResolvedModule {
    let dependencies: &[DependencyExports<'_>] = &[];
    resolve_module(module, dependencies).expect("leaf module should resolve")
}

fn definition_binder(definition: &ResolvedDefinition) -> &Binder {
    match &definition.kind {
        ResolvedDefinitionKind::Equational(global) => &global.interface.name,
        ResolvedDefinitionKind::InlineOperational(global) => &global.header.name,
    }
}

#[test]
fn local_binder_numbers_are_qualified_by_their_defining_module() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first as First\nimport second as Second\n",
        &[
            ("first.ash", "same : Unit -> Unit\nsame value = value\n"),
            ("second.ash", "same : Unit -> Unit\nsame value = value\n"),
        ],
    );
    let first = module_named(&graph, "first.ash");
    let second = module_named(&graph, "second.ash");
    let first_resolved = resolve_leaf(first);
    let second_resolved = resolve_leaf(second);
    let first_id = definition_binder(&first_resolved.definitions()[0]).id;
    let second_id = definition_binder(&second_resolved.definitions()[0]).id;

    assert_eq!(first_id.local(), second_id.local());
    assert_ne!(first_id, second_id);
    assert_eq!(first_id.module(), Some(first.id()));
    assert_eq!(second_id.module(), Some(second.id()));
}

#[test]
fn resolved_modules_are_declarations_only() {
    let tree = TempTree::create();
    let graph = load(&tree, "main : Unit -> Int\nmain () = 42\n", &[]);
    let entry = module_named(&graph, "entry.ash");
    let resolved = resolve_leaf(entry);

    assert_eq!(resolved.module(), entry.id());
    assert_eq!(resolved.definitions().len(), 1);
    assert_eq!(resolved.span(), entry.surface().span);
}

#[test]
fn export_candidates_reflect_term_and_type_visibility() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "type Hidden = Hidden(Int)\n",
            "pub opaque type Opaque = Opaque(Int)\n",
            "pub type Visible = Visible(Int)\n",
            "private_value : Unit -> Int\n",
            "private_value () = 0\n",
            "pub public_value : Unit -> Int\n",
            "public_value () = 1\n",
        ),
        &[],
    );
    let resolved = resolve_leaf(module_named(&graph, "entry.ash"));
    let candidate = resolved.export_candidate();

    assert!(candidate.term("private_value").is_none());
    assert!(candidate.term("public_value").is_some());
    assert!(candidate.is_private("private_value"));

    assert!(candidate.nominal("Hidden").is_none());
    assert!(candidate.constructor("Hidden").is_none());
    assert!(candidate.is_private("Hidden"));
    assert!(
        candidate
            .hidden_nominal(resolved.registry().nominals()[0].id)
            .is_some()
    );

    assert!(candidate.nominal("Opaque").is_some());
    assert!(candidate.constructor("Opaque").is_none());
    assert!(candidate.is_opaque_constructor("Opaque"));

    assert!(candidate.nominal("Visible").is_some());
    assert!(candidate.constructor("Visible").is_some());
}

#[test]
fn a_public_inline_operational_global_is_available_to_a_targeted_import() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import operations (increment)\n",
            "main : Unit -> Int\n",
            "main () = increment 41\n",
        ),
    );
    tree.write(
        "operations.ash",
        "pub fn increment(value : Int) -> Int {\n    value + 1\n}\n",
    );

    let observation = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("the public operational term should enter the targeted import scope");

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn duplicate_module_aliases_are_rejected_before_export_lookup() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first as Shared\nimport second as Shared\n",
        &[("first.ash", ""), ("second.ash", "")],
    );
    let entry = module_named(&graph, "entry.ash");
    let no_exports: &[DependencyExports<'_>] = &[];

    let error = resolve_module(entry, no_exports)
        .expect_err("a duplicate alias should fail before dependency export lookup");

    assert_eq!(error.reason, ResolveReason::DuplicateModuleAlias);
}

#[test]
fn export_candidates_keep_withheld_type_and_constructor_namespaces_separate() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!("type Foo = PrivateFoo\n", "pub opaque type Token = Foo\n",),
        &[],
    );
    let resolved = resolve_leaf(module_named(&graph, "entry.ash"));
    let candidate = resolved.export_candidate();

    assert!(candidate.is_private("Foo"));
    assert!(candidate.is_opaque_constructor("Foo"));
}

#[test]
fn repeated_summary_imports_share_one_graph_type_work_budget() {
    const PAYLOAD_WIDTH: usize = 10_000;
    const DEPENDENT_COUNT: usize = TYPE_WORK_LIMIT / PAYLOAD_WIDTH + 2;

    let tree = TempTree::create();
    let mut base = String::with_capacity(PAYLOAD_WIDTH * 5 + 32);
    base.push_str("pub type Wide =\nWide(");
    for index in 0..PAYLOAD_WIDTH {
        if index > 0 {
            base.push_str(", ");
        }
        base.push_str("Int");
    }
    base.push_str(")\n");
    tree.write("base.ash", &base);

    let mut entry = String::new();
    for index in 0..DEPENDENT_COUNT {
        entry.push_str(&format!("import dependency{index} as Dependency{index}\n"));
        tree.write(&format!("dependency{index}.ash"), "import base as Base\n");
    }
    entry.push_str("main : Unit -> Int\nmain () = 0\n");
    let entry = tree.write("entry.ash", &entry);

    let failure = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect_err("repeated dependency-summary retention must share graph type work");

    let FileFailure::Pipeline(PipelineFailure::Resolution(error)) = failure else {
        panic!("graph type work should remain owned by resolution: {failure:?}");
    };
    assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
}
