use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    module::{
        LoadGraphError, MODULE_PATH_SEGMENT_LIMIT, MODULE_PENDING_LIMIT, ModuleReason,
        ModuleResource, ModuleRoots, load_module_graph,
    },
    parser::{ResourceFailure, STRUCTURAL_DEPTH_LIMIT},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-module-loading-{}-{id}", std::process::id()));
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

    fn path(&self, relative: &str) -> PathBuf {
        self.0.join(relative)
    }
}

impl Drop for TempTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn display_names(graph: &ash::module::ModuleGraph) -> Vec<String> {
    graph
        .modules()
        .iter()
        .map(|module| {
            Path::new(module.source().display_path())
                .file_name()
                .expect("fixture should have a file name")
                .to_string_lossy()
                .into_owned()
        })
        .collect()
}

#[test]
fn loads_relative_descendants_in_dependency_order() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "import helpers.math as Math\n");
    tree.write("helpers/math.ash", "import constants as Constants\n");
    tree.write("helpers/constants.ash", "");

    let graph = load_module_graph(&entry, &ModuleRoots::empty()).expect("graph should load");

    assert_eq!(
        display_names(&graph),
        ["constants.ash", "math.ash", "entry.ash"]
    );
    assert_eq!(
        graph.modules().last().map(|module| module.id()),
        Some(graph.entry())
    );
}

#[test]
fn separate_compilation_graphs_do_not_reuse_module_identity() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "");

    let first = load_module_graph(&entry, &ModuleRoots::empty()).expect("first graph should load");
    let second =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("second graph should load");

    assert_ne!(first.entry(), second.entry());
}

#[test]
fn loads_an_absolute_path_from_its_named_root() {
    let tree = TempTree::create();
    let entry = tree.write("app/entry.ash", "import @std.collections.list as List\n");
    tree.write("standard/collections/list.ash", "");
    let roots =
        ModuleRoots::new([("std", tree.path("standard"))]).expect("named root should be valid");

    let graph = load_module_graph(&entry, &roots).expect("named graph should load");

    assert_eq!(display_names(&graph), ["list.ash", "entry.ash"]);
}

#[test]
fn a_diamond_admits_one_canonical_shared_module() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "import left as Left\nimport right as Right\n");
    tree.write("left.ash", "import shared as Shared\n");
    tree.write("right.ash", "import shared as Shared\n");
    tree.write("shared.ash", "");

    let graph = load_module_graph(&entry, &ModuleRoots::empty()).expect("diamond should load");

    assert_eq!(graph.modules().len(), 4);
    let shared = graph
        .modules()
        .iter()
        .find(|module| module.source().display_path().ends_with("shared.ash"))
        .expect("shared module should be admitted");
    let incoming = graph
        .modules()
        .iter()
        .flat_map(|module| module.dependencies())
        .filter(|dependency| dependency.target() == shared.id())
        .count();
    assert_eq!(incoming, 2);
}

#[test]
fn overlapping_roots_reuse_one_canonical_module_identity() {
    let tree = TempTree::create();
    let entry = tree.write(
        "app/entry.ash",
        "import @broad.pkg.shared as Broad\nimport @narrow.shared as Narrow\n",
    );
    tree.write("root/pkg/shared.ash", "");
    let roots = ModuleRoots::new([
        ("broad", tree.path("root")),
        ("narrow", tree.path("root/pkg")),
    ])
    .expect("overlapping roots should be configurable");

    let graph = load_module_graph(&entry, &roots).expect("both routes should share a module");

    assert_eq!(graph.modules().len(), 2);
    let entry_module = graph
        .modules()
        .iter()
        .find(|module| module.id() == graph.entry())
        .expect("the entry should remain in the graph");
    assert_eq!(entry_module.dependencies().len(), 2);
    assert_eq!(
        entry_module.dependencies()[0].target(),
        entry_module.dependencies()[1].target()
    );
}

#[test]
fn reports_unknown_roots_missing_files_and_cycles_at_the_module_stage() {
    let tree = TempTree::create();
    let unknown = tree.write("unknown.ash", "import @missing.value as Value\n");
    let missing = tree.write("missing.ash", "import absent as Absent\n");
    let cycle = tree.write("cycle.ash", "import cycle as Cycle\n");

    for (entry, expected) in [
        (unknown, ModuleReason::UnknownRoot),
        (missing, ModuleReason::NotFound),
        (cycle, ModuleReason::ImportCycle),
    ] {
        let failure = load_module_graph(&entry, &ModuleRoots::empty())
            .expect_err("fixture should fail loading");
        assert_eq!(failure.module_reason(), Some(expected));
        assert!(failure.is_source_rejection());
    }
}

#[test]
fn reports_an_indirect_import_cycle() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "import first as First\n");
    tree.write("first.ash", "import second as Second\n");
    tree.write("second.ash", "import first as First\n");

    let failure = load_module_graph(&entry, &ModuleRoots::empty())
        .expect_err("the indirect cycle should be rejected");

    assert_eq!(failure.module_reason(), Some(ModuleReason::ImportCycle));
    assert!(failure.is_source_rejection());
}

#[cfg(unix)]
#[test]
fn alternate_symlink_paths_share_one_module_identity() {
    use std::os::unix::fs::symlink;

    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        "import actual as Actual\nimport alternate as Alternate\n",
    );
    tree.write("actual.ash", "");
    symlink(tree.path("actual.ash"), tree.path("alternate.ash"))
        .expect("fixture symlink should be creatable");

    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("alternate canonical paths should load once");

    assert_eq!(graph.modules().len(), 2);
    let entry_module = graph
        .modules()
        .iter()
        .find(|module| module.id() == graph.entry())
        .expect("the entry should remain in the graph");
    assert_eq!(entry_module.dependencies().len(), 2);
    assert_eq!(
        entry_module.dependencies()[0].target(),
        entry_module.dependencies()[1].target()
    );
}

#[cfg(unix)]
#[test]
fn rejects_a_canonical_target_outside_its_owning_root() {
    use std::os::unix::fs::symlink;

    let tree = TempTree::create();
    let entry = tree.write("root/entry.ash", "import escape.secret as Secret\n");
    tree.write("outside/secret.ash", "");
    symlink(tree.path("outside"), tree.path("root/escape"))
        .expect("fixture symlink should be creatable");

    let failure = load_module_graph(&entry, &ModuleRoots::empty())
        .expect_err("root escape should fail loading");

    assert_eq!(failure.module_reason(), Some(ModuleReason::PathEscape));
    assert!(failure.is_source_rejection());
}

#[cfg(unix)]
#[test]
fn a_new_overlapping_owner_revalidates_existing_relative_edges() {
    use std::os::unix::fs::symlink;

    let tree = TempTree::create();
    let entry = tree.write(
        "app/entry.ash",
        "import @broad.pkg.shared as Broad\nimport @narrow.shared as Narrow\n",
    );
    tree.write("root/pkg/shared.ash", "import escape.child as Child\n");
    tree.write("root/outside/child.ash", "");
    symlink(tree.path("root/outside"), tree.path("root/pkg/escape"))
        .expect("fixture symlink should be creatable");
    let roots = ModuleRoots::new([
        ("broad", tree.path("root")),
        ("narrow", tree.path("root/pkg")),
    ])
    .expect("overlapping roots should be configurable");

    let failure = load_module_graph(&entry, &roots)
        .expect_err("the existing edge should escape the new owner");

    assert_eq!(failure.module_reason(), Some(ModuleReason::PathEscape));
    assert!(failure.is_source_rejection());
}

#[cfg(unix)]
#[test]
fn overlapping_owner_failures_follow_source_order_through_descendants() {
    use std::os::unix::fs::symlink;

    let tree = TempTree::create();
    let entry = tree.write(
        "app/entry.ash",
        "import @broad.pkg.shared as Broad\nimport @narrow.shared as Narrow\n",
    );
    tree.write(
        "root/pkg/shared.ash",
        "import first as First\nimport second as Second\n",
    );
    tree.write("root/pkg/first.ash", "import escape_first.child as Child\n");
    tree.write(
        "root/pkg/second.ash",
        "import escape_second.child as Child\n",
    );
    tree.write("root/outside-first/child.ash", "");
    tree.write("root/outside-second/child.ash", "");
    symlink(
        tree.path("root/outside-first"),
        tree.path("root/pkg/escape_first"),
    )
    .expect("first escape symlink should be creatable");
    symlink(
        tree.path("root/outside-second"),
        tree.path("root/pkg/escape_second"),
    )
    .expect("second escape symlink should be creatable");
    let roots = ModuleRoots::new([
        ("broad", tree.path("root")),
        ("narrow", tree.path("root/pkg")),
    ])
    .expect("overlapping roots should be configurable");

    let failure = load_module_graph(&entry, &roots)
        .expect_err("both descendant branches escape the later owner");

    assert_eq!(failure.module_reason(), Some(ModuleReason::PathEscape));
    assert!(
        failure
            .as_module_failure()
            .and_then(|failure| failure.path())
            .is_some_and(|path| path.ends_with("outside-first/child.ash")),
        "the first source branch should fail first: {failure:?}"
    );
}

#[test]
fn imported_syntax_failures_retain_the_parser_stage() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "import broken as Broken\n");
    tree.write("broken.ash", "import @ as Missing\n");

    let failure = load_module_graph(&entry, &ModuleRoots::empty())
        .expect_err("the imported source should fail parsing");

    assert!(matches!(&failure, LoadGraphError::Syntax(_)));
    assert_eq!(failure.module_reason(), None);
    assert!(failure.is_source_rejection());
}

#[test]
fn imported_syntax_resource_failures_retain_the_rejected_source() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "import deep as Deep\n");
    let nested = format!(
        "main : Unit\nmain () = {}0{}\n",
        "(".repeat(STRUCTURAL_DEPTH_LIMIT + 1),
        ")".repeat(STRUCTURAL_DEPTH_LIMIT + 1)
    );
    let rejected = tree.write("deep.ash", &nested);

    let failure = load_module_graph(&entry, &ModuleRoots::empty())
        .expect_err("the imported source should exhaust structural syntax depth");

    let LoadGraphError::Syntax(failure) = failure else {
        panic!("syntax resources should remain owned by the parser stage");
    };
    assert_eq!(failure.source.display_path(), rejected.to_string_lossy());
    assert_eq!(
        failure.resource,
        Some(ResourceFailure::StructuralDepth {
            limit: STRUCTURAL_DEPTH_LIMIT
        })
    );
    assert!(failure.lexical.is_empty());
    assert!(failure.parser.is_empty());
}

#[test]
fn path_segment_budget_rejects_before_filesystem_resolution() {
    let tree = TempTree::create();
    let mut source = String::with_capacity(MODULE_PATH_SEGMENT_LIMIT * 2 + 32);
    source.push_str("import ");
    for index in 0..=MODULE_PATH_SEGMENT_LIMIT {
        if index > 0 {
            source.push('.');
        }
        source.push('a');
    }
    source.push_str(" as Deep\n");
    let entry = tree.write("entry.ash", &source);

    let failure = load_module_graph(&entry, &ModuleRoots::empty())
        .expect_err("one segment beyond the graph path budget should fail");
    let module = failure
        .as_module_failure()
        .expect("path work should remain a module resource failure");

    assert_eq!(module.reason(), ModuleReason::ResourceLimit);
    assert_eq!(module.resource_kind(), Some(ModuleResource::PathSegments));
    assert!(!module.is_source_rejection());
}

#[test]
fn repeated_canonical_edges_do_not_exhaust_the_active_frame_budget() {
    let tree = TempTree::create();
    let mut source = String::with_capacity(MODULE_PENDING_LIMIT * 30);
    for index in 0..MODULE_PENDING_LIMIT {
        source.push_str(&format!("import shared as M{index}\n"));
    }
    let entry = tree.write("entry.ash", &source);
    tree.write("shared.ash", "");

    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("a two-frame graph should not exhaust the active frame budget");

    assert_eq!(graph.modules().len(), 2);
    let entry = graph
        .module(graph.entry())
        .expect("the entry identity should remain admitted");
    assert_eq!(entry.dependencies().len(), MODULE_PENDING_LIMIT);
}

#[test]
fn dependency_failure_selection_follows_depth_first_source_order() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        "import first as First\nimport malformed as Malformed\n",
    );
    tree.write("first.ash", "import absent as Absent\n");
    tree.write("malformed.ash", "import @ as Missing\n");

    let failure = load_module_graph(&entry, &ModuleRoots::empty())
        .expect_err("both dependency branches should fail");

    assert_eq!(failure.module_reason(), Some(ModuleReason::NotFound));
    assert!(
        failure
            .as_module_failure()
            .and_then(|failure| failure.path())
            .is_some_and(|path| path.ends_with("absent.ash")),
        "the descendant of the first source import should fail first: {failure:?}"
    );
}

#[test]
fn a_deep_dependency_chain_loads_and_drops_on_a_small_stack() {
    const DEPTH: usize = 1_024;

    let tree = TempTree::create();
    for index in 0..DEPTH {
        tree.write(
            &format!("module{index}.ash"),
            &format!("import module{} as Next\n", index + 1),
        );
    }
    tree.write(&format!("module{DEPTH}.ash"), "");
    let entry = tree.path("module0.ash");

    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let graph = load_module_graph(&entry, &ModuleRoots::empty())
                .expect("the explicit graph worklist should admit the deep chain");
            assert_eq!(graph.modules().len(), DEPTH + 1);
        })
        .expect("the small-stack loader thread should start")
        .join()
        .expect("loading and dropping the deep graph should fit the host stack");
}

#[test]
fn duplicate_named_root_configuration_is_an_invocation_failure() {
    let tree = TempTree::create();

    let failure = ModuleRoots::new([("std", tree.path("first")), ("std", tree.path("second"))])
        .expect_err("duplicate root names should fail");

    assert_eq!(failure.reason(), ModuleReason::DuplicateRoot);
    assert!(!failure.is_source_rejection());
}

#[test]
fn root_configuration_rejects_every_reserved_word() {
    let tree = TempTree::create();

    for spelling in [
        "_", "true", "false", "fn", "let", "rec", "and", "type", "match", "import", "as", "pub",
        "opaque", "Int", "Bool", "Unit",
    ] {
        let failure = ModuleRoots::new([(spelling, tree.0.clone())])
            .expect_err("reserved words cannot name a module root");

        assert_eq!(
            failure.reason(),
            ModuleReason::InvalidRootName,
            "{spelling}"
        );
        assert!(!failure.is_source_rejection(), "{spelling}");
    }
}
