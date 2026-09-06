use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::check_module,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct Tree(PathBuf);

impl Tree {
    fn new() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-resource-modules-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("fixture directory: {error}"),
            }
        }
    }

    fn write(&self, name: &str, source: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, source).expect("fixture source");
        path
    }
}

impl Drop for Tree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn check(graph: &ModuleGraph) -> Vec<CheckedModule> {
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let owner = checked
                    .iter()
                    .find(|module| module.module() == edge.target())
                    .expect("dependency order");
                DependencyExports::new(edge, owner.exports()).expect("authentic summary")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies).expect("resolved builtin API");
        checked.push(check_module(resolved).expect("checked builtin API"));
    }
    checked
}

#[test]
fn builtin_cell_import_supports_qualified_generic_forwarding() {
    let tree = Tree::new();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import @builtin.cell as Cell\n",
            "forward<R> : Cell.Handle<R> -> Int ! {Cell.Ops<R>} where Cell.Provider<R>\n",
            "forward value = Cell.read value\n",
            "main : Unit -> Int\nmain () = 42\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("compiler builtin loads without a configured root");
    assert_eq!(graph.modules().len(), 2);
    assert_eq!(check(&graph).len(), 2);
}

#[test]
fn builtin_root_conflict_precedes_filesystem_inspection() {
    let tree = Tree::new();
    let failure = ModuleRoots::new([
        ("ordinary", tree.0.join("missing")),
        ("builtin", tree.0.clone()),
    ])
    .expect_err("builtin is reserved");
    assert_eq!(failure.to_string(), "invocation.reserved-root");
    assert_eq!(failure.path(), None);
}

#[test]
fn unknown_builtin_paths_reject() {
    let tree = Tree::new();
    for path in ["@builtin.other", "@builtin.cell.extra"] {
        let entry = tree.write("entry.ash", &format!("import {path} as Cell\n"));
        let failure =
            load_module_graph(&entry, &ModuleRoots::empty()).expect_err("only the cell API exists");
        assert_eq!(failure.to_string(), "module.unknown-builtin");
        assert!(failure.is_source_rejection());
    }
}

#[test]
fn ordinary_cell_shaped_api_has_no_privileged_origin() {
    let tree = Tree::new();
    tree.write("cell.ash", concat!(
        "pub opaque type Handle<R> = Hidden\n",
        "pub effect Ops<R> {\nread : Handle<R> -> Int\nwrite : (Handle<R>, Int) -> Unit\n}\n",
        "pub interface Provider<R> {\nread : Handle<R> -> Int ! {Ops<R>}\nwrite : (Handle<R>, Int) -> Unit ! {Ops<R>}\n}\n",
        "pub make<R> : Unit -> Handle<R>\nmake () = Hidden\n",
        "impl Provider<Int> {\nread value = 1\nwrite value = ()\n}\n",
    ));
    let entry = tree.write(
        "entry.ash",
        "import cell as Cell\nmain : Unit -> Int\nmain () = 42\n",
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    check(&graph);
}

#[test]
fn builtin_names_can_be_targeted_renamed_and_forwarded_through_facades() {
    let tree = Tree::new();
    tree.write("facade.ash", "pub import @builtin.cell (Handle as Access, Provider as Supply, Ops as Requests, read as get, write as put)\n");
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import facade (Access, Supply, Requests, get, put)\n",
            "forward<R> : (Access<R>, Int) -> Int ! {Requests<R>} where Supply<R>\n",
            "forward (value, next) = {\nlet _ = put (value, next)\nget value\n}\n",
            "main : Unit -> Int\nmain () = 42\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    assert_eq!(check(&graph).len(), 3);
}

#[test]
fn source_cannot_introduce_the_builtin_provider() {
    let tree = Tree::new();
    for declaration in [
        "impl Cell.Provider<Int> {\nread value = 1\nwrite value = ()\n}\n",
        "main : Unit -> Int\nmain () = {\nnewtype Local = Local(Int)\nwith Cell.Provider<Local> {\nread value = 1\nwrite value = ()\n}\n42\n}\n",
    ] {
        let entry = tree.write(
            "entry.ash",
            &format!("import @builtin.cell as Cell\n{declaration}"),
        );
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        let builtin = &graph.modules()[0];
        let checked = check_module(resolve_module(builtin, &[]).unwrap()).unwrap();
        let entry = graph.module(graph.entry()).unwrap();
        let dependency =
            DependencyExports::new(&entry.dependencies()[0], checked.exports()).unwrap();
        let error = resolve_module(entry, &[dependency]).expect_err("builtin provider is sealed");
        assert!(format!("{error:?}").contains("SealedProvider"), "{error:?}");
    }
}

#[test]
fn acquisition_resolution_requires_a_direct_builtin_dependency() {
    let tree = Tree::new();
    let entry = tree.write(
        "entry.ash",
        "main : Unit -> Int\nmain () = resource cell<R> c = 41 {\n42\n}\n",
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    let error = resolve_module(graph.module(graph.entry()).unwrap(), &[])
        .expect_err("a direct builtin dependency is required");
    assert!(
        format!("{error:?}").contains("ResourceBuiltinRequired"),
        "{error:?}"
    );
}

#[test]
fn direct_targeted_import_satisfies_acquisition_availability_but_a_facade_does_not() {
    let tree = Tree::new();
    tree.write("facade.ash", "pub import @builtin.cell (Handle)\n");
    for import in ["@builtin.cell", "facade"] {
        let entry = tree.write("entry.ash", &format!("import {import} (Handle)\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {{\n42\n}}\n"));
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        let mut checked: Vec<CheckedModule> = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|owner| owner.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let result = resolve_module(module, &dependencies);
            if module.id() == graph.entry() {
                if import == "@builtin.cell" {
                    check_module(result.unwrap()).unwrap();
                } else {
                    let error = format!("{:?}", result.unwrap_err());
                    assert!(error.contains("ResourceBuiltinRequired"), "{error}");
                }
            } else {
                checked.push(check_module(result.unwrap()).unwrap());
            }
        }
    }
}

#[test]
fn source_has_no_builtin_handle_constructor_or_pattern() {
    let tree = Tree::new();
    for declaration in [
        "make<R> : Unit -> Cell.Handle<R>\nmake () = Cell.Hidden\n",
        "inspect<R> : Cell.Handle<R> -> Int\ninspect value = match value {\nCell.Hidden => 42\n}\n",
        "make<R> : Unit -> Cell.Handle<R>\nmake () = Cell.Handle 42\n",
    ] {
        let entry = tree.write(
            "entry.ash",
            &format!("import @builtin.cell as Cell\n{declaration}"),
        );
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        let builtin = &graph.modules()[0];
        let checked = check_module(resolve_module(builtin, &[]).unwrap()).unwrap();
        let entry = graph.module(graph.entry()).unwrap();
        let dependency =
            DependencyExports::new(&entry.dependencies()[0], checked.exports()).unwrap();
        assert!(resolve_module(entry, &[dependency]).is_err());
    }
}

#[test]
fn cli_preserves_builtin_failure_categories_and_resource_execution() {
    let tree = Tree::new();
    for (source, code, prefix) in [
        (
            "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = 42\n",
            0,
            "",
        ),
        (
            "import @builtin.unknown as Cell\n",
            1,
            "module.unknown-builtin\n",
        ),
        (
            "import @builtin.cell (Handle)\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\n42\n}\n",
            0,
            "",
        ),
    ] {
        let entry = tree.write("entry.ash", source);
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_ash"))
            .arg(&entry)
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(code),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stderr).starts_with(prefix));
        if code == 0 {
            assert_eq!(output.stdout, b"42 : Int\n");
            assert!(output.stderr.is_empty());
        }
    }
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg("--root")
        .arg(format!("ordinary={}", tree.0.join("missing").display()))
        .arg("--root")
        .arg(format!("builtin={}", tree.0.display()))
        .arg(tree.0.join("also-missing.ash"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stderr.starts_with(b"invocation.reserved-root\n"));
}

#[test]
fn direct_and_facade_paths_share_one_builtin_identity() {
    let tree = Tree::new();
    tree.write("facade.ash", "pub import @builtin.cell (Handle)\n");
    let entry = tree.write("entry.ash", "import facade as Wrapped\nimport @builtin.cell as Direct\nforward<R> : Wrapped.Handle<R> -> Direct.Handle<R>\nforward value = value\nmain : Unit -> Int\nmain () = 42\n");
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    assert_eq!(graph.modules().len(), 3);
    let builtin = graph.modules()[0].id();
    assert_eq!(graph.modules()[1].dependencies()[0].target(), builtin);
    assert_eq!(
        graph.module(graph.entry()).unwrap().dependencies()[1].target(),
        builtin
    );
    check(&graph);
}
