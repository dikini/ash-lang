use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::check_module,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
};

static NEXT_TREE: AtomicU64 = AtomicU64::new(0);

struct Tree(PathBuf);

impl Tree {
    fn new() -> Self {
        loop {
            let path = std::env::temp_dir().join(format!(
                "ash-resource-typing-{}-{}",
                std::process::id(),
                NEXT_TREE.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("fixture directory: {error}"),
            }
        }
    }

    fn check(&self, source: &str) -> Result<(), String> {
        let entry = self.0.join("entry.ash");
        fs::write(&entry, source).unwrap();
        let graph = load_module_graph(&entry, &ModuleRoots::empty())
            .map_err(|error| format!("{error:?}"))?;
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
                            .find(|checked| checked.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let resolved =
                resolve_module(module, &dependencies).map_err(|error| format!("{error:?}"))?;
            checked.push(check_module(resolved).map_err(|error| format!("{error:?}"))?);
        }
        Ok(())
    }
}

impl Drop for Tree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn acquisition_checks_direct_read_write_and_generic_forwarding() {
    let tree = Tree::new();
    for body in [
        "Cell.read c",
        "let _ = Cell.write (c, 42)\nCell.read c",
        "forward c",
    ] {
        let source = format!(
            "import @builtin.cell as Cell\nforward<R> : Cell.Handle<R> -> Int ! {{Cell.Ops<R>}} where Cell.Provider<R>\nforward value = Cell.read value\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {{\n{body}\n}}\n"
        );
        let error = tree.check(&source).unwrap_err();
        assert!(
            error.contains("ResourceProofUnavailable"),
            "{body}: {error}"
        );
    }
}

#[test]
fn acquisition_checks_with_only_handle_or_read_selected() {
    let tree = Tree::new();
    for (selected, body) in [("Handle", "42"), ("read", "read c")] {
        let error = tree.check(&format!("import @builtin.cell ({selected})\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {{\n{body}\n}}\n")).unwrap_err();
        assert!(
            error.contains("ResourceProofUnavailable"),
            "{selected}: {error}"
        );
    }
}

#[test]
fn initializer_has_int_type_and_preceding_scope() {
    let tree = Tree::new();
    for (expression, reason) in [
        ("resource cell<R> c = true {\n42\n}", "Mismatch"),
        ("resource cell<R> c = c {\n42\n}", "UnknownName"),
        (
            "resource cell<R> c = ({\nlet x : R = 41\nx\n}) {\n42\n}",
            "UnknownType",
        ),
        (
            "{\nlet _ = resource cell<R> c = 41 {\n42\n}\nc\n}",
            "UnknownName",
        ),
    ] {
        let error = tree
            .check(&format!(
                "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {expression}\n"
            ))
            .unwrap_err();
        assert!(error.contains(reason), "{expression}: {error}");
    }
    let error = tree.check("import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {\nlet c = 41\nresource cell<R> c = c {\nCell.read c\n}\n}\n").unwrap_err();
    assert!(error.contains("ResourceProofUnavailable"), "{error}");
}

#[test]
fn distinct_acquisition_handles_do_not_unify() {
    let tree = Tree::new();
    let error = tree.check("import @builtin.cell as Cell\nsame<R> : (Cell.Handle<R>, Cell.Handle<R>) -> Int ! {Cell.Ops<R>} where Cell.Provider<R>\nsame (left, right) = Cell.read left\nmain : Unit -> Int\nmain () = resource cell<A> a = 1 {\nresource cell<B> b = 2 {\nsame (a, b)\n}\n}\n").unwrap_err();
    assert!(error.contains("Argument"), "{error}");
}

#[test]
fn acquisition_does_not_supply_an_unrelated_provider() {
    let tree = Tree::new();
    let error = tree.check("import @builtin.cell as Cell\nneed : Unit -> Int where Cell.Provider<Int>\nneed () = 42\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\nneed ()\n}\n").unwrap_err();
    assert!(error.contains("Unsatisfied"), "{error}");
}

#[test]
fn acquisition_rejects_exposed_result_and_latent_row_escape() {
    let tree = Tree::new();
    for result in [
        "c",
        "{\nlet read_later : Unit -> Int ! {Cell.Ops<R>} = fn(ignored) {\nCell.read c\n}\nread_later\n}",
    ] {
        let error = tree.check(&format!("import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\n{result}\n}}\n42\n}}\n")).unwrap_err();
        assert!(error.contains("ResourceEscape"), "{result}: {error}");
    }
}

#[test]
fn immediate_outward_row_escape_labels_the_user_computation_not_its_final_value() {
    let tree = Tree::new();
    let source = "import @builtin.cell as Cell\neffect Escape<T> {\n    escape : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\n    let _ = perform Escape<R>.escape ()\n    42\n}\n";
    let entry = tree.0.join("entry.ash");
    fs::write(&entry, source).unwrap();
    let error = ash::driver::run_path(ash::driver::RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .unwrap_err();
    let ash::driver::FileFailure::Pipeline(ash::driver::PipelineFailure::Typing(
        ash::elaborate::TypeError::Source(diagnostic),
    )) = error
    else {
        panic!("resource escape diagnostic: {error:?}")
    };
    assert_eq!(
        diagnostic.reason,
        ash::elaborate::TypeReason::ResourceEscape
    );
    let end = u32::try_from(source.rfind('}').unwrap() + 1).unwrap();
    let body = ash::source::ByteRange::new(
        u32::try_from(source.find("{\n    let").unwrap()).unwrap(),
        end,
    )
    .unwrap();
    let acquisition = ash::source::ByteRange::new(
        u32::try_from(source.find("resource cell").unwrap()).unwrap(),
        end,
    )
    .unwrap();
    assert_eq!(diagnostic.primary.span().range(), body);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span().range(), acquisition);
    assert_eq!(
        diagnostic.primary.span().source(),
        diagnostic.related[0].span().source()
    );
}

#[test]
fn nested_acquisition_checking_uses_a_bounded_stack() {
    const CHILD: &str = "ASH_RESOURCE_CHECK_STACK_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let status = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "nested_acquisition_checking_uses_a_bounded_stack",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .status()
            .unwrap();
        assert!(
            status.success(),
            "fresh-process small-stack resource checking: {status}"
        );
        return;
    }
    std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
        Tree::new().check("effect Ping {\nping : Unit -> Int\n}\nmain : Unit -> Int ! {Ping}\nmain () = perform Ping.ping ()\n").expect("ordinary request control");
        let mut source = String::from("import @builtin.cell (Handle)\nmain : Unit -> Int\nmain () = ");
        for _ in 0..24 { source.push_str("resource cell<R> c = 41 {\n"); }
        source.push_str("42\n");
        for _ in 0..24 { source.push_str("}\n"); }
        let error = Tree::new().check(&source).unwrap_err();
        assert!(error.contains("ResourceProofUnavailable"), "{error}");
    }).unwrap().join().unwrap();
}

#[test]
fn initializer_preserves_outer_effect_instances() {
    let error = Tree::new().check("import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<A> a = 41 {\nresource cell<B> b = (Cell.read a) {\nlet _ = Cell.write (a, 42)\nCell.read b\n}\n}\n").unwrap_err();
    assert!(error.contains("ResourceProofUnavailable"), "{error}");
}

#[test]
fn acquisition_supplies_a_generic_helper_through_a_facade() {
    let tree = Tree::new();
    std::fs::write(tree.0.join("helper.ash"), "import @builtin.cell as Cell\npub forward<R> : Cell.Handle<R> -> Int ! {Cell.Ops<R>} where Cell.Provider<R>\nforward value = Cell.read value\n").unwrap();
    std::fs::write(tree.0.join("facade.ash"), "pub import helper (forward)\n").unwrap();
    for route in ["helper", "facade"] {
        let result = tree.check(&format!("import @builtin.cell (Handle)\nimport {route} (forward)\nmain : Unit -> Int\nmain () = 42\n"));
        result.expect("resource-free mixed-route control");
    }
    let error = tree.check("import @builtin.cell (Handle)\nimport facade (forward)\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\nforward c\n}\n").unwrap_err();
    assert!(error.contains("ResourceProofUnavailable"), "{error}");
}

#[test]
fn resource_rows_are_recomputed_inside_an_enclosing_handler_clause() {
    let error = Tree::new().check("import @builtin.cell as Cell\neffect Ask {\nask : Unit -> Int\n}\nmain : Unit -> Int\nmain () = resource cell<A> a = 1 {\nhandle ({\nlet answer = perform Ask.ask ()\nlet _ = Cell.write (a, answer)\nCell.read a\n}) with Ask {\nask ignored => resource cell<B> b = 41 {\nresume (Cell.read b)\n}\n}\n}\n").unwrap_err();
    assert!(error.contains("ResourceProofUnavailable"), "{error}");
}
