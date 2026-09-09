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

fn assert_check(outcome: Result<(), String>, expected: Option<&str>) {
    match expected {
        Some(reason) => {
            let error = outcome.unwrap_err();
            assert!(error.contains(reason), "{error}");
        }
        None => outcome.unwrap(),
    }
}

fn assert_opaque_resource_witness(source: &str, escapes: bool) {
    let tree = Tree::new();
    fs::write(tree.0.join("helper.ash"), "pub opaque type Box<A> = Hidden(A)\npub pack<A> : A -> Box<A>\npack value = Hidden value\npub unpack<A> : Box<A> -> A\nunpack (Hidden value) = value\n\n").unwrap();
    let entry = tree.0.join("entry.ash");
    fs::write(&entry, source).unwrap();
    let result = ash::driver::run_path(ash::driver::RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    });
    if escapes {
        assert_eq!(result.unwrap_err().reason_code(), "type.resource-escape");
    } else {
        assert_eq!(result.unwrap().value_display(), "42");
    }
}

#[test]
fn imported_opaque_wrapper_preserves_live_cell_access() {
    assert_opaque_resource_witness(
        "import @builtin.cell as Cell\nimport helper (pack, unpack)\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\nlet hidden = pack c\nlet access = unpack hidden\nlet _ = Cell.write (access, 42)\nCell.read c\n}\n\n",
        false,
    );
}

#[test]
fn imported_opaque_wrapper_allows_copied_closure_escape() {
    assert_opaque_resource_witness(
        "import @builtin.cell as Cell\nimport helper (pack, unpack)\nmain : Unit -> Int\nmain () = {\nlet escaped = resource cell<R> c = 41 {\nlet copied = Cell.read c\nlet later : Unit -> Int = fn(ignored) {\ncopied + 1\n}\npack later\n}\nlet call = unpack escaped\ncall ()\n}\n\n",
        false,
    );
}

#[test]
fn imported_opaque_wrapper_rejects_hidden_resource_closure_escape() {
    assert_opaque_resource_witness(
        "import @builtin.cell as Cell\nimport helper (pack, unpack)\nmain : Unit -> Int\nmain () = {\nlet escaped = resource cell<R> c = 41 {\nlet later : Unit -> Int = fn(ignored) {\nlet held = c\n42\n}\npack later\n}\nlet call = unpack escaped\ncall ()\n}\n\n",
        true,
    );
}

#[test]
fn opaque_request_payload_allows_copied_evidence_after_release() {
    assert_opaque_resource_witness(
        "import @builtin.cell as Cell\nimport helper (Box, pack, unpack)\ninterface Read<A> {\nread : A -> Int\n}\neffect Send {\nsend : Box<(Unit -> Int)> -> Unit\n}\nmain : Unit -> Int\nmain () = handle (resource cell<R> c = 41 {\nlet copied = Cell.read c\nnewtype Token = Token(Unit)\nlet token = Token(())\nwith Read<Token> {\nread ignored = copied + 1\n}\nlet later : Unit -> Int = fn(ignored) {\nread token\n}\nlet _ = perform Send.send (pack later)\n42\n}) with Send {\nsend payload => {\nlet _ = resume ()\nlet call = unpack payload\ncall ()\n}\n}\n\n",
        false,
    );
}

#[test]
fn opaque_request_payload_rejects_resource_dependent_evidence() {
    assert_opaque_resource_witness(
        "import @builtin.cell as Cell\nimport helper (Box, pack, unpack)\ninterface Read<A> {\nread : A -> Int\n}\neffect Send {\nsend : Box<(Unit -> Int)> -> Unit\n}\nmain : Unit -> Int\nmain () = handle (resource cell<R> c = 41 {\nlet copied = Cell.read c\nnewtype Token = Token(Unit)\nlet token = Token(())\nwith Read<Token> {\nread ignored = handle (Cell.read c) with Cell.Ops<R> {\nread ignored => resume 42\nwrite ignored => resume ()\n}\n}\nlet later : Unit -> Int = fn(ignored) {\nread token\n}\nlet _ = perform Send.send (pack later)\n42\n}) with Send {\nsend payload => {\nlet _ = resume ()\nlet call = unpack payload\ncall ()\n}\n}\n\n",
        true,
    );
}

#[test]
fn row_polymorphic_relay_preserves_imported_and_local_accessor_identity() {
    const HELPER: &str = "import @builtin.cell as Cell\npub reader<R> : Cell.Handle<R> -> (Unit -> Int ! {Cell.Ops<R>}) where Cell.Provider<R>\nreader value = fn(ignored) {\nCell.read value\n}\npub relay<E : EffectRow, A> : ((Unit -> Int ! {| E}), A) -> Int ! {| E}\nrelay (action, ignored) = action ()\n";
    for imported in [true, false] {
        for (nested, annotated) in [(false, false), (true, false), (true, true)] {
            let tree = Tree::new();
            fs::write(tree.0.join("helper.ash"), HELPER).unwrap();
            let header = if imported {
                "import @builtin.cell as Cell\nimport helper (reader, relay)\n".to_owned()
            } else {
                HELPER.replace("pub ", "")
            };
            let binding = if annotated {
                "let get : Unit -> Int ! {Cell.Ops<R>} = reader c"
            } else {
                "let get = reader c"
            };
            let body = if nested {
                "resource cell<S> other = 999 {\nrelay (get, true) + get ()\n}"
            } else {
                "relay (get, true) + get ()"
            };
            let source = format!(
                "{header}main : Unit -> Int\nmain () = resource cell<R> c = 21 {{\n{binding}\n{body}\n}}\n"
            );
            tree.check(&source).unwrap_or_else(|error| {
                panic!("imported={imported} nested={nested} annotated={annotated}: {error}")
            });
            let result = ash::driver::run_path(ash::driver::RunConfiguration {
                entry: tree.0.join("entry.ash"),
                roots: ModuleRoots::empty(),
            })
            .unwrap();
            assert_eq!(result.value().to_string(), "42");
        }
    }
}

#[test]
fn row_relays_keep_distinct_rows_and_locally_handled_prefixes() {
    for source in [
        "import @builtin.cell as Cell\nreader<R> : Cell.Handle<R> -> (Unit -> Int ! {Cell.Ops<R>}) where Cell.Provider<R>\nreader value = fn(ignored) {\nCell.read value\n}\nchoose<E : EffectRow, F : EffectRow> : ((Unit -> Int ! {| E}), (Unit -> Int ! {| F})) -> (Unit -> Int ! {| F}) ! {| E}\nchoose (first, second) = {\nlet _ = first ()\nlet later : Unit -> Int ! {| F} = fn(ignored) {\nsecond ()\n}\nlater\n}\nmain : Unit -> Int\nmain () = resource cell<R> c = 40 {\nresource cell<S> other = 2 {\nlet first = reader c\nlet second = reader other\nlet selected = choose (first, second)\nCell.read c + selected ()\n}\n}\n",
        "import @builtin.cell as Cell\neffect Mark {\nmark : Unit -> Unit\n}\nreader<R> : Cell.Handle<R> -> (Unit -> Int ! {Mark, Cell.Ops<R>}) where Cell.Provider<R>\nreader value = fn(ignored) {\nlet _ = perform Mark.mark ()\nCell.read value\n}\nrelay<E : EffectRow> : (Unit -> Int ! {Mark | E}) -> Int ! {| E}\nrelay action = handle (action ()) with Mark {\nmark ignored => resume ()\n}\nmain : Unit -> Int\nmain () = resource cell<R> c = 42 {\nlet get = reader c\nrelay get\n}\n",
        "import @builtin.cell as Cell\nreader<R> : Cell.Handle<R> -> (Unit -> Int ! {Cell.Ops<R>}) where Cell.Provider<R>\nreader value = fn(ignored) {\nCell.read value\n}\nrelay<E : EffectRow> : (Unit -> Int ! {| E}) -> Int ! {| E}\nrelay action = action ()\nmain : Unit -> Int\nmain () = resource cell<R> c = 20 {\nresource cell<S> other = 2 {\nlet get = reader c\nlet first = handle (relay get) with Cell.Ops<R> {\nread ignored => resume 40\nwrite ignored => resume ()\n}\nfirst + Cell.read other\n}\n}\n",
    ] {
        let tree = Tree::new();
        tree.check(source).unwrap();
        let result = ash::driver::run_path(ash::driver::RunConfiguration {
            entry: tree.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        assert_eq!(result.value().to_string(), "42");
    }
}

#[test]
fn row_relay_preserves_payload_and_scope_completion_obligations() {
    for copied in [false, true] {
        let capture = if copied { "copied" } else { "let held = c\n21" };
        let source = format!(
            "import @builtin.cell as Cell\neffect Send {{\nsend : (Unit -> Int) -> Int\n}}\nrelay<E : EffectRow> : (Unit -> Int ! {{| E}}) -> Int ! {{| E}}\nrelay action = action ()\nmain : Unit -> Int\nmain () = handle (resource cell<R> c = 21 {{\nlet copied = Cell.read c\nlet payload : Unit -> Int = fn(ignored) {{\n{capture}\n}}\nlet send : Unit -> Int ! {{Send}} = fn(ignored) {{\nperform Send.send payload\n}}\nrelay send\n}}) with Send {{\nsend payload => {{\nlet result = resume 21\nresult + payload ()\n}}\n}}\n"
        );
        let tree = Tree::new();
        assert_check(
            tree.check(&source),
            if copied { None } else { Some("ResourceEscape") },
        );
        if copied {
            let result = ash::driver::run_path(ash::driver::RunConfiguration {
                entry: tree.0.join("entry.ash"),
                roots: ModuleRoots::empty(),
            })
            .unwrap();
            assert_eq!(result.value().to_string(), "42");
        }
    }
    for discard in [false, true] {
        let completion = if discard {
            "let _ = discard\n42"
        } else {
            "resume 42"
        };
        let source = format!(
            "import @builtin.cell as Cell\neffect Stop {{\nstop : Unit -> Int\n}}\nrelay<E : EffectRow> : (Unit -> Int ! {{| E}}) -> Int ! {{| E}}\nrelay action = action ()\nmain : Unit -> Int\nmain () = handle (resource cell<R> c = 21 {{\nlet stop : Unit -> Int ! {{Stop}} = fn(ignored) {{\nperform Stop.stop ()\n}}\nrelay stop\n}}) with Stop {{\nstop ignored => {{\n{completion}\n}}\n}}\n"
        );
        let tree = Tree::new();
        tree.check(&source).unwrap();
        let result = ash::driver::run_path(ash::driver::RunConfiguration {
            entry: tree.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        assert_eq!(result.value().to_string(), "42");
    }
}

#[test]
fn discarded_strict_inputs_do_not_publish_unexecuted_resource_results() {
    for (shape, source) in [
        (
            "match",
            "import @builtin.cell as Cell\neffect Stop {\nstop : Unit -> Bool\n}\nmain : Unit -> Int\nmain () = {\nlet escaped = resource cell<R> c = 41 {\nlet later : Unit -> Int = fn(ignored) {\nlet held = c\n42\n}\nlet constant : Unit -> Int = fn(ignored) {\n42\n}\nhandle (match (perform Stop.stop ()) {\ntrue => later\nfalse => constant\n}) with Stop {\nstop ignored => {\nlet _ = discard\nconstant\n}\n}\n}\nescaped ()\n}\n",
        ),
        (
            "apply",
            "import @builtin.cell as Cell\neffect Stop {\nstop : Unit -> Bool\n}\nmain : Unit -> Int\nmain () = {\nlet escaped = resource cell<R> c = 41 {\nlet later : Unit -> Int = fn(ignored) {\nlet held = c\n42\n}\nlet constant : Unit -> Int = fn(ignored) {\n42\n}\nlet choose : Bool -> (Unit -> Int) = fn(ignored) {\nlater\n}\nhandle (choose (perform Stop.stop ())) with Stop {\nstop ignored => {\nlet _ = discard\nconstant\n}\n}\n}\nescaped ()\n}\n",
        ),
        (
            "tuple",
            "import @builtin.cell as Cell\neffect Stop {\nstop : Unit -> Bool\n}\nmain : Unit -> Int\nmain () = {\nlet escaped = resource cell<R> c = 41 {\nlet later : Unit -> Int = fn(ignored) {\nlet held = c\n42\n}\nlet constant : Unit -> Int = fn(ignored) {\n42\n}\nhandle ((later, perform Stop.stop ())) with Stop {\nstop ignored => {\nlet _ = discard\n(constant, true)\n}\n}\n}\n42\n}\n",
        ),
    ] {
        Tree::new()
            .check(source)
            .unwrap_or_else(|error| panic!("discarded {shape}: {error}"));
        let resumed = if shape == "tuple" {
            source.replace("let _ = discard\n(constant, true)", "resume true")
        } else {
            source.replace("let _ = discard\nconstant", "resume true")
        };
        let error = Tree::new().check(&resumed).unwrap_err();
        assert!(error.contains("ResourceEscape"), "resumed {shape}: {error}");
    }
    for (shape, body, returned) in [
        (
            "primitive",
            "{\nlet copied = (perform Stop.stop ()) == 0\nlater\n}",
            "0",
        ),
        (
            "initializer",
            "resource cell<S> inner = (perform Stop.stop ()) {\nlater\n}",
            "0",
        ),
    ] {
        let source = format!(
            "import @builtin.cell as Cell\neffect Stop {{\nstop : Unit -> Int\n}}\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet later : Unit -> Int = fn(ignored) {{\nlet held = c\n42\n}}\nlet constant : Unit -> Int = fn(ignored) {{\n42\n}}\nhandle ({body}) with Stop {{\nstop ignored => {{\nlet _ = discard\nconstant\n}}\n}}\n}}\nescaped ()\n}}\n"
        );
        Tree::new()
            .check(&source)
            .unwrap_or_else(|error| panic!("discarded {shape}: {error}"));
        let resumed = source.replace("let _ = discard\nconstant", &format!("resume {returned}"));
        let error = Tree::new().check(&resumed).unwrap_err();
        assert!(error.contains("ResourceEscape"), "resumed {shape}: {error}");
    }
}

#[test]
fn suspended_same_site_resource_preserves_outer_operation_and_metadata_captures() {
    for source in [
        "import @builtin.cell as Cell\neffect Pause {\nask : Unit -> Unit\n}\nvisit : Int -> Int ! {Pause}\nvisit depth = resource cell<R> c = depth {\nmatch depth == 0 {\ntrue => {\nlet _ = perform Pause.ask ()\nCell.read c\n}\nfalse => {\nlet observe : Unit -> Int ! {Cell.Ops<R>} = fn(ignored) {\nCell.read c\n}\nhandle (visit 0) with Pause {\nask ignored => {\nlet outer = observe ()\nlet inner = resume ()\nouter + inner\n}\n}\n}\n}\n}\nmain : Unit -> Int\nmain () = handle (visit 1) with Pause {\nask ignored => resume ()\n}\n",
        "import @builtin.cell as Cell\neffect E<T> {\nask : Unit -> Int\n}\neffect Pause {\nask : Unit -> Unit\n}\nvisit : Int -> Int ! {Pause}\nvisit depth = resource cell<R> c = depth {\nlet observe : Unit -> Int ! {E<R>} = fn(ignored) {\nperform E<R>.ask ()\n}\nhandle (match depth == 0 {\ntrue => {\nlet _ = perform Pause.ask ()\n0\n}\nfalse => {\nhandle (visit 0) with Pause {\nask ignored => {\nlet outer = observe ()\nlet inner = resume ()\nouter + inner\n}\n}\n}\n}) with E<R> {\nask ignored => resume depth\n}\n}\nmain : Unit -> Int\nmain () = handle (visit 1) with Pause {\nask ignored => resume ()\n}\n",
    ] {
        Tree::new().check(source).unwrap();
    }
}

#[test]
fn resource_owners_publish_checked_summaries_through_real_imports() {
    for implementation_only in [false, true] {
        let tree = Tree::new();
        let (owner, entry) = if implementation_only {
            (
                "import @builtin.cell as Cell\npub interface Value<A> {\nvalue : A -> Int\n}\npub impl Value<Unit> {\nvalue ignored = resource cell<R> c = 42 {\nCell.read c\n}\n}\n",
                "import owner (value, impl Value)\nmain : Unit -> Int\nmain () = value ()\n",
            )
        } else {
            (
                "import @builtin.cell as Cell\npub readCell : Unit -> Int\nreadCell () = resource cell<R> c = 42 {\nCell.read c\n}\npub makeCopiedClosure : Unit -> (Unit -> Int)\nmakeCopiedClosure () = resource cell<R> c = 41 {\nlet copied = Cell.read c\nlet later : Unit -> Int = fn(ignored) {\ncopied + 1\n}\nlater\n}\n",
                "import owner (readCell, makeCopiedClosure)\nmain : Unit -> Int\nmain () = {\nlet _ = readCell ()\nlet later = makeCopiedClosure ()\nlater ()\n}\n",
            )
        };
        fs::write(tree.0.join("owner.ash"), owner).unwrap();
        tree.check(entry)
            .unwrap_or_else(|error| panic!("implementation_only={implementation_only}: {error}"));
        let result = ash::driver::run_path(ash::driver::RunConfiguration {
            entry: tree.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        assert_eq!(result.value().to_string(), "42");
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
        tree.check(&source).unwrap();
    }
}

#[test]
fn acquisition_checks_with_only_handle_or_read_selected() {
    let tree = Tree::new();
    for (selected, body) in [("Handle", "42"), ("read", "read c")] {
        tree.check(&format!("import @builtin.cell ({selected})\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {{\n{body}\n}}\n")).unwrap();
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
    tree.check("import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {\nlet c = 41\nresource cell<R> c = c {\nCell.read c\n}\n}\n").unwrap();
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
fn identity_free_closure_cannot_escape_its_resource_owner() {
    let tree = Tree::new();
    let error = tree.check("import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {\nlet escaped = resource cell<R> c = 41 {\nlet later : Unit -> Int = fn(ignored) {\nhandle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nlater\n}\n42\n}\n").unwrap_err();
    assert!(error.contains("ResourceEscape"), "{error}");
}

#[test]
fn copied_integer_and_constant_closure_have_no_stored_resource_dependency() {
    let tree = Tree::new();
    for body in [
        "Cell.read c",
        "let later : Unit -> Int = fn(ignored) {\n42\n}\nlater",
        "let copied = Cell.read c\nlet later : Unit -> Int = fn(ignored) {\ncopied\n}\nlater",
    ] {
        tree.check(&format!("import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\n{body}\n}}\n42\n}}\n")).unwrap();
    }
}

#[test]
fn helper_and_factory_results_preserve_stored_resource_dependencies() {
    let tree = Tree::new();
    for result in ["keep later", "make later"] {
        let error = tree.check(&format!("import @builtin.cell as Cell\nkeep<T> : T -> T\nkeep value = value\nmake : (Unit -> Int) -> (Unit -> Int)\nmake value = fn(ignored) {{\nvalue ()\n}}\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet later : Unit -> Int = fn(ignored) {{\nhandle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\n{result}\n}}\n42\n}}\n")).unwrap_err();
        assert!(error.contains("ResourceEscape"), "{result}: {error}");
    }
}

#[test]
fn operation_metadata_alone_retains_the_resource_identity() {
    let tree = Tree::new();
    let error = tree.check("import @builtin.cell as Cell\nquiet<R> : Unit -> Int ! {Cell.Ops<R>}\nquiet () = 42\nmain : Unit -> Int\nmain () = {\nlet escaped = resource cell<R> c = 41 {\nlet later : Unit -> Int = fn(ignored) {\nlet scoped : Unit -> Int ! {Cell.Ops<R>} = quiet\nhandle (scoped ()) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nlater\n}\n42\n}\n").unwrap_err();
    assert!(error.contains("ResourceEscape"), "{error}");
}

#[test]
fn outer_handler_cannot_receive_a_hidden_resource_dependent_payload() {
    let error = Tree::new().check("import @builtin.cell as Cell\neffect Send {\nsend : (Unit -> Int) -> Unit\n}\nmain : Unit -> Int\nmain () = {\nlet escaped = handle ({\nlet _ = resource cell<R> c = 41 {\nlet later : Unit -> Int = fn(ignored) {\nhandle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nlet _ = perform Send.send later\n42\n}\nlet constant : Unit -> Int = fn(ignored) {\n0\n}\nconstant\n}) with Send {\nsend payload => {\nlet _ = resume ()\npayload\n}\n}\nescaped ()\n}\n").unwrap_err();
    assert!(error.contains("ResourceEscape"), "{error}");
}

#[test]
fn outward_copied_payload_and_still_live_outer_dependency_remain_admitted() {
    for source in [
        "import @builtin.cell as Cell\neffect Send {\nsend : Int -> Unit\n}\nmain : Unit -> Int\nmain () = handle (resource cell<R> c = 41 {\nlet copied = Cell.read c\nlet _ = perform Send.send copied\n42\n}) with Send {\nsend payload => {\nlet _ = resume ()\npayload\n}\n}\n",
        "import @builtin.cell as Cell\neffect Send {\nsend : (Unit -> Int) -> Unit\n}\nmain : Unit -> Int\nmain () = resource cell<A> a = 41 {\nlet escaped = handle (resource cell<B> b = 0 {\nlet later : Unit -> Int = fn(ignored) {\nhandle (Cell.read a) with Cell.Ops<A> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nlet _ = perform Send.send later\nlet constant : Unit -> Int = fn(ignored) {\n0\n}\nconstant\n}) with Send {\nsend payload => {\nlet _ = resume ()\npayload\n}\n}\nescaped ()\n}\n",
    ] {
        Tree::new().check(source).unwrap();
    }
}

#[test]
fn discard_closes_its_owned_acquired_resource_scope() {
    Tree::new().check("import @builtin.cell as Cell\neffect Stop {\nstop : Unit -> Unit\n}\nmain : Unit -> Unit\nmain () = handle (resource cell<R> c = 41 {\nperform Stop.stop ()\n}) with Stop {\nstop ignored => discard\n}\n").unwrap();
}

#[test]
fn discard_inside_an_acquired_scope_preserves_its_completion() {
    Tree::new().check("import @builtin.cell as Cell\neffect Stop {\nstop : Unit -> Unit\n}\nmain : Unit -> Unit\nmain () = resource cell<R> c = 41 {\nhandle (perform Stop.stop ()) with Stop {\nstop ignored => discard\n}\n}\n").unwrap();
}

#[test]
fn discard_cannot_skip_resume_of_a_resource_owned_outside_its_capture() {
    let error = Tree::new().check("import @builtin.cell as Cell\neffect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\nmain : Unit -> Unit\nmain () = handle (resource cell<R> c = 41 {\nperform A.ask ()\n}) with A {\nask ignored => {\nlet _ = handle ({\nlet _ = perform B.ask ()\nresume ()\n}) with B {\nask ignored => discard\n}\n()\n}\n}\n").unwrap_err();
    assert!(error.contains("DiscardUnsafe"), "{error}");
}

#[test]
fn consumed_clause_owner_does_not_keep_a_completed_resource_live() {
    Tree::new().check("import @builtin.cell as Cell\neffect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\nmain : Unit -> Unit\nmain () = handle (resource cell<R> c = 41 {\nperform A.ask ()\n}) with A {\nask ignored => {\nlet _ = resume ()\nhandle (perform B.ask ()) with B {\nask ignored => discard\n}\n}\n}\n").unwrap();
}

#[test]
fn recursive_resource_occurrences_preserve_inside_scope_discard() {
    Tree::new().check("import @builtin.cell as Cell\neffect Stop {\nstop : Unit -> Unit\n}\nrepeat : Bool -> Unit\nrepeat again = resource cell<R> c = 41 {\nmatch again {\ntrue => repeat false\nfalse => handle (perform Stop.stop ()) with Stop {\nstop ignored => discard\n}\n}\n}\nmain : Unit -> Unit\nmain () = repeat true\n").unwrap();
}

#[test]
fn invoking_a_known_callback_preserves_its_result_dependencies() {
    for result in ["later", "constant"] {
        let outcome = Tree::new().check(&format!("import @builtin.cell as Cell\ninvoke : (Unit -> (Unit -> Int)) -> (Unit -> Int)\ninvoke callback = callback ()\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet later : Unit -> Int = fn(ignored) {{\nhandle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\nlet constant : Unit -> Int = fn(ignored) {{\n42\n}}\nlet callback : Unit -> (Unit -> Int) = fn(ignored) {{\nlet _ = later ()\n{result}\n}}\ninvoke callback\n}}\n42\n}}\n"));
        let expected = if result == "later" {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn projecting_a_resource_free_field_does_not_retain_other_fields() {
    for select in ["left", "right"] {
        let outcome = Tree::new().check(&format!("import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet later : Unit -> Int = fn(ignored) {{\nhandle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\nlet constant : Unit -> Int = fn(ignored) {{\n42\n}}\nlet (left, right) = (later, constant)\n{select}\n}}\n42\n}}\n"));
        let expected = if select == "left" {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn outward_unhandled_request_cannot_export_a_resource_dependent_payload() {
    let error = Tree::new().check("import @builtin.cell as Cell\neffect Send {\nsend : (Unit -> Int) -> Unit\n}\npub helper : Unit -> Int ! {Send}\nhelper () = resource cell<R> c = 41 {\nlet later : Unit -> Int = fn(ignored) {\nhandle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nlet _ = perform Send.send later\n42\n}\nmain : Unit -> Int\nmain () = 42\n").unwrap_err();
    assert!(error.contains("ResourceEscape"), "{error}");
}

#[test]
fn two_outer_wrapper_calls_keep_the_inner_factory_arguments_separate() {
    for order in [
        "let dependent = wrap later\nlet safe = wrap constant",
        "let safe = wrap constant\nlet dependent = wrap later",
    ] {
        Tree::new().check(&format!("import @builtin.cell as Cell\nmake : (Unit -> Int) -> (Unit -> Int)\nmake value = fn(ignored) {{\nvalue ()\n}}\nwrap : (Unit -> Int) -> (Unit -> Int)\nwrap value = make value\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet later : Unit -> Int = fn(ignored) {{\nhandle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\nlet constant : Unit -> Int = fn(ignored) {{\n42\n}}\n{order}\nsafe\n}}\n42\n}}\n")).unwrap();
    }
}

#[test]
fn generic_constructor_payload_projection_preserves_resource_dependencies() {
    for result in ["later", "constant"] {
        let outcome = Tree::new().check(&format!("import @builtin.cell as Cell\ntype Box<T> = Box(T)\nget<T> : Box<T> -> T\nget (Box value) = value\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet later : Unit -> Int = fn(ignored) {{\nhandle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\nlet constant : Unit -> Int = fn(ignored) {{\n42\n}}\nget (Box {result})\n}}\n42\n}}\n"));
        let expected = if result == "later" {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn imported_generic_projections_preserve_only_the_selected_field() {
    let tree = Tree::new();
    std::fs::write(tree.0.join("helper.ash"), "pub first<A, B> : (A, B) -> A\nfirst (left, right) = left\npub second<A, B> : (A, B) -> B\nsecond (left, right) = right\n").unwrap();
    for function in ["first", "second"] {
        let outcome = tree.check(&format!("import @builtin.cell as Cell\nimport helper ({function})\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet later : Unit -> Int = fn(ignored) {{\nhandle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\nlet constant : Unit -> Int = fn(ignored) {{\n42\n}}\n{function} (later, constant)\n}}\n42\n}}\n"));
        let expected = if function == "first" {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn pure_imported_data_summaries_preserve_erased_execution() {
    let tree = Tree::new();
    fs::write(
        tree.0.join("helper.ash"),
        "pub second<A, B> : (A, B) -> B\nsecond (left, right) = right\n",
    )
    .unwrap();
    fs::write(
        tree.0.join("entry.ash"),
        "import helper (second)\nmain : Unit -> Int\nmain () = second (true, 42)\n",
    )
    .unwrap();
    let observation = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: tree.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .unwrap();
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn builtin_import_and_ordinary_effect_registry_execute_without_acquisition() {
    let tree = Tree::new();
    fs::write(tree.0.join("entry.ash"), "import @builtin.cell as Cell\neffect Send {\nsend : Int -> Int\n}\nmain : Unit -> Int\nmain () = handle (perform Send.send 42) with Send {\nsend value => resume value\n}\n").unwrap();
    let observation = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: tree.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .unwrap();
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn capture_control_selects_the_requested_operation_not_every_effect_clause() {
    Tree::new().check("effect A {\nfirst : Unit -> Unit\nsecond : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\nmain : Unit -> Unit\nmain () = handle (handle (perform A.first ()) with A {\nfirst ignored => resume ()\nsecond ignored => {\nlet _ = perform B.ask ()\nresume ()\n}\n}) with B {\nask ignored => discard\n}\n").unwrap();
}

#[test]
fn returned_generic_callable_closes_owned_resource_free_captures() {
    for direct in [true, false] {
        let body = if direct {
            "perform B.ask ()"
        } else {
            "handle (perform A.ask ()) with A {\nask ignored => {\nlet _ = perform B.ask ()\nresume ()\n}\n}"
        };
        let source = format!(
            "effect A {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\nidentity<F> : F -> F\nidentity value = value\nask : Unit -> Unit ! {{B}}\nask () = {body}\nmain : Unit -> Int\nmain () = handle ({{\nlet action = identity ask\nlet _ = action ()\n0\n}}) with B {{\nask ignored => {{\nlet _ = discard\n42\n}}\n}}\n"
        );
        let tree = Tree::new();
        tree.check(&source).unwrap();
        let observation = ash::driver::run_path(ash::driver::RunConfiguration {
            entry: tree.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        assert_eq!(observation.value_display(), "42");
    }
}

#[test]
fn resumed_payload_flows_back_to_the_suspended_request_result() {
    for body in [
        "handle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}",
        "42",
    ] {
        let source = format!(
            "import @builtin.cell as Cell\neffect Send {{\nsend : (Unit -> Int) -> (Unit -> Int)\n}}\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet later : Unit -> Int = fn(ignored) {{\n{body}\n}}\nhandle (perform Send.send later) with Send {{\nsend payload => resume payload\n}}\n}}\n42\n}}\n"
        );
        let outcome = Tree::new().check(&source);
        let expected = if body == "42" {
            None
        } else {
            Some("ResourceEscape")
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn request_payload_projection_preserves_only_the_selected_dependency() {
    let tree = Tree::new();
    fs::write(tree.0.join("helper.ash"), "pub first<A, B> : (A, B) -> A\nfirst (left, right) = left\npub second<A, B> : (A, B) -> B\nsecond (left, right) = right\n").unwrap();
    for select in ["first", "second"] {
        let source = format!(
            "import @builtin.cell as Cell\nimport helper ({select})\neffect Send {{\nsend : (Unit -> Int) -> Unit\n}}\nmain : Unit -> Int\nmain () = handle (resource cell<R> c = 41 {{\nlet copied = Cell.read c\nlet later : Unit -> Int = fn(ignored) {{\nhandle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\nlet constant : Unit -> Int = fn(ignored) {{\n42\n}}\nlet _ = perform Send.send ({select} (later, constant))\n42\n}}) with Send {{\nsend payload => resume ()\n}}\n"
        );
        let outcome = tree.check(&source);
        let expected = if select == "first" {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn constructor_application_does_not_skip_a_later_resource_payload_request() {
    for body in ["let held = c\n42", "42"] {
        let source = format!(
            "import @builtin.cell as Cell\ntype Box<A> = Box(A)\neffect Send {{\nsend : (Unit -> Int) -> Unit\n}}\nmain : Unit -> Int\nmain () = handle (resource cell<R> c = 41 {{\nlet boxed = Box 1\nlet later : Unit -> Int = fn(ignored) {{\n{body}\n}}\nlet _ = perform Send.send later\n42\n}}) with Send {{\nsend payload => resume ()\n}}\n"
        );
        let outcome = Tree::new().check(&source);
        let expected = if body == "42" {
            None
        } else {
            Some("ResourceEscape")
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn prefocus_resume_preserves_nested_handler_callback_dependencies() {
    for body in [
        "handle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}",
        "copied",
        "42",
    ] {
        let source = format!(
            "import @builtin.cell as Cell\neffect Ask {{\nask : Unit -> (Unit -> Int)\n}}\neffect Send {{\nsend : (Unit -> Int) -> Unit\n}}\nmain : Unit -> Int\nmain () = handle (\nhandle ({{\nlet later = perform Ask.ask ()\nlet _ = perform Send.send later\n42\n}}) with Ask {{\nask ignored => resource cell<R> c = 41 {{\nlet copied = Cell.read c\nlet later : Unit -> Int = fn(ignored) {{\n{body}\n}}\nresume later\n}}\n}}\n) with Send {{\nsend later => {{\nlet copied = later ()\nlet _ = resume ()\ncopied\n}}\n}}\n"
        );
        let outcome = Tree::new().check(&source);
        let expected = if body.starts_with("handle") {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn nested_generic_handler_callback_normalizes_solved_effect_arguments() {
    let tree = Tree::new();
    let source = "effect E<A> {\nget : A -> Int\n}\nrequest<A> : A -> Int ! {E<A>}\nrequest value = perform E<A>.get value\neffect Ask {\nask : Unit -> (Unit -> Int)\n}\nmain : Unit -> Int\nmain () = handle ({\nlet later = perform Ask.ask ()\nlater ()\n}) with Ask {\nask ignored => {\nlet later : Unit -> Int = fn(ignored) {\nhandle (request 42) with E<Int> {\nget value => resume value\n}\n}\nresume later\n}\n}\n";
    fs::write(tree.0.join("entry.ash"), source).unwrap();
    let observation = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: tree.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect(
        "solved nested effect instance should remain exact through outer resume-row recomputation",
    );
    assert_eq!(observation.value_display(), "42");
    let wrong = source.replace("with E<Int>", "with E<Bool>");
    let error = tree.check(&wrong).unwrap_err();
    assert!(error.contains("MissingHandledEffect"), "{error}");
}

#[test]
fn delayed_resume_values_wake_calls_and_payload_obligations() {
    for invoke in [false, true] {
        for hidden in [true, false] {
            let body = if hidden { "let held = c\n42" } else { "42" };
            let (callback_type, callback_body, continuation) = if invoke {
                (
                    "Unit -> Unit ! {Send}",
                    format!(
                        "let payload : Unit -> Int = fn(ignored) {{\n{body}\n}}\nperform Send.send payload"
                    ),
                    "let _ = later ()",
                )
            } else {
                (
                    "Unit -> Int",
                    body.to_owned(),
                    "let _ = perform Send.send later",
                )
            };
            let source = format!(
                "import @builtin.cell as Cell\neffect Send {{\nsend : (Unit -> Int) -> Unit\n}}\neffect Ask {{\nask : Unit -> ({callback_type})\n}}\nmain : Unit -> Int\nmain () = handle (resource cell<R> c = 41 {{\nlet later = handle (perform Ask.ask ()) with Ask {{\nask ignored => {{\nlet callback : {callback_type} = fn(ignored) {{\n{callback_body}\n}}\nresume callback\n}}\n}}\n{continuation}\n42\n}}) with Send {{\nsend ignored => resume ()\n}}\n"
            );
            let outcome = Tree::new().check(&source);
            let expected = if hidden { Some("ResourceEscape") } else { None };
            assert_check(outcome, expected);
        }
    }
}

#[test]
fn mixed_kind_row_forwarding_preserves_metadata_captures() {
    for body in [
        "let scoped : Unit -> Int ! {Cell.Ops<R>} = quiet\nhandle (relay scoped) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}",
        "42",
    ] {
        let source = format!(
            "import @builtin.cell as Cell\nquiet<R> : Unit -> Int ! {{Cell.Ops<R>}}\nquiet () = 42\nrelay<E : EffectRow, A> : (Unit -> A ! {{| E}}) -> A ! {{| E}}\nrelay action = action ()\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet later : Unit -> Int = fn(ignored) {{\n{body}\n}}\nlater\n}}\n42\n}}\n"
        );
        let outcome = Tree::new().check(&source);
        let expected = if body == "42" {
            None
        } else {
            Some("ResourceEscape")
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn tuple_pattern_can_project_an_effectful_callback_and_execute() {
    let tree = Tree::new();
    let source = "effect Ask {\nask : Unit -> Int\n}\nrelay<E : EffectRow, A> : ((Unit -> Int ! {| E}), A) -> Int ! {| E}\nrelay (action, ignored) = action ()\nask : Unit -> Int ! {Ask}\nask () = perform Ask.ask ()\nmain : Unit -> Int\nmain () = handle (relay (ask, true)) with Ask {\nask ignored => resume 42\n}\n";
    fs::write(tree.0.join("entry.ash"), source).unwrap();
    let observation = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: tree.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .unwrap();
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn selected_lexical_method_retains_its_actual_body_dependencies() {
    for body in [
        "handle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}",
        "42",
    ] {
        let source = format!(
            "import @builtin.cell as Cell\ninterface Read<A> {{\nread : A -> Int\n}}\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nnewtype Token = Token(Unit)\nlet saved = Token(())\nwith Read<Token> {{\nread ignored = {body}\n}}\nlet later : Unit -> Int = fn(ignored) {{\nread saved\n}}\nlater\n}}\n42\n}}\n"
        );
        let outcome = Tree::new().check(&source);
        let expected = if body == "42" {
            None
        } else {
            Some("ResourceEscape")
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn disjoint_evidence_selections_do_not_share_the_method_name_capture() {
    for result in ["hidden", "safe"] {
        let source = format!(
            "import @builtin.cell as Cell\ninterface Read<A> {{\nread : A -> Int\n}}\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nnewtype Token = Token(Unit)\nlet saved = Token(())\nlet hidden : Unit -> Int = {{\nwith Read<Token> {{\nread ignored = handle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\nfn(ignored) {{\nread saved\n}}\n}}\nlet safe : Unit -> Int = {{\nwith Read<Token> {{\nread ignored = 42\n}}\nfn(ignored) {{\nread saved\n}}\n}}\n{result}\n}}\n42\n}}\n"
        );
        let outcome = Tree::new().check(&source);
        let expected = if result == "safe" {
            None
        } else {
            Some("ResourceEscape")
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn imported_constrained_helper_retains_selected_evidence_dependencies() {
    let tree = Tree::new();
    fs::write(tree.0.join("helper.ash"), "pub interface Read<A> {\nread : A -> Int\n}\npub invoke<A> : A -> Int where Read<A>\ninvoke value = read value\n").unwrap();
    for body in [
        "handle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}",
        "copied",
    ] {
        let source = format!(
            "import @builtin.cell as Cell\nimport helper (Read, read, invoke)\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet copied = Cell.read c\nnewtype Token = Token(Unit)\nlet saved = Token(())\nwith Read<Token> {{\nread ignored = {body}\n}}\nlet later : Unit -> Int = fn(ignored) {{\ninvoke saved\n}}\nlater\n}}\n42\n}}\n"
        );
        let outcome = tree.check(&source);
        let expected = if body == "copied" {
            None
        } else {
            Some("ResourceEscape")
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn unused_imported_evidence_prerequisite_does_not_capture_its_method() {
    for wrapper in [false, true] {
        for helper_body in ["read value", "42"] {
            let tree = Tree::new();
            let declarations = if wrapper {
                format!(
                    "inner<A> : A -> Int where Read<A>\ninner value = {helper_body}\npub invoke<A> : A -> Int where Read<A>\ninvoke value = inner value\n"
                )
            } else {
                format!("pub invoke<A> : A -> Int where Read<A>\ninvoke value = {helper_body}\n")
            };
            fs::write(
                tree.0.join("helper.ash"),
                format!("pub interface Read<A> {{\nread : A -> Int\n}}\n{declarations}"),
            )
            .unwrap();
            let source = "import @builtin.cell as Cell\nimport helper (Read, read, invoke)\nmain : Unit -> Int\nmain () = {\nlet escaped = resource cell<R> c = 41 {\nnewtype Token = Token(Unit)\nlet saved = Token(())\nwith Read<Token> {\nread ignored = handle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nlet later : Unit -> Int = fn(ignored) {\ninvoke saved\n}\nlater\n}\n42\n}\n";
            let outcome = tree.check(source);
            let expected = if helper_body == "42" {
                None
            } else {
                Some("ResourceEscape")
            };
            assert_check(outcome, expected);
        }
    }
}

#[test]
fn imported_implementation_method_preserves_selected_prerequisite_capture() {
    for nested in [false, true] {
        let tree = Tree::new();
        let implementations = if nested {
            "pub impl<A> Read<Box<A>> where Read<A> {\nread (Box value) = read value\n}\npub impl<A> Make<Box<Box<A>>> where Read<Box<A>> {\nmake (Box value) = fn(ignored) {\nread value\n}\n}\n"
        } else {
            "pub impl<A> Make<Box<A>> where Read<A> {\nmake (Box value) = fn(ignored) {\nread value\n}\n}\n"
        };
        fs::write(tree.0.join("helper.ash"), format!("pub interface Read<A> {{\nread : A -> Int\n}}\npub type Box<A> = Box(A)\npub interface Make<A> {{\nmake : A -> (Unit -> Int)\n}}\n{implementations}")).unwrap();
        for body in [
            "handle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}",
            "copied",
            "42",
        ] {
            let additional = if nested { ", impl Read" } else { "" };
            let argument = if nested {
                "Box (Box saved)"
            } else {
                "Box saved"
            };
            let source = format!(
                "import @builtin.cell as Cell\nimport helper (Read, read, Box, make, impl Make{additional})\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet copied = Cell.read c\nnewtype Token = Token(Unit)\nlet saved = Token(())\nwith Read<Token> {{\nread ignored = {body}\n}}\nlet later : Unit -> Int = make ({argument})\nlater\n}}\n42\n}}\n"
            );
            let outcome = tree.check(&source);
            let expected = if body.starts_with("handle") {
                Some("ResourceEscape")
            } else {
                None
            };
            assert_check(outcome, expected);
        }
    }
}

#[test]
fn nested_implementation_adapters_preserve_method_local_arguments_and_pure_execution() {
    let tree = Tree::new();
    fs::write(tree.0.join("helper.ash"), "pub interface Read<A> {\nread : A -> Int\n}\npub type Box<A> = Box(A)\npub interface Make<A> {\nmake : A -> (Unit -> Int)\n}\npub impl<A> Make<Box<A>> where Read<A> {\nmake (Box value) = fn(ignored) {\nread value\n}\n}\npub interface Lift<A> {\nlift<B> : (A, B) -> (Unit -> Int)\n}\npub impl<A> Lift<Box<A>> where Make<A> {\nlift (Box value, ignored) = make value\n}\n").unwrap();
    for body in [
        "handle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}",
        "copied",
        "42",
    ] {
        let source = format!(
            "import @builtin.cell as Cell\nimport helper (Read, read, Box, lift, impl Lift, impl Make)\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nlet copied = Cell.read c\nnewtype Token = Token(Unit)\nlet saved = Token(())\nwith Read<Token> {{\nread ignored = {body}\n}}\nlet later : Unit -> Int = lift (Box (Box saved), true)\nlater\n}}\n42\n}}\n"
        );
        let outcome = tree.check(&source);
        let expected = if body.starts_with("handle") {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
    }
    for variant in ["make", "lift", "effect"] {
        let (imports, call) = if variant == "make" {
            ("make, impl Make", "make (Box (Token 42))")
        } else {
            (
                "lift, impl Lift, impl Make",
                "lift (Box (Box (Token 42)), true)",
            )
        };
        let effects = if variant == "effect" {
            "effect Ask {\nask : Unit -> Int\n}\n"
        } else {
            ""
        };
        let request = if variant == "effect" {
            "let _ = perform Ask.ask ()\n"
        } else {
            ""
        };
        let body = format!("{{\n{request}let later : Unit -> Int = {call}\nlater ()\n}}");
        let body = if variant == "effect" {
            format!("handle {body} with Ask {{\nask ignored => resume 42\n}}")
        } else {
            body
        };
        fs::write(tree.0.join("entry.ash"), format!("import helper (Read, read, Box, {imports})\ntype Token = Token(Int)\nimpl Read<Token> {{\nread (Token value) = value\n}}\n{effects}main : Unit -> Int\nmain () = {body}\n")).unwrap();
        let observation = ash::driver::run_path(ash::driver::RunConfiguration {
            entry: tree.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap_or_else(|error| panic!("{variant}: {error:?}"));
        assert_eq!(observation.value_display(), "42", "{variant}");
    }
}

#[test]
fn same_typed_implementation_methods_keep_their_own_capture_summaries() {
    let tree = Tree::new();
    fs::write(tree.0.join("helper.ash"), "pub interface Read<A> {\nread : A -> Int\n}\npub type Box<A> = Box(A)\npub interface Two<A> {\nfirst : A -> (Unit -> Int)\nsecond : A -> (Unit -> Int)\n}\npub impl<A> Two<Box<A>> where Read<A> {\nfirst (Box value) = fn(ignored) {\nread value\n}\nsecond (Box value) = fn(ignored) {\n42\n}\n}\n").unwrap();
    for method in ["first", "second"] {
        let source = format!(
            "import @builtin.cell as Cell\nimport helper (Read, read, Box, first, second, impl Two)\nmain : Unit -> Int\nmain () = {{\nlet escaped = resource cell<R> c = 41 {{\nnewtype Token = Token(Unit)\nlet saved = Token(())\nwith Read<Token> {{\nread ignored = handle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\nlet later : Unit -> Int = {method} (Box saved)\nlater\n}}\n42\n}}\n"
        );
        let outcome = tree.check(&source);
        let expected = if method == "first" {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn repeated_resource_site_distinguishes_inherited_and_local_payload_owners() {
    for payload in ["local", "inherited"] {
        let source = format!(
            "import @builtin.cell as Cell\neffect Send {{\nsend : (Unit -> Int) -> Unit\n}}\nvisit : (Int, (Unit -> Int)) -> Int ! {{Send}}\nvisit (depth, inherited) = resource cell<R> c = depth {{\nlet local : Unit -> Int = fn(ignored) {{\nhandle (Cell.read c) with Cell.Ops<R> {{\nread value => resume 42\nwrite value => resume ()\n}}\n}}\nmatch depth == 0 {{\ntrue => {{\nlet _ = perform Send.send {payload}\n42\n}}\nfalse => {{\nlet next = match depth == 2 {{\ntrue => 1\nfalse => 0\n}}\nhandle (visit (next, local)) with Send {{\nsend payload => {{\nlet copied = payload ()\nlet _ = resume ()\ncopied\n}}\n}}\n}}\n}}\n}}\nmain : Unit -> Int\nmain () = {{\nlet initial : Unit -> Int = fn(ignored) {{\n0\n}}\nhandle (visit (2, initial)) with Send {{\nsend payload => {{\nlet copied = payload ()\nlet _ = resume ()\ncopied\n}}\n}}\n}}\n"
        );
        let outcome = Tree::new().check(&source);
        let expected = if payload == "local" {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn completed_factory_value_survives_recursive_resumed_argument() {
    for result in ["inherited", "local"] {
        let source = format!(
            "import @builtin.cell as Cell\neffect Ask {{\nask : Int -> (Unit -> Int)\n}}\nfactory : (Unit -> Int) -> ((Unit -> Int) -> (Unit -> Int))\nfactory inherited = fn(local) {{\n{result}\n}}\nvisit : (Int, (Unit -> Int)) -> (Unit -> Int)\nvisit (depth, inherited) = handle (\n(factory inherited) (perform Ask.ask depth)\n) with Ask {{\nask value => resource cell<R> c = value {{\nlet local : Unit -> Int = fn(ignored) {{\nlet held = c\n42\n}}\nlet _ = match depth == 0 {{\ntrue => 42\nfalse => {{\nlet next = match depth == 2 {{\ntrue => 1\nfalse => 0\n}}\nlet previous = visit (next, local)\nprevious ()\n}}\n}}\nresume local\n}}\n}}\nmain : Unit -> Int\nmain () = {{\nlet initial : Unit -> Int = fn(ignored) {{\n42\n}}\nlet returned = visit (2, initial)\nreturned ()\n}}\n"
        );
        let outcome = Tree::new().check(&source);
        let expected = if result == "local" {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
    }
}

#[test]
fn restored_recursive_resource_preserves_inherited_payload_owner() {
    for payload in ["local", "inherited"] {
        let source = "import @builtin.cell as Cell\neffect Start {\nstart : Unit -> Unit\n}\neffect Send {\nsend : (Unit -> Int) -> Unit\n}\nvisit : (Int, (Unit -> Int)) -> Int ! {Send}\nvisit (depth, inherited) = resource cell<R> c = depth {\nlet local : Unit -> Int = fn(ignored) {\nhandle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nmatch depth == 0 {\ntrue => {\nlet _ = perform Send.send inherited\n42\n}\nfalse => {\nlet next = match depth == 2 {\ntrue => 1\nfalse => 0\n}\nhandle (visit (next, local)) with Send {\nsend payload => {\nlet copied = payload ()\nlet _ = resume ()\ncopied\n}\n}\n}\n}\n}\nmain : Unit -> Int\nmain () = {\nlet initial : Unit -> Int = fn(ignored) {\n0\n}\nhandle ({\nlet _ = perform Start.start ()\nhandle (visit (2, initial)) with Send {\nsend payload => {\nlet copied = payload ()\nlet _ = resume ()\ncopied\n}\n}\n}) with Start {\nstart ignored => resume ()\n}\n}\n".replace("perform Send.send inherited", &format!("perform Send.send {payload}"));
        let outcome = Tree::new().check(&source);
        let expected = if payload == "local" {
            Some("ResourceEscape")
        } else {
            None
        };
        assert_check(outcome, expected);
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
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(diagnostic)) =
        error.pipeline_failure().expect("pipeline failure")
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
        Tree::new().check(&source).unwrap();
    }).unwrap().join().unwrap();
}

#[test]
fn initializer_preserves_outer_effect_instances() {
    Tree::new().check("import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<A> a = 41 {\nresource cell<B> b = (Cell.read a) {\nlet _ = Cell.write (a, 42)\nCell.read b\n}\n}\n").unwrap();
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
    tree.check("import @builtin.cell (Handle)\nimport facade (forward)\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\nforward c\n}\n").unwrap();
}

#[test]
fn resource_rows_are_recomputed_inside_an_enclosing_handler_clause() {
    Tree::new().check("import @builtin.cell as Cell\neffect Ask {\nask : Unit -> Int\n}\nmain : Unit -> Int\nmain () = resource cell<A> a = 1 {\nhandle ({\nlet answer = perform Ask.ask ()\nlet _ = Cell.write (a, answer)\nCell.read a\n}) with Ask {\nask ignored => resource cell<B> b = 41 {\nresume (Cell.read b)\n}\n}\n}\n").unwrap();
}
