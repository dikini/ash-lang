use std::{
    fs,
    path::{Path, PathBuf},
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

#[test]
fn retained_continue_crosses_imported_generic_helpers_with_shared_answer_row() {
    let tree = Tree::new();
    tree.write(
        "helper.ash",
        concat!(
            "import @builtin.retained_control as Control\n",
            "pub forward<N,A,E : EffectRow> : ",
            "(Control.Store<N,(Unit -> A ! {| E})>,Control.Key<N>) -> ",
            "Control.Option<A> ! {Control.Drive<N> | E}\n",
            "forward pair = Control.advance pair\n",
            "pub forward_driven<N,A,E : EffectRow> : ",
            "(Control.Store<N,(Unit -> A ! {Control.Drive<N> | E})>,Control.Key<N>) -> ",
            "Control.Option<A> ! {Control.Drive<N> | E}\n",
            "forward_driven pair = Control.advance_with_drive pair\n",
        ),
    );
    tree.write("facade.ash", "pub import helper (forward,forward_driven)\n");
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import @builtin.retained_control as Control\nimport facade as F\n",
            "nested<N,E : EffectRow> : ",
            "(Control.Store<N,(Unit -> (Unit -> Int ! {| E}) ! {| E})>,Control.Key<N>) -> ",
            "Control.Option<(Unit -> Int ! {| E})> ! {Control.Drive<N> | E}\n",
            "nested pair = F.forward pair\n",
            "nested_driven<N,E : EffectRow> : ",
            "(Control.Store<N,(Unit -> (Unit -> Int ! {| E}) ! {Control.Drive<N> | E})>,Control.Key<N>) -> ",
            "Control.Option<(Unit -> Int ! {| E})> ! {Control.Drive<N> | E}\n",
            "nested_driven pair = {\nlet alias : ",
            "(Control.Store<N,(Unit -> (Unit -> Int ! {| E}) ! {Control.Drive<N> | E})>,Control.Key<N>) -> ",
            "Control.Option<(Unit -> Int ! {| E})> ! {Control.Drive<N> | E} = F.forward_driven\n",
            "alias pair\n}\n",
            "main : Unit -> Int\nmain () = 42\n",
        ),
    );
    let observation = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("the imported helper is checked and linked with the shared answer row");
    assert_eq!(observation.value_display(), "42");

    tree.write(
        "entry.ash",
        concat!(
            "import @builtin.retained_control as Control\nimport facade as F\n",
            "main : Unit -> Int\n",
            "main () = resource Control.Store<N,(Unit -> Int)> store = () {\n",
            "let relay : (Control.Store<N,(Unit -> Int)>,Control.Key<N>) -> ",
            "Control.Option<Int> ! {Control.Drive<N>} = F.forward\n42\n}\n",
        ),
    );
    let failure = ash::driver::compile_path(ash::driver::RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect_err("store release is still awaiting C3");
    assert_eq!(
        failure.reason_code(),
        "core.validation.retained-release",
        "{failure:?}"
    );
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

fn resolve_entry(
    graph: &ModuleGraph,
) -> Result<ash::resolved::ResolvedModule, ash::resolve::ResolveModuleError> {
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let owner = checked
                    .iter()
                    .find(|owner| owner.module() == edge.target())
                    .expect("the exact dependency target should already be checked");
                DependencyExports::new(edge, owner.exports()).expect("authentic target summary")
            })
            .collect::<Vec<_>>();
        let result = resolve_module(module, &dependencies);
        if module.id() == graph.entry() {
            return result;
        }
        checked
            .push(check_module(result.expect("dependency resolves")).expect("dependency checks"));
    }
    panic!("the loaded entry should be present")
}

fn assert_inventory(graph: &ModuleGraph, expected: &[&str]) {
    let names = graph
        .modules()
        .iter()
        .map(|module| {
            Path::new(module.source().display_path())
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(names, expected);
    let checked = check(graph);
    assert_eq!(
        checked
            .iter()
            .map(CheckedModule::module)
            .collect::<Vec<_>>(),
        graph
            .modules()
            .iter()
            .map(|module| module.id())
            .collect::<Vec<_>>()
    );
}

fn module_named<'a>(graph: &'a ModuleGraph, name: &str) -> &'a ash::module::LoadedModule {
    let mut matches = graph.modules().iter().filter(|module| {
        Path::new(module.source().display_path()).file_name() == Some(name.as_ref())
    });
    let module = matches
        .next()
        .expect("the exact fixture module should exist");
    assert!(
        matches.next().is_none(),
        "fixture names should identify one owner"
    );
    module
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
    assert_inventory(
        &graph,
        &[
            "@builtin.foreign",
            "@compiler.region",
            "@builtin.cell",
            "entry.ash",
        ],
    );
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
    assert_inventory(
        &graph,
        &[
            "@builtin.foreign",
            "@compiler.region",
            "@builtin.cell",
            "facade.ash",
            "entry.ash",
        ],
    );
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
        let error = resolve_entry(&graph).expect_err("builtin provider is sealed");
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
    let error = resolve_entry(&graph).expect_err("a direct builtin dependency is required");
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
        assert!(resolve_entry(&graph).is_err());
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
        if prefix.is_empty() {
            assert!(output.stderr.is_empty());
        } else {
            assert!(
                String::from_utf8_lossy(&output.stderr).ends_with(&format!("reason: {prefix}"))
            );
        }
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
    assert!(
        output
            .stderr
            .ends_with(b"reason: invocation.reserved-root\n")
    );
}

#[test]
fn direct_and_facade_paths_share_one_builtin_identity() {
    let tree = Tree::new();
    tree.write("facade.ash", "pub import @builtin.cell (Handle)\n");
    let entry = tree.write("entry.ash", "import facade as Wrapped\nimport @builtin.cell as Direct\nforward<R> : Wrapped.Handle<R> -> Direct.Handle<R>\nforward value = value\nmain : Unit -> Int\nmain () = 42\n");
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    assert_inventory(
        &graph,
        &[
            "@builtin.foreign",
            "@compiler.region",
            "@builtin.cell",
            "facade.ash",
            "entry.ash",
        ],
    );
    let builtin = module_named(&graph, "@builtin.cell").id();
    assert_eq!(
        module_named(&graph, "facade.ash").dependencies()[0].target(),
        builtin
    );
    assert_eq!(
        graph.module(graph.entry()).unwrap().dependencies()[1].target(),
        builtin
    );
}

#[test]
fn repeated_imported_hook_pipeline_forgets_completed_discard_histories() {
    let tree = Tree::new();
    // Reduced from ash-doc's repeated-hook-pipeline case: payload tagging,
    // normalization branching, and trace construction are unnecessary.
    tree.write(
        "pipeline.ash",
        r#"pub type Request = Request(Int)
pub type Steps = End
    | Step(Int, Steps)

pub type Result = Delivered(Request)
    | Rejected

effect Pipeline {
    publish : Request -> Request
}

effect Policy {
    check : Request -> Unit
}

effect Trace {
    stage : Int -> Unit
}

normalize : Request -> Request ! {Trace}
normalize (Request(priority)) = {
    let ignored = perform Trace.stage 1
    Request(1)
}

check_policy : Request -> Request ! {Policy, Trace}
check_policy request = {
    let ignored = perform Trace.stage 2
    let ignored = perform Policy.check request
    request
}

enrich : Request -> Request ! {Trace}
enrich (Request(priority)) = {
    let ignored = perform Trace.stage 3
    Request(priority)
}

publish_and_deliver : Request -> Result ! {Pipeline, Trace}
publish_and_deliver request = {
    let transformed = perform Pipeline.publish request
    let ignored = perform Trace.stage 4
    Delivered(transformed)
}

pipeline : Bool -> Result ! {Policy, Trace}
pipeline include_enrichment = hook Pipeline {
    register Pipeline normalize {
        register Pipeline check_policy {
            match include_enrichment {
                true => register Pipeline enrich {
                    publish_and_deliver (Request(0))
                }
                false => publish_and_deliver (Request(0))
            }
        }
    }
}

pub run : (Bool, Bool) -> (Result, Steps)
run (allow, include_enrichment) = handle {
    let result = handle (pipeline include_enrichment) with Policy {
        check request => match allow {
            true => resume ()
            false => {
                let ignored = discard
                Rejected
            }
        }
    }
    (result, End)
} with Trace {
    stage digit => {
        resume ()
    }
}
"#,
    );
    let entry = tree.write("entry.ash", r#"import @demo.pipeline as Pipeline
main : Unit -> ((Pipeline.Result, Pipeline.Steps), (Pipeline.Result, Pipeline.Steps), (Pipeline.Result, Pipeline.Steps))
main () = (Pipeline.run (true, true), Pipeline.run (false, true), Pipeline.run (true, false))
"#);
    let result = ash::driver::run_path(ash::driver::RunConfiguration {
        entry,
        roots: ModuleRoots::new([("demo", tree.0.clone())]).unwrap(),
    })
    .expect("three finite pipeline calls fit the ordinary work budget");
    assert_eq!(
        result.value().to_string(),
        "((Delivered(Request(1)), End), (Rejected, End), (Delivered(Request(1)), End))"
    );
}

#[test]
fn generic_cell_metadata_imports_and_facades_preserve_the_separate_family() {
    let tree = Tree::new();
    tree.write("facade.ash", "pub import @builtin.generic_cell (Cell as Access, Provider as Supply, Ops as Requests, read as get, write as put)\n");
    let entry = tree.write("entry.ash", "import facade as Wrapped\nimport @builtin.generic_cell as Direct\nimport @builtin.cell as Legacy\nmain : Unit -> Int\nmain () = 42\n");
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    assert_inventory(
        &graph,
        &[
            "@builtin.foreign",
            "@compiler.region",
            "@builtin.generic_cell",
            "facade.ash",
            "@builtin.cell",
            "entry.ash",
        ],
    );
    let generic = module_named(&graph, "@builtin.generic_cell").id();
    assert_eq!(
        module_named(&graph, "facade.ash").dependencies()[0].target(),
        generic
    );
    assert_eq!(
        graph.module(graph.entry()).unwrap().dependencies()[1].target(),
        generic
    );
    assert_ne!(
        graph.module(graph.entry()).unwrap().dependencies()[2].target(),
        generic
    );
}

#[test]
fn cell_n09_generic_provider_is_sealed_through_direct_and_facade_imports() {
    let tree = Tree::new();
    tree.write(
        "facade.ash",
        "pub import @builtin.generic_cell (Cell, Provider, Ops, read, write)\n",
    );
    for import in ["@builtin.generic_cell", "facade"] {
        for declaration in [
            "impl Cell.Provider<Int, Int> {\nread value = 1\nwrite value = ()\n}\n",
            "main : Unit -> Int\nmain () = {\nnewtype Local = Local(Int)\nwith Cell.Provider<Local, Int> {\nread value = 1\nwrite value = ()\n}\n42\n}\n",
        ] {
            let entry = tree.write(
                "entry.ash",
                &format!("import {import} as Cell\n{declaration}"),
            );
            let failure = ash::driver::compile_path(ash::driver::RunConfiguration {
                entry: entry.clone(),
                roots: ModuleRoots::empty(),
            })
            .unwrap_err();
            assert_eq!(failure.reason_code(), "resolve.sealed-provider");
            let ash::driver::FileFailure::Pipeline(context) = failure else {
                panic!("public resolver refusal")
            };
            assert!(matches!(
                context.failure(),
                ash::driver::PipelineFailure::Resolution(_)
            ));
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
                    let error = result.unwrap_err();
                    assert!(format!("{error:?}").contains("SealedProvider"), "{error:?}");
                } else {
                    checked.push(check_module(result.unwrap()).unwrap());
                }
            }
        }
    }
}

#[test]
fn cell_p05_imported_recursive_predecessor_relation_reconstructs_from_linked_code() {
    let tree = Tree::new();
    let helper = r#"import @builtin.generic_cell as Cell
pub visit : (Bool, Unit -> Int) -> Int
visit (again, initial) = resource Cell.Cell<R,(Unit -> Int)> c = initial {
    match again {
        true => {
            let next : Unit -> Int = fn(ignored) {
                let held = c
                9
            }
            visit (false,next)
        }
        false => {
            let saved = Cell.read c
            saved ()
        }
    }
}
"#;
    tree.write("helper.ash", helper);
    let entry = tree.write("entry.ash", "import helper (visit)\ninitial : Unit -> Int\ninitial () = 7\nmain : Unit -> Int\nmain () = visit (true,initial)\n");
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    check(&graph);
    ash::driver::compile_path(ash::driver::RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("imported recursive predecessor proof must rebuild from linked code");
}

#[test]
fn cell_p06_facade_aliases_and_conditional_write_summary_keep_all_targets_and_payloads() {
    let tree = Tree::new();
    tree.write("helper.ash", "import @builtin.generic_cell as Cell\npub get<R,T> : Cell.Cell<R,T> -> T ! {Cell.Ops<R,T>} where Cell.Provider<R,T>\nget c = Cell.read c\npub put<R,T> : (Cell.Cell<R,T>,T) -> Unit ! {Cell.Ops<R,T>} where Cell.Provider<R,T>\nput pair = Cell.write pair\n");
    tree.write(
        "facade.ash",
        "pub import helper (get,put)\npub import @builtin.generic_cell (Cell as Access)\n",
    );
    let entry = tree.write("entry.ash", "import facade as F\nmain : Unit -> Int\nmain () = resource F.Access<R,Int> c = 41 {\nlet alias = c\nlet selected = match true {\ntrue => c\nfalse => alias\n}\nlet _ = F.put (selected,42)\nF.get c\n}\n");
    ash::driver::compile_path(ash::driver::RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("facade and same-owner alias branches preserve conditional flow");
    tree.write("entry.ash", "import facade as F\nindependent : Unit -> Int\nindependent () = 7\nmain : Unit -> Int\nmain () = resource F.Access<A,(Unit -> Int)> a = independent {\nresource F.Access<B,Int> b = 41 {\nlet bad : Unit -> Int = fn(ignored) {\nlet held = b\n42\n}\nlet _ = F.put (a,bad)\n42\n}\n}\n");
    let error = ash::driver::compile_path(ash::driver::RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .unwrap_err();
    assert_eq!(error.reason_code(), "type.resource-escape");
    let ash::driver::FileFailure::Pipeline(context) = &error else {
        panic!("source dependency phase")
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(diagnostic)) =
        context.failure()
    else {
        panic!("source dependency reason: {error:?}")
    };
    let refs = error.sources().iter().collect::<Vec<_>>();
    let presented = ash::presentation::compile_type_diagnostic(diagnostic, &refs)
        .expect("imported capture/call labels must compile for presentation");
    let mut json = Vec::new();
    ash::presentation::write_json(&mut json, &presented).unwrap();
    assert!(!json.is_empty());
    for locale in [
        ash::message::Locale::English,
        ash::message::Locale::Bulgarian,
    ] {
        let mut text = Vec::new();
        let catalogue = ash::message::Catalogue::new(locale).unwrap();
        ash::presentation::write_human(&mut text, &presented, &catalogue).unwrap();
        assert!(!text.is_empty());
    }
    let text = |span: ash::source::Span| {
        let source = error
            .sources()
            .iter()
            .find(|source| source.id() == span.source())
            .unwrap();
        &source.text()[span.range().start() as usize..span.range().end() as usize]
    };
    assert!(text(diagnostic.primary.span()).contains("Cell.write pair"));
    for (label, fragment) in [
        ("acquired", "resource F.Access<A"),
        ("carries the retained dependency", "let held = b"),
        ("call propagates", "F.put (a,bad)"),
    ] {
        assert!(
            diagnostic
                .related
                .iter()
                .any(|related| related.message().contains(label)
                    && text(related.span()).contains(fragment)),
            "missing {label}: {diagnostic:?}"
        );
    }
}
