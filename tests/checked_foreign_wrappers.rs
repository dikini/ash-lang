use ash::{module::ModuleRoots, resolved::CheckedModule};
use std::{
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

const LIBRARY: &str = r#"import @builtin.foreign as Foreign
foreign checked library Native {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    assumption Callee "the admitted callee follows its declared native contract"
    symbol Abs<Before : EffectRow, H, T, After : EffectRow> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (I32) -> I32
        host H
        assumes { Callee }
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
"#;

const DIRECT: &str = r#"pub call<Before : EffectRow, H, T, After : EffectRow> : (T, Int) -> Foreign.CheckedCall<Int> ! {Abs<{| Before}, H, T, {| After}>, Foreign.NativeHost<H>}
call (unused, value) = perform Abs<{| Before}, H, T, {| After}>.call value
"#;

const CLOSED: &str = r#"pub closed<T> : T -> Foreign.CheckedCall<Int>
closed unused = foreign host Local {
    perform Abs<{}, Local, T, {}>.call 1
}
"#;

struct Fixture(PathBuf);
impl Fixture {
    fn new(producer: &str, entry: &str) -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let directory = std::env::temp_dir().join(format!(
            "ash-checked-wrappers-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&directory).unwrap();
        std::fs::write(directory.join("native.ash"), producer).unwrap();
        std::fs::write(directory.join("entry.ash"), entry).unwrap();
        Self(directory)
    }
    fn graph(&self) -> ash::module::ModuleGraph {
        ash::module::load_module_graph(&self.0.join("entry.ash"), &ModuleRoots::empty()).unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn checked_with_profile(
    graph: &ash::module::ModuleGraph,
    checked_profile: bool,
) -> Vec<CheckedModule> {
    let mut checked: Vec<CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                ash::resolve::DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = if checked_profile {
            ash::resolve::resolve_checked_foreign_module(loaded, &dependencies)
        } else {
            ash::resolve::resolve_module(loaded, &dependencies)
        }
        .unwrap_or_else(|error| panic!("{} resolution: {error:?}", loaded.source().display_path()));
        checked.push(
            ash::elaborate::check_module(resolved).unwrap_or_else(|error| {
                panic!("{} checking: {error:?}", loaded.source().display_path())
            }),
        );
    }
    checked
}

fn core(graph: &ash::module::ModuleGraph) -> ash::core::ValidatedEffectProgram {
    core_with_profile(graph, true)
}

fn core_with_profile(
    graph: &ash::module::ModuleGraph,
    checked_profile: bool,
) -> ash::core::ValidatedEffectProgram {
    let linked =
        ash::elaborate::link_modules(checked_with_profile(graph, checked_profile), graph.entry())
            .unwrap();
    let linked = ash::evidence_validation::validate_interface_evidence(linked).unwrap();
    let mut elaborator = ash::elaborate::EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap();
    let program = elaborator.finish(typed.node).unwrap();
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    ash::core::validate_effect_modules(program, &sources, &modules).unwrap()
}

#[test]
fn checked_imported_generic_wrapper_preserves_complete_actuals_through_core() {
    let fixture = Fixture::new(
        &format!("{LIBRARY}{DIRECT}")
            .replace("foreign checked library", "pub foreign checked library"),
        "import @builtin.foreign as Foreign\nimport native as Native\neffect First {\n    first : Unit -> Unit\n}\neffect Last {\n    last : Unit -> Unit\n}\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = foreign host Session {\n    let invoke : (Bool, Int) -> Foreign.CheckedCall<Int> ! {Native.Abs<{First}, Session, Bool, {Last}>, Foreign.NativeHost<Session>} = Native.call\n    invoke (true, 1)\n}\n",
    );
    let graph = fixture.graph();
    let _ = core(&graph);
}

#[test]
fn checked_closed_wrapper_keeps_internal_host_bound_across_two_instantiations() {
    let fixture = Fixture::new(
        &format!("{LIBRARY}{CLOSED}"),
        "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> (Foreign.CheckedCall<Int>, Foreign.CheckedCall<Int>)\nmain () = (Native.closed 1, Native.closed true)\n",
    );
    let graph = fixture.graph();
    let _ = core(&graph);
}

#[test]
fn checked_closed_wrapper_requires_opt_in_for_a_body_free_consumer() {
    let fixture = Fixture::new(
        &format!("{LIBRARY}{CLOSED}"),
        "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = Native.closed 1\n",
    );
    let graph = fixture.graph();
    let mut producers: Vec<CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        // Only immutable export summaries enter consumer checking. Producer
        // executable bodies are supplied separately by core() at linking.
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                ash::resolve::DependencyExports::new(
                    edge,
                    producers
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        if loaded.id() == graph.entry() {
            let error = match ash::resolve::resolve_module(loaded, &dependencies) {
                Err(error) => error,
                Ok(_) => {
                    panic!("a closed outward row cannot erase the checked profile requirement")
                }
            };
            assert!(
                matches!(error, ash::resolve::ResolveModuleError::Resolution(error) if error.reason == ash::resolve::ResolveReason::ForeignContract)
            );
            return;
        }
        let resolved = ash::resolve::resolve_checked_foreign_module(loaded, &dependencies).unwrap();
        producers.push(ash::elaborate::check_module(resolved).unwrap());
    }
    panic!("consumer module missing");
}

#[test]
fn checked_closed_wrapper_reexport_preserves_its_original_host_contract() {
    let fixture = Fixture::new(
        &format!("{LIBRARY}{CLOSED}"),
        "import @builtin.foreign as Foreign\nimport facade as Facade\nmain : Unit -> (Foreign.CheckedCall<Int>, Foreign.CheckedCall<Int>)\nmain () = (Facade.wrapped 1, Facade.wrapped true)\n",
    );
    std::fs::write(
        fixture.0.join("facade.ash"),
        "pub import native (closed as wrapped)\n",
    )
    .unwrap();
    let graph = fixture.graph();
    let _ = core(&graph);
}

#[test]
fn checked_opaque_snapshot_keeps_native_requirements_without_constructor_access() {
    let producer = format!(
        "{LIBRARY}pub opaque type Token = HiddenToken\npub snapshot : Unit -> Token\nsnapshot () = {{\n    let ignored = foreign host Local {{\n        perform Abs<{{}}, Local, Int, {{}}>.call 1\n    }}\n    HiddenToken\n}}\n"
    );
    let fixture = Fixture::new(
        &producer,
        "import native as Native\nmain : Unit -> Native.Token\nmain () = Native.snapshot ()\n",
    );
    let graph = fixture.graph();
    let _ = core(&graph);
    std::fs::write(
        fixture.0.join("entry.ash"),
        "import native as Native\nmain : Unit -> Native.Token\nmain () = Native.HiddenToken\n",
    )
    .unwrap();
    let graph = fixture.graph();
    let mut producers: Vec<CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                ash::resolve::DependencyExports::new(
                    edge,
                    producers
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        if loaded.id() == graph.entry() {
            assert!(
                ash::resolve::resolve_checked_foreign_module(loaded, &dependencies).is_err(),
                "opaque constructor must remain inaccessible"
            );
            return;
        }
        producers.push(
            ash::elaborate::check_module(
                ash::resolve::resolve_checked_foreign_module(loaded, &dependencies).unwrap(),
            )
            .unwrap(),
        );
    }
    panic!("consumer module missing");
}

#[test]
fn checked_branch_only_native_dependencies_survive_a_closed_host_row() {
    let library = format!(
        "{}    assumption OtherCallee \"the other admitted contract holds\"\n    symbol Other<Before : EffectRow, H, T, After : EffectRow> : Int -> Foreign.CheckedCall<Int> {{\n        name \"abs\"\n        abi (I32) -> I32\n        host H\n        assumes {{ OtherCallee }}\n        operand 0 from 0 scalar\n        output result as scalar\n        outcome otherwise {{ readable result }}\n    }}\n}}\n",
        LIBRARY.trim_end().strip_suffix('}').unwrap()
    );
    let producer = format!(
        "{library}pub choose : Bool -> Foreign.CheckedCall<Int>\nchoose first = foreign host Local {{\n    match first {{\n        true => perform Abs<{{}}, Local, Int, {{}}>.call 1\n        false => perform Other<{{}}, Local, Bool, {{}}>.call 2\n    }}\n}}\n"
    );
    let fixture = Fixture::new(
        &producer,
        "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = Native.choose false\n",
    );
    let graph = fixture.graph();
    let _ = core(&graph);
}

#[test]
fn checked_recursive_wrapper_retains_its_private_closed_callee() {
    let producer = format!(
        "{LIBRARY}{}pub repeat : Int -> Foreign.CheckedCall<Int>\nrepeat count = match count == 0 {{\n    true => closed count\n    false => repeat 0\n}}\n",
        CLOSED.replace("pub closed", "closed")
    );
    let fixture = Fixture::new(
        &producer,
        "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = Native.repeat 1\n",
    );
    let graph = fixture.graph();
    let _ = core(&graph);
}

#[test]
fn checked_higher_order_wrapper_retains_its_private_closed_callee() {
    let producer = format!(
        "{LIBRARY}{}pub select : Bool -> (Int -> Foreign.CheckedCall<Int>)\nselect first = match first {{\n    true => closed\n    false => fn(value) {{\n        closed value\n    }}\n}}\n",
        CLOSED.replace("pub closed", "closed")
    );
    let fixture = Fixture::new(
        &producer,
        "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = (Native.select false) 1\n",
    );
    let graph = fixture.graph();
    let _ = core(&graph);
}

#[test]
fn legacy_native_wrapper_summary_remains_valid_without_checked_opt_in() {
    let library = LIBRARY
        .replace("foreign checked library", "foreign library")
        .replace(
            "    assumption Callee \"the admitted callee follows its declared native contract\"\n",
            "",
        )
        .replace("        host H\n", "")
        .replace("        assumes { Callee }\n", "")
        .replace("Foreign.CheckedCall", "Foreign.Call");
    let direct = DIRECT
        .replace("Foreign.CheckedCall", "Foreign.Call")
        .replace(", Foreign.NativeHost<H>", "");
    let fixture = Fixture::new(
        &format!("{library}{direct}"),
        "import native as Native\nmain : Unit -> Int\nmain () = 42\n",
    );
    let graph = fixture.graph();
    let _ = core_with_profile(&graph, false);
}

#[test]
fn checked_imported_wrapper_rejects_a_reordered_host_actual() {
    let fixture = Fixture::new(
        &format!("{LIBRARY}{DIRECT}")
            .replace("foreign checked library", "pub foreign checked library"),
        "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = foreign host Session {\n    let invoke : (Bool, Int) -> Foreign.CheckedCall<Int> ! {Native.Abs<{}, Bool, Session, {}>, Foreign.NativeHost<Bool>} = Native.call\n    invoke (true, 1)\n}\n",
    );
    let graph = fixture.graph();
    let mut producers: Vec<CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                ash::resolve::DependencyExports::new(
                    edge,
                    producers
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = ash::resolve::resolve_checked_foreign_module(loaded, &dependencies).unwrap();
        let result = ash::elaborate::check_module(resolved);
        if loaded.id() == graph.entry() {
            assert!(
                result.is_err(),
                "a complete native actual vector cannot exchange H and another Type argument"
            );
            return;
        }
        producers.push(result.unwrap());
    }
    panic!("consumer module missing");
}

#[test]
fn checked_selected_module_method_prerequisites_preserve_body_free_core() {
    let methods = r#"pub type Box<A> = Box(A)
pub interface Read<A> {
    read : A -> Foreign.CheckedCall<Int>
}
pub impl Read<Int> {
    read value = closed value
}
pub impl<A> Read<Box<A>> where Read<A> {
    read (Box value) = read value
}
pub invoke<A> : A -> Foreign.CheckedCall<Int> where Read<A>
invoke value = read value
"#;
    let fixture = Fixture::new(
        &format!(
            "{}{}{}",
            LIBRARY,
            methods,
            CLOSED.replace("pub closed", "closed")
        ),
        "import @builtin.foreign as Foreign\nimport native as Native\nimport native (impl Read)\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = Native.invoke (Native.Box (Native.Box 7))\n",
    );
    let graph = fixture.graph();
    let _ = core(&graph);
}

#[test]
fn checked_selected_module_direct_method_preserves_body_free_core() {
    let methods = r#"pub interface Read<A> {
    read : A -> Foreign.CheckedCall<Int>
}
pub impl Read<Int> {
    read value = closed value
}
"#;
    let fixture = Fixture::new(
        &format!(
            "{}{}{}",
            LIBRARY,
            methods,
            CLOSED.replace("pub closed", "closed")
        ),
        "import @builtin.foreign as Foreign\nimport native as Native\nimport native (impl Read)\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = Native.read 7\n",
    );
    let graph = fixture.graph();
    let _ = core(&graph);
}

#[test]
fn checked_selected_opaque_prerequisite_reexport_preserves_two_contract_core() {
    let fixture = Fixture::new(
        include_str!("fixtures/checked-foreign-selected/native.ash"),
        "import @builtin.foreign as Foreign\nimport facade as Facade\nimport facade (impl Read)\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = Facade.invoke (Facade.wrap (Facade.wrap (Facade.before, Facade.after)))\n",
    );
    std::fs::write(
        fixture.0.join("facade.ash"),
        "pub import native (Box, wrap, Read, read, invoke, before, after, impl Read)\n",
    )
    .unwrap();
    let _ = core(&fixture.graph());
}

#[test]
fn checked_selected_method_only_requires_body_free_consumer_opt_in() {
    let methods = "pub interface Read<A> {\n    read : A -> Foreign.CheckedCall<Int>\n}\npub impl Read<Int> {\n    read value = closed value\n}\n";
    let fixture = Fixture::new(
        &format!(
            "{LIBRARY}{methods}{}",
            CLOSED.replace("pub closed", "closed")
        ),
        "import @builtin.foreign as Foreign\nimport native as Native\nimport native (impl Read)\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = Native.read 7\n",
    );
    let graph = fixture.graph();
    let mut producers: Vec<CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                ash::resolve::DependencyExports::new(
                    edge,
                    producers
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        if loaded.id() == graph.entry() {
            assert!(
                matches!(ash::resolve::resolve_module(loaded, &dependencies),
                Err(ash::resolve::ResolveModuleError::Resolution(error))
                if error.reason == ash::resolve::ResolveReason::ForeignContract)
            );
            return;
        }
        producers.push(
            ash::elaborate::check_module(
                ash::resolve::resolve_checked_foreign_module(loaded, &dependencies).unwrap(),
            )
            .unwrap(),
        );
    }
    panic!("consumer module missing");
}
