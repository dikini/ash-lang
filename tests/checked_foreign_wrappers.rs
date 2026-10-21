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

fn checked(graph: &ash::module::ModuleGraph) -> Vec<CheckedModule> {
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
        let resolved = ash::resolve::resolve_checked_foreign_module(loaded, &dependencies)
            .unwrap_or_else(|error| {
                panic!("{} resolution: {error:?}", loaded.source().display_path())
            });
        checked.push(
            ash::elaborate::check_module(resolved).unwrap_or_else(|error| {
                panic!("{} checking: {error:?}", loaded.source().display_path())
            }),
        );
    }
    checked
}

fn core(graph: &ash::module::ModuleGraph) -> ash::core::ValidatedEffectProgram {
    let linked = ash::elaborate::link_modules(checked(graph), graph.entry()).unwrap();
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
        "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = foreign host Session {\n    let invoke : (Bool, Int) -> Foreign.CheckedCall<Int> ! {Native.Abs<{}, Session, Bool, {}>, Foreign.NativeHost<Session>} = Native.call\n    invoke (true, 1)\n}\n",
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
