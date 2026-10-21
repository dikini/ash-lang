//! Static checked-owner lifecycle correspondence; no native execution.

#[test]
fn checked_owner_lifecycle_source_fixture_loads() {
    let entry = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/checked-owner-lifecycle/owner.ash");
    let graph = ash::module::load_module_graph(&entry, &ash::module::ModuleRoots::empty())
        .expect("the canonical checked_scope source fixture must parse and project");
    let source = graph.module(graph.entry()).unwrap();
    assert_eq!(source.surface().source_resources.len(), 1);
    assert_eq!(source.surface().foreign_libraries.len(), 1);
}

#[test]
fn checked_owner_lifecycle_source_checks_under_exact_host() {
    let entry = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/checked-owner-lifecycle/owner.ash");
    let graph = ash::module::load_module_graph(&entry, &ash::module::ModuleRoots::empty())
        .expect("the checked lifecycle fixture must load before source admission");
    let mut checked: Vec<ash::resolved::CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                let producer = checked
                    .iter()
                    .find(|module| module.module() == edge.target())
                    .unwrap();
                ash::resolve::DependencyExports::new(edge, producer.exports()).unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = ash::resolve::resolve_checked_foreign_module(loaded, &dependencies).expect(
            "exact checked owner/resource originals must resolve before lifecycle checking",
        );
        checked.push(
            ash::elaborate::check_module(resolved)
                .expect("canonical checked owner lifecycle must pass source phase checking"),
        );
    }
    assert_eq!(checked.len(), graph.modules().len());
}

struct TemporarySource(std::path::PathBuf);
impl TemporarySource {
    fn new(source: &str) -> Self {
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let directory = std::env::temp_dir().join(format!(
            "ash-checked-lifecycle-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let path = directory.join("owner.ash");
        std::fs::write(&path, source).unwrap();
        Self(path)
    }
    fn graph(&self) -> ash::module::ModuleGraph {
        ash::module::load_module_graph(&self.0, &ash::module::ModuleRoots::empty()).unwrap()
    }
}
impl Drop for TemporarySource {
    fn drop(&mut self) {
        std::fs::remove_dir_all(self.0.parent().unwrap()).unwrap();
    }
}

#[test]
fn checked_owner_lifecycle_fallible_scalar_finish_does_not_borrow_void_refinement() {
    let source = include_str!("fixtures/checked-owner-lifecycle/owner.ash");
    let original = source.split("\npub type Acquire").next().unwrap();
    let fallible = original
        .replace(
            "symbol Free<H, R> : State<H, R> ->",
            "symbol Free<H, R> : (State<H, R>, Int) ->",
        )
        .replace(
            "abi (pointer(Address)) -> void",
            "abi (pointer(Address), Size) -> void",
        )
        .replace(
            "operand 0 from 0 current",
            "operand 0 from 0 current\n        operand 1 from 1 scalar",
        )
        .replace(
            "output result as owner(State<H, R>)",
            "destruction_operand 1 from 0 scalar\n        output result as owner(State<H, R>)",
        );
    assert_ne!(fallible, original);
    let passive = TemporarySource::new(&format!(
        "{fallible}\npub idle : Unit -> Int\nidle () = 42\n"
    ));
    let graph = passive.graph();
    let producer = graph.module(graph.entry()).unwrap();
    let prepared = ash::foreign::source_contract::prepare_checked_foreign_library(
        producer.id(),
        &producer.surface().foreign_libraries[0],
    )
    .expect("the actual fallible scalar teardown prepares canonically");
    assert_eq!(prepared.symbols()[1].operands().len(), 2);
    let mut checked: Vec<ash::resolved::CheckedModule> = Vec::new();
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
            .expect("fallible scalar teardown originals bind before lifecycle use");
        checked.push(
            ash::elaborate::check_module(resolved).expect("passive fallible contract checks"),
        );
    }
    let lifecycle = source.replacen(original, &fallible, 1).replace(
        "perform Free<H, R>.call state",
        "perform Free<H, R>.call (state, 7)",
    );
    let fixture = TemporarySource::new(&lifecycle);
    let graph = fixture.graph();
    let mut checked: Vec<ash::resolved::CheckedModule> = Vec::new();
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
        let resolved = ash::resolve::resolve_checked_foreign_module(loaded, &dependencies).expect(
            "the real scalar conversion contract resolves before its unsupported lifecycle",
        );
        match ash::elaborate::check_module(resolved) {
            Ok(module) => checked.push(module),
            Err(ash::elaborate::TypeError::Source(error)) => {
                assert_eq!(loaded.id(), graph.entry());
                assert_eq!(error.reason, ash::elaborate::TypeReason::Argument);
                let message = format!("{error:?}");
                assert!(
                    message.contains("source resource header requires matching owned state"),
                    "{message}"
                );
                assert!(!message.contains("ResourceExhausted"), "{message}");
                return;
            }
            Err(error) => {
                panic!("unsupported scalar lifecycle must reject semantically: {error:?}")
            }
        }
    }
    panic!("fallible scalar conversion cannot use the State-only void finish refinement");
}
