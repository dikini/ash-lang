//! Ordinary body-free declaration closure and private callee linkage regressions.
use ash::{module::ModuleRoots, resolved::CheckedModule};
use std::{
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

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
    let mut saw_consumer = false;
    for loaded in graph.modules() {
        // Consumer resolution receives immutable export summaries only. Producer
        // executable bodies enter separately below when linking the checked graph.
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
        let resolved =
            ash::resolve::resolve_module(loaded, &dependencies).unwrap_or_else(|error| {
                panic!("{} resolution: {error:?}", loaded.source().display_path())
            });
        if loaded.id() == graph.entry() {
            assert!(
                !dependencies.is_empty(),
                "the consumer must use detached summaries"
            );
            saw_consumer = true;
        }
        checked.push(
            ash::elaborate::check_module(resolved).unwrap_or_else(|error| {
                panic!("{} checking: {error:?}", loaded.source().display_path())
            }),
        );
    }
    assert!(saw_consumer);
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

fn assert_core_and_transforms(graph: &ash::module::ModuleGraph, expected: &str) {
    let valid = core(graph);
    assert_eq!(
        ash::eval::evaluate_effect(&valid)
            .unwrap()
            .value
            .to_string(),
        expected
    );
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
    let identity = ash::core::transform::identity_effect_traversal(&valid).unwrap();
    let identity = ash::core::validate_effect_modules(identity, &sources, &modules).unwrap();
    assert_eq!(
        ash::eval::evaluate_effect(&identity)
            .unwrap()
            .value
            .to_string(),
        expected
    );
    let folded = ash::core::transform::fold_effect_literal_primitives(&identity).unwrap();
    let folded = ash::core::validate_effect_modules(folded, &sources, &modules).unwrap();
    assert_eq!(
        ash::eval::evaluate_effect(&folded)
            .unwrap()
            .value
            .to_string(),
        expected
    );
}

fn assert_private_names(fixture: &Fixture, module: &str, names: &[&str]) {
    let entry = fixture.0.join("entry.ash");
    let original = std::fs::read_to_string(&entry).unwrap();
    for name in names {
        std::fs::write(
            &entry,
            format!("import {module} ({name})\nmain : Unit -> Int\nmain () = 0\n"),
        )
        .unwrap();
        let failure = ash::driver::compile_path(ash::driver::RunConfiguration {
            entry: entry.clone(),
            roots: ModuleRoots::empty(),
        })
        .expect_err("retained hidden metadata must not publish a source name");
        assert!(
            matches!(failure.pipeline_failure(),
            Some(ash::driver::PipelineFailure::Resolution(error)) if error.reason==ash::resolve::ResolveReason::UnavailableExport),
            "{module}.{name}: {failure:?}"
        );
    }
    std::fs::write(entry, original).unwrap();
}

const CAPTURE: &str = r"type Held = Held(Int)
type Spare = Spare(Int)
closed<T> : (T, Int) -> Int
closed (unused, value) = value
pub select : Int -> (Unit -> Int)
select value = {
    let held = Held value
    fn(ignored) {
        match held {
            Held(captured) => closed (held, captured)
        }
    }
}
";
const LEAF: &str = r"type Leaf = Leaf(Int)
type Donor = Donor(Int)
type Spare = Spare(Int)
pub type Envelope = Envelope(Leaf)
pub type Witness = Witness(Donor)
closed : Int -> Int
closed value = value
pub make : Int -> Envelope
make value = Envelope (Leaf value)
pub inspect : Envelope -> Int
inspect envelope = match envelope {
    Envelope(Leaf(value)) => closed value
}
";

#[test]
fn branch_only_private_callees_survive_body_free_consumer_and_core() {
    let fixture = Fixture::new(
        r"closed : Int -> Int
closed value = value + 1
other : Int -> Int
other value = value + 2
pub choose : Bool -> Int
choose first = match first {
    true => closed 41
    false => other 41
}
",
        "import native as Native\nmain : Unit -> (Int, Int)\nmain () = (Native.choose true, Native.choose false)\n",
    );
    assert_core_and_transforms(&fixture.graph(), "(42, 43)");
    assert_private_names(&fixture, "native", &["closed", "other"]);
}

#[test]
fn recursive_wrapper_retains_its_private_callee_through_core_transforms() {
    let fixture = Fixture::new(
        r"closed : Int -> Int
closed value = value + 41
pub repeat : Int -> Int
repeat count = match count == 0 {
    true => closed 1
    false => repeat 0
}
",
        "import native as Native\nmain : Unit -> Int\nmain () = Native.repeat 1\n",
    );
    assert_core_and_transforms(&fixture.graph(), "42");
    assert_private_names(&fixture, "native", &["closed"]);
}

#[test]
fn higher_order_wrapper_retains_its_private_callee_through_core_transforms() {
    let fixture = Fixture::new(
        r"closed : Int -> Int
closed value = value + 1
pub select : Bool -> (Int -> Int)
select first = match first {
    true => closed
    false => fn(value) {
        closed (value + 1)
    }
}
",
        "import native as Native\nmain : Unit -> (Int, Int)\nmain () = ((Native.select true) 41, (Native.select false) 41)\n",
    );
    assert_core_and_transforms(&fixture.graph(), "(42, 43)");
    assert_private_names(&fixture, "native", &["closed"]);
}

#[test]
fn capture_only_private_nominal_survives_body_free_consumer_and_core() {
    let fixture = Fixture::new(
        CAPTURE,
        "import native as Native\nmain : Unit -> Int\nmain () = {\n    let call = Native.select 7\n    call ()\n}\n",
    );
    assert_core_and_transforms(&fixture.graph(), "7");
    assert_private_names(&fixture, "native", &["Held", "Spare", "closed"]);
}

#[test]
fn capture_only_private_nominal_survives_hidden_reexport() {
    let fixture = Fixture::new(
        CAPTURE,
        "import facade as Facade\nmain : Unit -> Int\nmain () = {\n    let call = Facade.wrapped 7\n    call ()\n}\n",
    );
    std::fs::write(
        fixture.0.join("facade.ash"),
        "pub import native (select as wrapped)\n",
    )
    .unwrap();
    assert_core_and_transforms(&fixture.graph(), "7");
    assert_private_names(&fixture, "facade", &["Held", "Spare", "closed", "select"]);
}

#[test]
fn selected_capture_only_private_nominal_survives_body_free_core() {
    let producer = format!(
        "{}pub interface Read<A> {{\n    read : A -> (Unit -> Int)\n}}\npub impl Read<Int> {{\n    read value = select value\n}}\n",
        CAPTURE.replace("pub select", "select")
    );
    let fixture = Fixture::new(
        &producer,
        "import native as Native\nimport native (impl Read)\nmain : Unit -> Int\nmain () = {\n    let call = Native.read 7\n    call ()\n}\n",
    );
    assert_core_and_transforms(&fixture.graph(), "7");
    assert_private_names(&fixture, "native", &["Held", "Spare", "closed", "select"]);
}

#[test]
fn constructor_payload_private_leaf_survives_body_free_consumer_and_core() {
    let fixture = Fixture::new(
        LEAF,
        "import native as Native\nmain : Unit -> Int\nmain () = Native.inspect (Native.make 7)\n",
    );
    assert_core_and_transforms(&fixture.graph(), "7");
    assert_private_names(&fixture, "native", &["Leaf", "Donor", "Spare", "closed"]);
}

#[test]
fn constructor_payload_private_leaf_survives_renamed_reexport() {
    let fixture = Fixture::new(
        LEAF,
        "import facade as Facade\nmain : Unit -> Int\nmain () = Facade.read (Facade.build 7)\n",
    );
    std::fs::write(
        fixture.0.join("facade.ash"),
        "pub import native (Envelope as Packet, make as build, inspect as read)\n",
    )
    .unwrap();
    assert_core_and_transforms(&fixture.graph(), "7");
    assert_private_names(
        &fixture,
        "facade",
        &[
            "Leaf", "Donor", "Spare", "closed", "Envelope", "make", "inspect",
        ],
    );
}
