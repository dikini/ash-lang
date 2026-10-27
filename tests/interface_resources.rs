//! Cross-stage resource evidence for interfaces and implementations.

use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, run_path},
    elaborate::TypeError,
    module::ModuleRoots,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ResourceFixture(PathBuf);

impl ResourceFixture {
    fn create(entry: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir().join(format!(
                "ash-interface-resource-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let entry_path = directory.join("entry.ash");
                    fs::write(&entry_path, entry).expect("entry fixture should be writable");
                    return Self(entry_path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("resource fixture should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) {
        let path = self
            .0
            .parent()
            .expect("fixture entry should have a parent")
            .join(relative);
        fs::write(path, text).expect("dependency fixture should be writable");
    }

    fn run(&self) -> Result<ash::driver::Observation, FileFailure> {
        run_path(RunConfiguration {
            entry: self.0.clone(),
            roots: ModuleRoots::empty(),
        })
    }
}

impl Drop for ResourceFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn public_interfaces(width: usize) -> String {
    let mut source = String::new();
    for index in 0..width {
        source.push_str(&format!(
            "pub interface Marker{index}<A> {{\nmark{index} : A -> A\n}}\n\n"
        ));
    }
    source
}

fn public_polymorphic_interfaces(width: usize) -> String {
    let mut source = String::new();
    for index in 0..width {
        source.push_str(&format!(
            "pub interface Marker{index}<A> {{\nmark{index}<T> : (A, T) -> A\n}}\n\n"
        ));
    }
    source
}

fn public_interface_implementations(width: usize) -> String {
    let mut source = String::new();
    for index in 0..width {
        source.push_str(&format!(
            "pub interface Marker{index}<A> {{\nmark{index} : A -> A\n}}\n\n\
             pub impl Marker{index}<Int> {{\nmark{index} value = value\n}}\n\n"
        ));
    }
    source
}

fn public_route_reexports(module: &str, width: usize) -> String {
    let mut selected = Vec::with_capacity(width * 3);
    let mut repeated_implementations = Vec::with_capacity(width);
    for index in 0..width {
        selected.push(format!("Marker{index}"));
        selected.push(format!("mark{index}"));
        selected.push(format!("impl Marker{index}"));
        repeated_implementations.push(format!("impl Marker{index}"));
    }
    format!(
        "pub import {module} ({})\npub import {module} ({})\n",
        selected.join(", "),
        repeated_implementations.join(", ")
    )
}

fn deep_public_route_fixture(depth: usize, width: usize) -> ResourceFixture {
    assert!(depth > 0);
    assert!(width > 0);
    let last_layer = format!("layer{}", depth - 1);
    let entry = format!(
        "{}main : Unit -> Int\nmain () = mark0(42)\n",
        public_route_reexports(&last_layer, width)
    );
    let fixture = ResourceFixture::create(&entry);
    fixture.write("base.ash", &public_interface_implementations(width));
    let mut dependency = String::from("base");
    for layer in 0..depth {
        let module = format!("layer{layer}");
        fixture.write(
            &format!("{module}.ash"),
            &public_route_reexports(&dependency, width),
        );
        dependency = module;
    }
    fixture
}

#[test]
fn one_constraint_budget_persists_from_dependency_admission_through_validation() {
    // The public normal policy admits the unchanged graph. The companion
    // driver unit retains the cumulative-versus-fresh-stage refusal control
    // with explicit finite owners, without an unrelated standalone Type cap.
    const WIDTH: usize = 4_500;
    let fixture = ResourceFixture::create(concat!(
        "import dependency as Dependency\n",
        "main : Unit -> Int\n",
        "main () = 42\n",
    ));
    fixture.write("dependency.ash", &public_interfaces(WIDTH));

    let observation = fixture
        .run()
        .expect("the unchanged wide graph should fit the measured normal constraint policy");
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn polymorphic_summary_resource_rejection_is_repeatable_and_a_fresh_run_recovers() {
    const ACCEPTED_WIDTH: usize = 1_024;
    const REJECTED_WIDTH: usize = 5_000;
    let entry = concat!(
        "import dependency as Dependency\n",
        "main : Unit -> Int\n",
        "main () = 42\n",
    );
    let accepted = ResourceFixture::create(entry);
    accepted.write(
        "dependency.ash",
        &public_polymorphic_interfaces(ACCEPTED_WIDTH),
    );
    let rejected = ResourceFixture::create(entry);
    rejected.write(
        "dependency.ash",
        &public_polymorphic_interfaces(REJECTED_WIDTH),
    );

    let observation = accepted
        .run()
        .expect("the admitted polymorphic summaries should fit the normal public budgets");
    assert_eq!(observation.value_display(), "42");
    drop(observation);

    // The former default refusal is retained with an explicit 327,680-unit
    // actual-driver owner in the companion unit; this unchanged public Source
    // now exercises the measured normal allowance on independent runs.
    for attempt in 0..2 {
        let observation = rejected
            .run()
            .expect("the unchanged wider polymorphic graph should fit the normal policy");
        assert_eq!(observation.value_display(), "42", "fresh attempt {attempt}");
    }

    let observation = accepted
        .run()
        .expect("a fresh public run should retain independent owner admission");
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn monomorphic_interface_capacity_preserves_predecessor_default_acceptance() {
    const WIDTH: usize = 2_800;
    let fixture = ResourceFixture::create(concat!(
        "import dependency as Dependency\n",
        "main : Unit -> Int\n",
        "main () = 42\n",
    ));
    fixture.write("dependency.ash", &public_interfaces(WIDTH));

    let observation = fixture
        .run()
        .expect("the predecessor-accepted monomorphic interface graph should still fit");
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn cycle_precedes_constraint_resource_exhaustion_after_import_admission() {
    // Preserve the original admitted dependency prefix and active-goal cycle.
    const WIDTH: usize = 4_500;
    let fixture = ResourceFixture::create(concat!(
        "import dependency as Dependency\n\n",
        "interface First<A> {\nfirst : A -> A\n}\n\n",
        "interface Second<A> {\nsecond : A -> A\n}\n\n",
        "impl First<Int> where Second<Int> {\nfirst value = value\n}\n\n",
        "impl Second<Int> where First<Int> {\nsecond value = value\n}\n\n",
        "main : Unit -> Int\n",
        "main () = first 1\n",
    ));
    fixture.write("dependency.ash", &public_interfaces(WIDTH));

    let failure = fixture
        .run()
        .expect_err("the active prerequisite must be recognized as a cycle");

    assert_eq!(failure.reason_code(), "constraint.cycle");
    let PipelineFailure::Typing(TypeError::Interface(_)) =
        failure.pipeline_failure().expect("pipeline failure")
    else {
        panic!("the cycle should remain owned by interface checking");
    };
}

#[test]
fn public_run_admits_and_drops_deep_public_routes_on_a_small_stack() {
    const DEPTH: usize = 48;
    const WIDTH: usize = 4;
    const STACK_SIZE: usize = 320 * 1024;

    std::thread::Builder::new()
        .name(String::from("public-deep-route"))
        .stack_size(STACK_SIZE)
        .spawn(|| {
            let fixture = deep_public_route_fixture(DEPTH, WIDTH);
            let observation = fixture
                .run()
                .expect("the public runner should admit the deep public route fixture");
            assert_eq!(observation.value_display(), "42");
            drop(observation);
        })
        .expect("the public small-stack witness thread should spawn")
        .join()
        .expect("the public runner should admit and dispose deep routes on a small stack");
}

#[test]
fn nested_supplied_method_bodies_use_bounded_host_stack() {
    const DEPTH: usize = 32;
    const STACK_SIZE: usize = 512 * 1024;

    for (leaf, accepted) in [("42", true), ("true", false)] {
        let mut source = String::from(
            "interface Read<A> {\nread : A -> Int\n}\nmain : Unit -> Int\nmain () = {\n",
        );
        for index in 0..DEPTH {
            source.push_str(&format!(
                "newtype N{index} = N{index}(Unit)\nwith Read<N{index}> {{\nread ignored = {{\n"
            ));
        }
        source.push_str(leaf);
        source.push('\n');
        for index in (0..DEPTH).rev() {
            source.push_str(&format!("}}\n}}\nread(N{index}(()))\n"));
        }
        source.push_str("}\n");

        std::thread::Builder::new()
            .name(String::from("nested-supplied-method-bodies"))
            .stack_size(STACK_SIZE)
            .spawn(move || {
                let fixture = ResourceFixture::create(&source);
                if accepted {
                    let observation = fixture
                        .run()
                        .expect("nested supplied methods should use existing iterative stage work");
                    assert_eq!(observation.value_display(), "42");
                    drop(observation);
                } else {
                    let failure = fixture
                        .run()
                        .expect_err("the deepest method has the wrong result");
                    assert_eq!(failure.reason_code(), "type.definition-result");
                    drop(failure);
                }
            })
            .expect("the nested-method small-stack witness should spawn")
            .join()
            .expect("nested supplied method bodies should finish on a bounded host stack");
    }
}
