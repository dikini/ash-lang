//! Public cross-stage resource evidence for explicit kinds.
//!
//! Exact private formulas remain beside their owning operations: `types`
//! owns Kind and Type construction/clone/equality/hash/render/substitution
//! and structural disposal;
//! `kind` owns resolved kind checking; `elaborate` owns occurs checking and
//! unification; `interface` owns implementation matching and overlap;
//! `evidence` owns selection; and `resolve`, `resolved`, and
//! `evidence_validation` own their respective resolution, summary/import, and
//! linked-admission boundaries. The Core dialect owns construction and
//! disposal, `core::transform` owns rebuilds, and `core::validate` owns
//! independent validation. This integration target anchors the source-vector
//! path that crosses those private owners.

use std::{
    fmt::Write as _,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, run_path},
    kind::{KindFailure, KindReason},
    module::ModuleRoots,
    types::{Kind, Type},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct WideKindFixture(PathBuf);

impl WideKindFixture {
    fn create(entry: &str, dependency: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory =
                std::env::temp_dir().join(format!("ash-kind-resource-{}-{id}", std::process::id()));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let entry_path = directory.join("entry.ash");
                    fs::write(&entry_path, entry).expect("the entry fixture should be writable");
                    fs::write(directory.join("dependency.ash"), dependency)
                        .expect("the dependency fixture should be writable");
                    return Self(entry_path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("the resource fixture should be creatable: {error}"),
            }
        }
    }

    fn run(&self) -> Result<ash::driver::Observation, FileFailure> {
        run_path(RunConfiguration {
            entry: self.0.clone(),
            roots: ModuleRoots::empty(),
        })
    }
}

impl Drop for WideKindFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn comma_separated(count: usize, mut item: impl FnMut(usize) -> String) -> String {
    let mut output = String::new();
    for index in 0..count {
        if index > 0 {
            output.push_str(", ");
        }
        output.push_str(&item(index));
    }
    output
}

fn wide_dependency(width: usize) -> String {
    assert!(width >= 2);
    let parameters = comma_separated(width, |index| {
        if index + 1 == width {
            "F : Type -> Type".to_owned()
        } else {
            format!("P{index}")
        }
    });
    let arguments = comma_separated(width, |index| {
        if index + 1 == width {
            "Option".to_owned()
        } else {
            "Int".to_owned()
        }
    });
    let mut source = String::new();
    writeln!(source, "pub type Option<A> =\nNone\n| Some(A)")
        .expect("writing to a String should succeed");
    writeln!(source, "pub type Wide<{parameters}> =\nWide")
        .expect("writing to a String should succeed");
    writeln!(source, "pub make : Unit -> Wide<{arguments}>")
        .expect("writing to a String should succeed");
    source.push_str("make () = Wide\n");
    source
}

fn wide_entry(width: usize, final_argument: &str) -> String {
    let arguments = comma_separated(width, |index| {
        if index + 1 == width {
            final_argument.to_owned()
        } else {
            "Int".to_owned()
        }
    });
    format!(
        "import dependency as Dependency\n\nmain : Unit -> Unit\nmain () = {{\nlet value : Dependency.Wide<{arguments}> = Dependency.make(())\n()\n}}\n"
    )
}

#[test]
fn wide_source_argument_vector_crosses_body_free_link_and_core_on_a_small_stack() {
    // Source projection retains one W-wide argument vector. Resolution folds
    // it into W unary `Application` nodes; later summary, import, link, Core,
    // validation, evaluation, and disposal consume the canonical spine.
    // Repeated scheme instantiation makes this complete product fixture
    // deliberately more expensive than the isolated linear witnesses. Keep
    // headroom below the production limit instead of making it a brittle
    // capacity boundary.
    const WIDTH: usize = 256;

    std::thread::Builder::new()
        .name("public-wide-kind-route".to_owned())
        .stack_size(320 * 1024)
        .spawn(|| {
            let dependency = wide_dependency(WIDTH);

            let accepted =
                WideKindFixture::create(&wide_entry(WIDTH, "Dependency.Option"), &dependency);
            let observation = accepted
                .run()
                .expect("the wide canonical application should cross the complete public path");
            assert_eq!(observation.value_display(), "()");
            assert_eq!(observation.ty(), &Type::Unit);
            drop(observation);

            let rejected = WideKindFixture::create(&wide_entry(WIDTH, "Int"), &dependency);
            let failure = rejected
                .run()
                .expect_err("the final source argument has kind Type, not Type -> Type");
            let PipelineFailure::Kind(KindFailure::Source(error)) =
                failure.pipeline_failure().expect("pipeline failure")
            else {
                panic!("the rejected source vector should retain kind ownership");
            };
            assert_eq!(error.reason, KindReason::Argument);
            assert_eq!(
                error.expected_kind(),
                Some(&Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)))
            );
            assert_eq!(error.found_kind(), Some(&Kind::Type));
            assert_eq!(
                error.primary.message(),
                "this type argument has the wrong kind"
            );
            assert_eq!(error.related.len(), 1);
            assert_ne!(
                error.primary.span().source(),
                error.related[0].span().source(),
                "the rejected argument must retain its imported declaration relation",
            );
            assert_eq!(
                error.related[0].message(),
                "the applied type's parameter kind is declared here"
            );
        })
        .expect("the public wide-route thread should start")
        .join()
        .expect("accepted and rejected wide routes should tear down on 320 KiB");
}
