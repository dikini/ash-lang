//! DN-0036 evidence for complete source owner arguments and imported closure.
use ash::{
    driver::{PipelineFailure, RunConfiguration, run_path},
    foreign::{ForeignRegistrations, provider_manifest, sqlite_manifest},
    module::{ForeignRegistrationId, LoadGraphError, ModuleRoots},
    parser::{ResourceFailure, STRUCTURAL_DEPTH_LIMIT},
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/provider-experiments/owner-rows")
        .join(name)
}

fn roots() -> ModuleRoots {
    ModuleRoots::empty().with_foreign_registrations(
        ForeignRegistrations::new([
            provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
            sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap(),
    )
}

struct FixtureCopy(PathBuf);
impl FixtureCopy {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-owner-rows-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&path).unwrap();
        for name in ["provider.ash", "library.ash", "entry.ash"] {
            fs::copy(fixture(name), path.join(name)).unwrap();
        }
        Self(path)
    }
    fn replace(&self, name: &str, before: &str, after: &str) {
        let path = self.0.join(name);
        let source = fs::read_to_string(&path).unwrap();
        assert!(
            source.contains(before),
            "fixture mutation must reach its source site"
        );
        fs::write(path, source.replacen(before, after, 1)).unwrap();
    }
    fn run(&self) -> Result<ash::driver::Observation, ash::driver::FileFailure> {
        run_path(RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: roots(),
        })
    }
}
impl Drop for FixtureCopy {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn mixed_owner_declarations_and_imported_callbacks_check_through_public_driver() {
    let observation = run_path(RunConfiguration {
        entry: fixture("entry.ash"),
        roots: roots(),
    })
    .expect("complete mixed owner arguments and inherited callback rows should check and publish");
    assert_eq!(observation.value_display(), "()");
    assert_eq!(observation.type_display(), "Unit");
}

#[test]
fn targeted_reexport_retains_nested_row_effect_owner_metadata() {
    let observation = run_path(RunConfiguration {
        entry: fixture("nested-entry.ash"),
        roots: roots(),
    })
    .expect("a targeted imported constraint must retain Outer and nested Inner signatures");
    assert_eq!(observation.value_display(), "()");
}

#[test]
fn source_owner_arguments_reject_wrong_tags_kinds_and_saturation() {
    for (name, before, after) in [
        (
            "interface row tag",
            "provider ConnectionProvider<R, {| Rows}>",
            "provider ConnectionProvider<R, Rows>",
        ),
        (
            "resource Type tag",
            "Connection<R, {| Rows}>",
            "Connection<{}, {| Rows}>",
        ),
        (
            "resource saturation",
            "Connection<R, {| Rows}>",
            "Connection<R>",
        ),
        (
            "effect saturation",
            "effect ConnectionOps<R, {| Rows}>",
            "effect ConnectionOps<R>",
        ),
        (
            "interface saturation",
            "provider ConnectionProvider<R, {| Rows}>",
            "provider ConnectionProvider<R>",
        ),
        ("row tail kind", "Rows : EffectRow", "Rows : Type"),
    ] {
        let tree = FixtureCopy::new();
        tree.replace("library.ash", before, after);
        let failure = tree.run().expect_err(name);
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(
                    PipelineFailure::Resolution(_)
                        | PipelineFailure::Kind(_)
                        | PipelineFailure::Typing(_)
                )
            ),
            "{name} must reach owner checking after parsing: {failure:?}"
        );
        assert!(
            failure.is_source_rejection(),
            "{name} must reject source: {failure:?}"
        );
    }
}

#[test]
fn row_arguments_have_no_standalone_or_ordinary_nominal_type_denotation() {
    for (declaration, standalone_row) in [
        ("pub invalid : {| Rows} -> Unit\ninvalid value = ()\n", true),
        ("pub type Invalid<A : EffectRow> = Invalid(A)\n", false),
        (
            "pub type Box<A> = Box(A)\npub invalid : Box<{}> -> Unit\ninvalid value = ()\n",
            false,
        ),
    ] {
        let tree = FixtureCopy::new();
        tree.replace(
            "entry.ash",
            "main : Unit -> Unit",
            &format!("{declaration}\nmain : Unit -> Unit"),
        );
        let failure = tree
            .run()
            .expect_err("ordinary monotypes cannot absorb row arguments or row-kind arrows");
        if standalone_row {
            assert!(
                matches!(failure.graph_failure(), Some(LoadGraphError::Syntax(_))),
                "a standalone row is outside atomic type syntax: {failure:?}"
            );
        } else {
            assert!(
                matches!(
                    failure.pipeline_failure(),
                    Some(
                        PipelineFailure::Resolution(_)
                            | PipelineFailure::Kind(_)
                            | PipelineFailure::Typing(_)
                    )
                ),
                "ordinary owner rows parse before kind rejection: {failure:?}"
            );
        }
        assert!(failure.is_source_rejection(), "{failure:?}");
    }
}

#[test]
fn nested_owner_rows_obey_the_existing_depth_limit_on_a_small_stack() {
    std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
        for depth in [STRUCTURAL_DEPTH_LIMIT + 1, 1_024] {
            let tree = FixtureCopy::new();
            let row = format!("{}{{Library.Inner}}{}", "{Library.Outer<".repeat(depth - 1), ">}".repeat(depth - 1));
            tree.replace("entry.ash", "main : Unit -> Unit", &format!("pub deep : Unit -> Unit where Library.Witness<{row}>\ndeep () = ()\n\nmain : Unit -> Unit"));
            let failure = tree.run().expect_err("complete owner rows must consume the existing structural depth budget");
            let Some(LoadGraphError::Syntax(syntax)) = failure.graph_failure() else {
                panic!("the parser must reject the depth before recursive source checking: {failure:?}");
            };
            assert_eq!(syntax.resource, Some(ResourceFailure::StructuralDepth { limit: STRUCTURAL_DEPTH_LIMIT }));
            assert!(syntax.lexical.is_empty());
            assert!(syntax.parser.is_empty());
            assert!(!failure.is_source_rejection(), "a replaceable implementation depth limit is not a language rejection");
        }
    }).unwrap().join().unwrap();
}
