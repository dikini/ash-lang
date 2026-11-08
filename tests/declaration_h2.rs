use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{PipelineFailure, RunConfiguration, compile_path, execute},
    module::ModuleRoots,
    resolve::ResolveReason,
};

fn fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/hygiene")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

#[test]
fn i12_distinct_caller_selected_helpers_reach_the_ordinary_driver() {
    for name in ["early_terms.ash", "control_early_terms.ash"] {
        let program = compile_path(fixture(name)).expect("the fixed I12 case compiles");
        assert_eq!(execute(&program).unwrap().value_display(), "84");
    }
}

#[test]
fn i12_duplicate_helpers_reach_ordinary_resolution_with_both_sources() {
    for (name, expected) in [
        (
            "early_terms_duplicate.ash",
            [(106, 118), (69, 81), (46, 81)],
        ),
        (
            "early_terms_handwritten_duplicate.ash",
            [(114, 120), (106, 112), (82, 112)],
        ),
    ] {
        let failure = compile_path(fixture(name)).expect_err("the duplicate helper must reject");
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("expected ordinary resolution failure: {failure:?}");
        };
        assert_eq!(error.reason, ResolveReason::DuplicateGlobal);
        let source = failure
            .sources()
            .iter()
            .find(|source| Path::new(source.display_path()).ends_with(name))
            .expect("the caller source is retained");
        let [first, definition] = error.related.as_slice() else {
            panic!("expected the earlier name and definition");
        };
        for (label, (start, end)) in [&error.primary, first, definition]
            .into_iter()
            .zip(expected)
        {
            let span = label.span();
            assert_eq!(span.source(), source.id());
            assert_eq!((span.range().start(), span.range().end()), (start, end));
        }
    }
}

#[test]
fn caller_selected_references_and_introduced_parameters_remain_distinct() {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "ash-h2-terms-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    struct Fixture(PathBuf);
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let fixture = Fixture(path);
    for (name, text) in [
        (
            "forms.ash",
            "pub syntax declaration: (make_value) $name:ident using $helper:ident from $value:ident => {\n    $helper : Int -> Int\n    $helper parameter = $value(()) + parameter\n    pub $name : Unit -> Int\n    $name () = $helper(1)\n}\n",
        ),
        (
            "entry.ash",
            "import forms (syntax make_value)\nmake_value first using helper_first from left\nmake_value second using helper_second from right\nleft : Unit -> Int\nleft () = 10\nright : Unit -> Int\nright () = 20\nparameter : Unit -> Int\nparameter () = 999\nmain : Unit -> Int\nmain () = first(()) * 100 + second(())\n",
        ),
    ] {
        fs::write(fixture.0.join(name), text).unwrap();
    }
    let program = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect("the caller-selected references and introduced parameters resolve");
    assert_eq!(execute(&program).unwrap().value_display(), "1121");
}
