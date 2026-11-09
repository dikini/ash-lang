use std::path::PathBuf;

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
fn i13_definition_private_and_renamed_facade_references_reach_the_driver() {
    for name in ["early_owner.ash", "control_early_owner.ash"] {
        let program = compile_path(fixture(name)).expect(name);
        let result = execute(&program).expect(name);
        assert_eq!(result.value_display(), "42", "{name}");
        assert_eq!(result.type_display(), "Int", "{name}");
    }
}

#[test]
fn i13_direct_import_of_the_owner_private_helper_is_refused() {
    let failure = compile_path(fixture("early_owner_private.ash"))
        .expect_err("the caller cannot import the owner's private helper");
    assert!(failure.is_source_rejection());
    let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
        panic!("expected ordinary resolution failure: {failure:?}");
    };
    assert_eq!(error.reason, ResolveReason::UnavailableExport);
    assert_eq!(error.found.as_deref(), Some("private_calculation"));
    assert_eq!(
        error.primary.message(),
        "this declaration is private to its defining module"
    );
    let primary = error.primary.span();
    let caller = failure
        .sources()
        .iter()
        .find(|source| source.id() == primary.source())
        .expect("the importing source is retained");
    assert!(caller.display_path().ends_with("early_owner_private.ash"));
    let range = primary.range();
    assert_eq!(
        &caller.text()[range.start() as usize..range.end() as usize],
        "private_calculation"
    );

    let [declaration] = error.related.as_slice() else {
        panic!("expected the private declaration location");
    };
    let span = declaration.span();
    let owner = failure
        .sources()
        .iter()
        .find(|source| source.id() == span.source())
        .expect("the owner's source is retained");
    assert!(owner.display_path().ends_with("early_owner_forms.ash"));
    let range = span.range();
    assert!(
        owner.text()[range.start() as usize..range.end() as usize].contains("private_calculation")
    );
}
