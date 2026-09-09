use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, run_path},
    eval::RuntimeFailure,
    message::{Catalogue, Locale},
    module::ModuleRoots,
    presentation::{compile_file_diagnostics, write_human, write_json, write_short},
};

#[test]
fn file_dispatch_reuses_retained_pipeline_sources_and_reason_codes() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for fixture in [
        "tests/fixtures/first-stratum/type/binding-initializer.ash",
        "tests/fixtures/first-stratum/type/t002-operator-operand.ash",
        "tests/fixtures/first-stratum/parse/p003-independent-recovery.ash",
        "tests/fixtures/first-stratum/parse/excluded-bom.ash",
    ] {
        let failure = run_path(RunConfiguration {
            entry: root.join(fixture),
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        let views = compile_file_diagnostics(&failure).unwrap();
        assert!(!views.is_empty());
        let mut json = Vec::new();
        write_json(&mut json, &views[0]).unwrap();
        let value: serde_json::Value = serde_json::from_slice(&json).unwrap();
        assert_eq!(value["reason"], failure.reason_code());
        assert!(!value["labels"].as_array().unwrap().is_empty());
        for locale in [Locale::English, Locale::Bulgarian] {
            let catalogue = Catalogue::new(locale).unwrap();
            let mut text = Vec::new();
            for view in &views {
                write_human(&mut text, view, &catalogue).unwrap();
                write_short(&mut text, view, &catalogue).unwrap();
            }
            assert!(!text.is_empty());
        }
    }
}

#[test]
fn file_dispatch_does_not_route_runtime_failures_into_compile_time_reporting() {
    let failure = FileFailure::from(PipelineFailure::Runtime(RuntimeFailure::MissingBinding));
    assert!(compile_file_diagnostics(&failure).is_err());
    assert!(failure.sources().is_empty());
}

#[test]
fn file_input_dispatch_preserves_path_and_io_kind_without_source_labels() {
    for failure in [
        FileFailure::Read {
            path: "missing.ash".into(),
            kind: std::io::ErrorKind::NotFound,
        },
        FileFailure::InvalidUtf8 {
            path: "bytes.ash".into(),
        },
    ] {
        let views = compile_file_diagnostics(&failure).unwrap();
        let mut output = Vec::new();
        write_json(&mut output, &views[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["reason"], failure.reason_code());
        assert_eq!(json["responsibility"], "input");
        assert_eq!(json["labels"], serde_json::json!([]));
        assert!(
            json["facts"]
                .as_array()
                .unwrap()
                .iter()
                .any(|fact| fact["name"] == "path")
        );
    }
}

#[test]
fn missing_source_context_fallback_keeps_input_responsibility_and_marks_the_gap() {
    let failure = FileFailure::Source(ash::source::SourceError::TextTooLarge);
    let error = compile_file_diagnostics(&failure).err().unwrap();
    let mut output = Vec::new();
    ash::presentation::write_unadapted_file_diagnostic(&mut output, &failure, error).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["reason"], failure.reason_code());
    assert_eq!(json["responsibility"], "input");
    assert_eq!(
        json["developer_details"]["presentation_error"],
        "missing-source"
    );
    assert!(
        json["developer_details"]["retained_diagnostic"]
            .as_str()
            .unwrap()
            .contains("source")
    );
    let failure = FileFailure::from(PipelineFailure::Runtime(RuntimeFailure::HeapCapacity));
    output.clear();
    assert!(
        ash::presentation::write_unadapted_file_diagnostic(&mut output, &failure, error).is_err()
    );
    assert!(output.is_empty());
}
