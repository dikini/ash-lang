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
fn unlocated_source_errors_preserve_facts_without_inventing_paths() {
    use ash::message::{Catalogue, Locale};
    use ash::presentation::write_human;
    use ash::source::{ByteRange, SourceError, SourceFile};
    let first = SourceFile::new("first.ash", "").unwrap();
    let second = SourceFile::new("second.ash", "").unwrap();
    for error in [
        SourceError::SourceIdExhausted,
        SourceError::DisplayPathTooLarge,
        SourceError::TextTooLarge,
        SourceError::TooManyLines,
        SourceError::LineTooLong,
        SourceError::RangeOutsideSource {
            range: ByteRange::new(1, 4).unwrap(),
            source_len: 3,
        },
        SourceError::ForeignSpan {
            expected: first.id(),
            found: second.id(),
        },
        SourceError::OffsetOutsideSource {
            offset: u32::MAX,
            source_len: 3,
        },
        SourceError::OffsetSplitsCodePoint { offset: 1 },
        SourceError::InvalidLineState,
    ] {
        for (failure, operation) in [
            (FileFailure::Source(error), "admission"),
            (
                FileFailure::from(PipelineFailure::SourceModel(error)),
                "span-construction",
            ),
        ] {
            let views = compile_file_diagnostics(&failure).unwrap();
            assert_eq!(views.len(), 1);
            for locale in [Locale::English, Locale::Bulgarian] {
                let mut output = Vec::new();
                write_human(&mut output, &views[0], &Catalogue::new(locale).unwrap()).unwrap();
                assert!(!output.is_empty());
            }
            let mut output = Vec::new();
            write_json(&mut output, &views[0]).unwrap();
            let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(json["reason"], failure.reason_code());
            assert_eq!(json["labels"], serde_json::json!([]));
            assert!(json.get("developer_details").is_none());
            let facts = json["facts"].as_array().unwrap();
            assert!(!facts.iter().any(|fact| fact["name"] == "path"));
            assert_eq!(facts.last().unwrap()["value"], operation);
            if operation == "span-construction" {
                assert_eq!(json["responsibility"], "compiler");
            }
            if matches!(error, SourceError::OffsetOutsideSource { .. }) {
                assert!(
                    facts
                        .iter()
                        .any(|fact| fact["name"] == "offset" && fact["value"] == u32::MAX)
                );
            }
            if matches!(error, SourceError::TextTooLarge) && operation == "admission" {
                assert_eq!(json["responsibility"], "input");
            }
        }
    }
}

#[test]
fn bare_projection_failures_keep_their_cause_or_limit() {
    use ash::{
        message::{Catalogue, Locale},
        parser::{InternalReason, ProjectionError, ResourceFailure},
        presentation::write_human,
    };
    for error in [
        ProjectionError::RecoveryNodesPresent,
        ProjectionError::MalformedTree(InternalReason::UnexpectedShape),
        ProjectionError::ResourceLimit(ResourceFailure::StructuralDepth { limit: 42 }),
        ProjectionError::ResourceLimit(ResourceFailure::SyntaxWork { limit: 43 }),
    ] {
        let failure = FileFailure::from(PipelineFailure::Projection(error));
        let views = compile_file_diagnostics(&failure).unwrap();
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_human(&mut output, &views[0], &Catalogue::new(locale).unwrap()).unwrap();
            assert!(!output.is_empty());
        }
        let mut output = Vec::new();
        write_json(&mut output, &views[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["reason"], failure.reason_code());
        assert_eq!(json["responsibility"], "compiler");
        assert_eq!(json["labels"], serde_json::json!([]));
        assert!(json.get("developer_details").is_none());
        let facts = json["facts"].as_array().unwrap();
        assert_eq!(facts.len(), 1);
        match error {
            ProjectionError::RecoveryNodesPresent => {
                assert_eq!(facts[0]["value"], "recovery-nodes")
            }
            ProjectionError::MalformedTree(_) => assert_eq!(facts[0]["value"], "unexpected-shape"),
            ProjectionError::ResourceLimit(
                ResourceFailure::StructuralDepth { limit } | ResourceFailure::SyntaxWork { limit },
            ) => assert_eq!(facts[0]["value"], limit),
        }
    }
}

#[test]
fn missing_source_context_fallback_marks_the_gap_and_excludes_runtime() {
    let source = ash::source::SourceFile::new("unretained.ash", "\r").unwrap();
    let span = source
        .span(ash::source::ByteRange::new(0, 1).unwrap())
        .unwrap();
    let failure = FileFailure::from(PipelineFailure::Syntax(Box::new(
        ash::driver::SyntaxFailure {
            lexical: vec![ash::diagnostic::Diagnostic::new(
                ash::lexer::LexReason::BareCarriageReturn,
                ash::diagnostic::SourceLabel::new(span, "bare carriage return"),
            )],
            parser: Vec::new(),
            resource: None,
        },
    )));
    let error = compile_file_diagnostics(&failure).err().unwrap();
    let mut output = Vec::new();
    ash::presentation::write_unadapted_file_diagnostic(&mut output, &failure, error).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["reason"], failure.reason_code());
    assert_eq!(
        json["developer_details"]["presentation_error"],
        "missing-source"
    );
    assert!(
        json["developer_details"]["retained_diagnostic"]
            .as_str()
            .unwrap()
            .contains("lex.bare-carriage-return")
    );
    let failure = FileFailure::from(PipelineFailure::Runtime(RuntimeFailure::HeapCapacity));
    output.clear();
    assert!(
        ash::presentation::write_unadapted_file_diagnostic(&mut output, &failure, error).is_err()
    );
    assert!(output.is_empty());
}
