use ash::{
    driver::{PipelineFailure, RunConfiguration, run_path},
    elaborate::{TypeError, check_module},
    message::{Catalogue, Locale},
    module::{ModuleRoots, load_module_graph},
    presentation::{compile_type_diagnostic, write_human, write_short},
    resolve::resolve_module,
};

#[test]
fn human_excerpt_expands_tabs_and_aligns_unicode_without_changing_json_offsets() {
    use ash::{
        diagnostic::{Diagnostic, SourceLabel},
        elaborate::TypeReason,
        source::{ByteRange, SourceFile},
    };
    for (text, start, expected_excerpt, expected_indent) in [
        ("\tЖ界e\u{301} x", 10, "    Ж界e\u{301} x", 9),
        ("界\tx", 4, "界  x", 4),
        ("e\u{301} x", 4, "e\u{301} x", 2),
    ] {
        let source = SourceFile::new("layout.ash", text).unwrap();
        let span = source
            .span(ByteRange::new(start, start + 1).unwrap())
            .unwrap();
        let mut diagnostic = Diagnostic::new(
            TypeReason::BindingInitializer,
            SourceLabel::new(span, "ignored"),
        );
        diagnostic
            .related
            .push(SourceLabel::new(span, "annotation"));
        diagnostic.expected = Some("Bool".into());
        diagnostic.found = Some("Int".into());
        let diagnostic = diagnostic.into();
        let view = compile_type_diagnostic(&diagnostic, &[&source]).unwrap();
        let mut output = Vec::new();
        write_human(
            &mut output,
            &view,
            &Catalogue::new(Locale::English).unwrap(),
        )
        .unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(
            output.contains(&format!(
                "1 | {expected_excerpt}\n  | {}^",
                " ".repeat(expected_indent)
            )),
            "{output}"
        );
        let mut json = Vec::new();
        ash::presentation::write_json(&mut json, &view).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
        assert_eq!(json["labels"][0]["byte_start"], start);
        assert_eq!(json["labels"][0]["byte_end"], start + 1);
    }
}

#[test]
fn human_excerpt_handles_multiline_ranges_and_empty_end_of_file() {
    use ash::{
        diagnostic::{Diagnostic, SourceLabel},
        elaborate::TypeReason,
        source::{ByteRange, SourceFile},
    };
    for (text, start, end, included, excluded) in [
        ("first\r\nsecond\nthird", 0, 14, "2 | second", "3 | third"),
        ("first\n", 6, 6, "2 | \n  | ^", "1 | first"),
        ("", 0, 0, "1 | \n  | ^", "2 |"),
        ("\n\n\n\n\n\n\n\n\nx", 9, 10, "10 | x\n   | ^", "9 |"),
    ] {
        let source = SourceFile::new("range.ash", text).unwrap();
        let span = source.span(ByteRange::new(start, end).unwrap()).unwrap();
        let mut diagnostic = Diagnostic::new(
            TypeReason::BindingInitializer,
            SourceLabel::new(span, "ignored"),
        );
        diagnostic
            .related
            .push(SourceLabel::new(span, "annotation"));
        diagnostic.expected = Some("Bool".into());
        diagnostic.found = Some("Int".into());
        let diagnostic = diagnostic.into();
        let view = compile_type_diagnostic(&diagnostic, &[&source]).unwrap();
        let mut output = Vec::new();
        write_human(
            &mut output,
            &view,
            &Catalogue::new(Locale::English).unwrap(),
        )
        .unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains(included), "{output}");
        assert!(!output.contains(excluded), "{output}");
        assert!(!output.contains('\r'));
    }
}

#[test]
fn driver_failure_owns_the_sources_needed_for_later_rendering() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/first-stratum/type/binding-initializer.ash");
    let failure = run_path(RunConfiguration {
        entry: path,
        roots: ModuleRoots::empty(),
    })
    .unwrap_err();
    let PipelineFailure::Typing(TypeError::Source(error)) = failure.pipeline_failure().unwrap()
    else {
        panic!("expected the binding initializer failure");
    };
    let sources: Vec<_> = failure.sources().iter().collect();
    assert_eq!(sources.len(), 1);
    let view = compile_type_diagnostic(error, &sources).unwrap();
    let mut output = Vec::new();
    write_human(
        &mut output,
        &view,
        &Catalogue::new(Locale::English).unwrap(),
    )
    .unwrap();
    assert!(
        String::from_utf8(output)
            .unwrap()
            .contains("let value : Bool = 1")
    );
}

#[test]
fn real_binding_error_keeps_initializer_and_annotation_context() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/first-stratum/type/binding-initializer.ash");
    let graph = load_module_graph(&path, &ModuleRoots::empty()).unwrap();
    let loaded = graph
        .modules()
        .iter()
        .find(|m| m.id() == graph.entry())
        .unwrap();
    let resolved = resolve_module(loaded, &[]).unwrap();
    let TypeError::Source(error) = check_module(resolved).unwrap_err() else {
        panic!("expected a structured type diagnostic");
    };
    let view = compile_type_diagnostic(&error, &[loaded.source()]).unwrap();
    let mut human = Vec::new();
    let catalogue = Catalogue::new(Locale::English).unwrap();
    write_human(&mut human, &view, &catalogue).unwrap();
    let human = String::from_utf8(human).unwrap();
    assert!(human.starts_with(
        "This binding needs a value of type `Bool`, but its initializer has type `Int`.\n"
    ));
    let path = loaded.source().display_path();
    assert_eq!(
        human,
        format!(
            "This binding needs a value of type `Bool`, but its initializer has type `Int`.\n  --> {path}:3:24\n3 |     let value : Bool = 1\n  | {}^ This initializer has type `Int`.\n  --> {path}:3:17\n3 |     let value : Bool = 1\n  | {}^ This annotation requires type `Bool`.\nreason: type.binding-initializer\n",
            " ".repeat(23),
            " ".repeat(16),
        )
    );
    let mut short = Vec::new();
    write_short(&mut short, &view, &catalogue).unwrap();
    let short = String::from_utf8(short).unwrap();
    assert_eq!(
        short,
        format!(
            "{path}:3:24: This binding needs a value of type `Bool`, but its initializer has type `Int`. [type.binding-initializer]\n"
        )
    );

    let mut bulgarian = Vec::new();
    write_human(
        &mut bulgarian,
        &view,
        &Catalogue::new(Locale::Bulgarian).unwrap(),
    )
    .unwrap();
    assert_eq!(
        String::from_utf8(bulgarian).unwrap(),
        format!(
            "Тази променлива изисква стойност от тип `Bool`, но началният израз има тип `Int`.\n  --> {path}:3:24\n3 |     let value : Bool = 1\n  | {}^ Този начален израз има тип `Int`.\n  --> {path}:3:17\n3 |     let value : Bool = 1\n  | {}^ Тази анотация изисква тип `Bool`.\nreason: type.binding-initializer\n",
            " ".repeat(23),
            " ".repeat(16),
        )
    );
    let mut short_bg = Vec::new();
    write_short(
        &mut short_bg,
        &view,
        &Catalogue::new(Locale::Bulgarian).unwrap(),
    )
    .unwrap();
    assert_eq!(
        String::from_utf8(short_bg).unwrap(),
        format!(
            "{path}:3:24: Тази променлива изисква стойност от тип `Bool`, но началният израз има тип `Int`. [type.binding-initializer]\n"
        )
    );
}

#[test]
fn driver_retains_the_dependency_source_not_just_the_entry_file() {
    let entry = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/diagnostic-source-retention/entry.ash");
    let failure = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .unwrap_err();
    let PipelineFailure::Typing(TypeError::Source(error)) = failure.pipeline_failure().unwrap()
    else {
        panic!("expected the dependency initializer failure");
    };
    assert_eq!(failure.sources().len(), 2);
    let sources: Vec<_> = failure.sources().iter().collect();
    let view = compile_type_diagnostic(error, &sources).unwrap();
    let mut output = Vec::new();
    write_human(
        &mut output,
        &view,
        &Catalogue::new(Locale::English).unwrap(),
    )
    .unwrap();
    let output = String::from_utf8(output).unwrap();
    assert!(output.contains("dependency.ash:3:24"));
    assert!(output.contains("dependency.ash:3:17"));
    assert!(!output.contains("entry.ash"));
}
