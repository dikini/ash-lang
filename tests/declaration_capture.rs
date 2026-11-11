use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::{LoadGraphError, ModuleRoots},
    parser::{ExpectedForm, FoundToken, ParseReason},
};

#[test]
fn imported_empty_template_captures_a_complete_declaration() {
    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/surface-macros/declaration-capture/main.ash");
    let program = compile_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("the imported empty template accepts one complete source declaration");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn captured_declaration_is_forwarded_to_the_module_consumer() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("forms.ash"),
        "pub syntax declaration: (pass) $item:declaration => { $item }\n",
    )
    .unwrap();
    fs::write(
        fixture.0.join("main.ash"),
        "import forms (syntax pass)\n\nbefore : Unit -> Int\nbefore () = 0\npass {\n    passed : Unit -> Int\n    passed () = 42\n}\nafter : Unit -> Int\nafter () = 0\nmain : Unit -> Int\nmain () = before(()) + passed(()) + after(())\n",
    )
    .unwrap();
    let program = compile_path(RunConfiguration {
        entry: fixture.0.join("main.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect("the captured declaration is collected between its neighbors");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn declaration_capture_cannot_enter_other_syntax_positions_or_fuse_with_neighbors() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("entry.ash"),
        "import forms (syntax bad)\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    for (position, body) in [
        (
            "expression",
            "bad_value : Unit -> Int\nbad_value () = $item\n",
        ),
        ("type", "bad_value : $item -> Int\nbad_value _ = 42\n"),
        ("pattern", "bad_value : Unit -> Int\nbad_value $item = 42\n"),
        (
            "local block",
            "bad_value : Unit -> Int\nbad_value () = {\n$item\n42\n}\n",
        ),
        (
            "before a neighbor",
            "$item next : Unit -> Int\nnext () = 42\n",
        ),
        (
            "after a neighbor",
            "bad_value : Unit -> Int\nbad_value () = 42 $item\n",
        ),
    ] {
        fs::write(
            fixture.0.join("forms.ash"),
            format!("pub syntax declaration: (bad) $item:declaration => {{\n{body}}}\n"),
        )
        .unwrap();
        let failure = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .expect_err(position);
        assert!(
            failure.reason_code().starts_with("parse."),
            "{position}: {failure:?}"
        );
    }
}

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-d5-capture-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn compile(
        &self,
        forms: &str,
        invocation: &str,
    ) -> Result<ash::driver::CompiledProgram, ash::driver::FileFailure> {
        fs::write(self.0.join("forms.ash"), forms).unwrap();
        fs::write(
            self.0.join("main.ash"),
            format!(
                "import forms (syntax sink)\n\n{invocation}\n\nmain : Unit -> Int\nmain () = 42\n"
            ),
        )
        .unwrap();
        compile_path(RunConfiguration {
            entry: self.0.join("main.ash"),
            roots: ModuleRoots::empty(),
        })
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn source_sink_accepts_each_ordinary_declaration_category() {
    let fixture = Fixture::new();
    let forms = include_str!("fixtures/surface-macros/declaration-capture/forms.ash");
    for declaration in [
        "type Color = Red(Int)",
        "newtype Box = Box(Int)",
        "interface Marker<A> {\n    mark : A -> Bool\n}",
        "impl Marker<Int> {\n    mark _ = true\n}",
        "effect Ask {\n    ask : Unit -> Int\n}",
        "foreign library Fixture {\n    profile \"x86_64-unknown-linux-gnu\"\n    symbol Make : Unit -> F.Address { name \"fixture_make\" }\n}",
        "passed : Unit -> Int\npassed () = 42",
        "fn same(value: Int) -> Int {\n    value\n}",
    ] {
        let program = fixture
            .compile(forms, &format!("sink {{\n{declaration}\n}}"))
            .unwrap_or_else(|error| panic!("{declaration}: {error:?}"));
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }
}

#[test]
fn source_capture_rejects_incomplete_multiple_or_excluded_declarations() {
    let fixture = Fixture::new();
    let forms = include_str!("fixtures/surface-macros/declaration-capture/forms.ash");
    for (declaration, offset, expected, found) in [
        ("", 1, ExpectedForm::Identifier, FoundToken::Spelling("}")),
        (
            "passed : Unit -> Int",
            "passed : Unit -> Int".len() + 1,
            ExpectedForm::Identifier,
            FoundToken::Spelling("}"),
        ),
        (
            "passed () = 42",
            0,
            ExpectedForm::Identifier,
            FoundToken::Identifier,
        ),
        (
            "type One = One\ntype Two = Two",
            "type One = One\n".len(),
            ExpectedForm::RightBrace,
            FoundToken::Spelling("type"),
        ),
        (
            "type One = One trailing",
            "type One = One ".len(),
            ExpectedForm::RightBrace,
            FoundToken::Identifier,
        ),
        (
            "type Broken =",
            "type Broken =".len() + 1,
            ExpectedForm::Identifier,
            FoundToken::Spelling("}"),
        ),
        (
            "import other (name)",
            0,
            ExpectedForm::Identifier,
            FoundToken::Spelling("import"),
        ),
        (
            "pub syntax declaration: (other) => {}",
            0,
            ExpectedForm::Identifier,
            FoundToken::Spelling("pub"),
        ),
        (
            "sink { type Nested = Nested }",
            0,
            ExpectedForm::Identifier,
            FoundToken::Identifier,
        ),
        (
            "resource Forbidden {}",
            0,
            ExpectedForm::Identifier,
            FoundToken::Spelling("resource"),
        ),
    ] {
        let failure = match fixture.compile(forms, &format!("sink {{\n{declaration}\n}}")) {
            Ok(_) => panic!("accepted {declaration:?}"),
            Err(failure) => failure,
        };
        let ash::driver::FileFailure::Graph(graph) = failure else {
            panic!("{declaration:?}: expected caller parsing failure, got {failure:?}");
        };
        let LoadGraphError::Syntax(failure) = graph.failure() else {
            panic!(
                "{declaration:?}: expected syntax failure, got {:?}",
                graph.failure()
            );
        };
        assert!(failure.source.display_path().ends_with("main.ash"));
        assert!(failure.lexical.is_empty() && failure.resource.is_none());
        let start = "import forms (syntax sink)\n\nsink {\n".len() + offset;
        assert!(
            failure.parser.iter().any(|diagnostic| {
                diagnostic.reason == ParseReason::ExpectedForm
                    && diagnostic.expected_form() == Some(expected)
                    && diagnostic.found_token() == Some(found)
                    && diagnostic.primary.span().range().start() as usize == start
            }),
            "{declaration:?}: {:?}",
            failure.parser
        );
    }
}

#[test]
fn removing_one_equation_can_leave_a_complete_declaration() {
    let fixture = Fixture::new();
    let forms = include_str!("fixtures/surface-macros/declaration-capture/forms.ash");
    let declaration = "passed : Bool -> Int\npassed true = 42\npassed false = 0";
    for source in [
        declaration.to_owned(),
        declaration.replace("\npassed false = 0", ""),
    ] {
        let program = fixture
            .compile(forms, &format!("sink {{\n{source}\n}}"))
            .expect("a remaining equation is syntactically complete");
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }
}

#[test]
fn unused_nonempty_declaration_capture_definition_is_admitted() {
    let fixture = Fixture::new();
    let forms = "pub syntax declaration: (sink) $item:declaration => { type Item = Item }\n";
    let program = fixture
        .compile(forms, "")
        .expect("a valid unused template is admitted");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn unused_template_reports_the_unknown_splice_in_human_and_json() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_file_diagnostics, write_human, write_json},
    };

    let fixture = Fixture::new();
    let forms = "pub syntax declaration: (bad) $name:ident => {\n    pub $missing : Unit -> Int\n    $missing () = 42\n}\n";
    fs::write(fixture.0.join("forms.ash"), forms).unwrap();
    fs::write(
        fixture.0.join("main.ash"),
        "import forms (syntax bad)\n\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    let failure = compile_path(RunConfiguration {
        entry: fixture.0.join("main.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect_err("the unused definition contains an unknown splice");
    assert_eq!(failure.reason_code(), "parse.unknown-template-capture");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut human = Vec::new();
    write_human(
        &mut human,
        &diagnostics[0],
        &Catalogue::new(Locale::English).unwrap(),
    )
    .unwrap();
    let human = String::from_utf8(human).unwrap();
    assert!(
        human.contains("$missing") && human.contains("forms.ash"),
        "{human}"
    );
    let mut output = Vec::new();
    write_json(&mut output, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["responsibility"], "source", "{json}");
    assert!(
        json["facts"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fact| { fact["name"] == "capture" && fact["value"] == "$missing" }),
        "{json}"
    );
    let primary = &json["labels"][0];
    assert_eq!(
        primary["relationship"], "unknown_template_capture",
        "{json}"
    );
    assert!(
        primary["path"].as_str().unwrap().ends_with("forms.ash"),
        "{json}"
    );
    let start = primary["byte_start"].as_u64().unwrap() as usize;
    let end = primary["byte_end"].as_u64().unwrap() as usize;
    assert_eq!(&forms[start..end], "missing", "{json}");
}

#[test]
fn unknown_splice_inside_template_repetition_keeps_its_cause() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("forms.ash"),
        "pub syntax declaration: (bad) $( $name:ident ),+ => {\n    $(\n        pub $missing : Unit -> Int\n        $missing () = 42\n    )+\n}\n",
    )
    .unwrap();
    fs::write(
        fixture.0.join("main.ash"),
        "import forms (syntax bad)\n\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    let failure = compile_path(RunConfiguration {
        entry: fixture.0.join("main.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect_err("the repetition contains an unknown splice");
    assert_eq!(failure.reason_code(), "parse.unknown-template-capture");
}

#[test]
fn expression_template_and_fixed_outer_quote_report_unknown_splices() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("forms.ash"),
        "pub syntax bad $value:expr => { $missing }\n",
    )
    .unwrap();
    fs::write(
        fixture.0.join("main.ash"),
        "import forms (syntax bad)\n\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    let failure = compile_path(RunConfiguration {
        entry: fixture.0.join("main.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect_err("the unused expression template contains an unknown splice");
    assert_eq!(failure.reason_code(), "parse.unknown-template-capture");

    let failure = compile_path(RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/escapes/unbound_outer.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect_err("the fixed outer quote contains an unknown outer splice");
    assert_eq!(failure.reason_code(), "parse.unknown-template-capture");
}

#[test]
fn imported_literal_globals_preserve_expansion_origin() {
    let fixture = Fixture::new();
    for body in [
        "main : Unit -> Int\n    main () = 42",
        "fn main(unit: Unit) -> Int {\n        42\n    }",
    ] {
        fs::write(
            fixture.0.join("forms.ash"),
            format!("pub syntax declaration: (sink) $item:declaration => {{\n    {body}\n}}\n"),
        )
        .unwrap();
        fs::write(
            fixture.0.join("main.ash"),
            "import forms (syntax sink)\nsink {\ndiscarded : Unit -> Int\ndiscarded () = true\n}\n",
        )
        .unwrap();
        let program = compile_path(RunConfiguration {
            entry: fixture.0.join("main.ash"),
            roots: ModuleRoots::empty(),
        })
        .expect("the introduced global reaches independent Core validation");
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }
}

#[test]
fn literal_template_output_is_checked_while_discarded_input_is_not() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("main.ash"),
        "import forms (syntax sink)\nsink {\ndiscarded : Unit -> Int\ndiscarded () = unknown(())\n}\n",
    )
    .unwrap();
    let forms = |expression: &str| {
        format!(
            "pub syntax declaration: (sink) $item:declaration => {{\n    main : Unit -> Int\n    main () = {expression}\n}}\n"
        )
    };
    fs::write(fixture.0.join("forms.ash"), forms("43")).unwrap();
    let configuration = || RunConfiguration {
        entry: fixture.0.join("main.ash"),
        roots: ModuleRoots::empty(),
    };
    let program = compile_path(configuration()).expect("discarded input is not resolved");
    assert_eq!(execute(&program).unwrap().value_display(), "43");
    fs::write(fixture.0.join("forms.ash"), forms("true")).unwrap();
    let failure = compile_path(configuration()).expect_err("generated output is checked");
    assert!(failure.reason_code().starts_with("type."), "{failure:?}");
}
