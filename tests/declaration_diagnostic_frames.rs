use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

fn run(entry: &str, json: bool) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("docs/design/macros/fixtures/diagnostics")
        .join(entry);
    let mut command = Command::new(env!("CARGO_BIN_EXE_ash"));
    command.args(["--locale", "en"]);
    if json {
        command.args(["--message-format", "json"]);
    }
    let output = command.arg(path).output().expect("driver starts");
    assert_eq!(output.status.code(), Some(1));
    String::from_utf8(output.stderr).unwrap()
}

fn label<'a>(json: &'a serde_json::Value, relationship: &str) -> &'a serde_json::Value {
    let labels = json["labels"].as_array().unwrap();
    let matching: Vec<_> = labels
        .iter()
        .filter(|label| label["relationship"] == relationship)
        .collect();
    assert_eq!(matching.len(), 1, "{json}");
    matching[0]
}

fn assert_span(label: &serde_json::Value, path: &str, start: usize, end: usize) {
    assert!(label["path"].as_str().unwrap().ends_with(path), "{label}");
    assert_eq!(label["byte_start"], start, "{label}");
    assert_eq!(label["byte_end"], end, "{label}");
}

static FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        loop {
            let id = FIXTURE_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-declaration-diagnostic-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("create diagnostic fixture: {error}"),
            }
        }
    }

    fn write(&self, name: &str, contents: &str) {
        fs::write(self.0.join(name), contents).unwrap();
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn declaration_source(name: &str) -> String {
    fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/declarations")
            .join(name),
    )
    .unwrap()
}

fn replace_once(value: &str, old: &str, new: &str) -> String {
    assert_eq!(value.matches(old).count(), 1);
    value.replacen(old, new, 1)
}

fn run_declaration(path: &Path, json: bool, locale: &str) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_ash"));
    command.args(["--locale", locale]);
    if json {
        command.args(["--message-format", "json"]);
    }
    let output = command.arg(path).output().expect("driver starts");
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(!stderr.contains("presentation_error"), "{stderr}");
    stderr
}

fn fact<'a>(json: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    json["facts"]
        .as_array()
        .unwrap()
        .iter()
        .find(|fact| fact["name"] == name)
        .unwrap_or_else(|| panic!("missing {name}: {json}"))
}

#[test]
fn fixed_i15_missing_identifier_reports_matcher_origins() {
    let human = run("missing.ash", false);
    assert!(human.contains("An identifier is required here."), "{human}");
    assert!(human.contains("missing.ash"), "{human}");
    assert!(human.contains("typed_forms.ash"), "{human}");
    assert!(human.contains("The syntax was invoked here"), "{human}");
    assert!(human.contains("The syntax was defined here"), "{human}");

    let json: serde_json::Value = serde_json::from_str(&run("missing.ash", true)).unwrap();
    assert_eq!(json["reason"], "parse.expected-form");
    assert!(
        json["facts"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fact| fact["name"] == "expected" && fact["value"] == "identifier"),
        "{json}"
    );
    assert!(
        json["facts"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fact| fact["name"] == "found" && fact["value"] == "line-end"),
        "{json}"
    );
    assert_span(&json["labels"][0], "missing.ash", 48, 49);
    assert_eq!(json["labels"][0]["relationship"], "expected_form");
    assert_span(label(&json, "syntax_invocation"), "missing.ash", 39, 48);
    assert_span(
        label(&json, "syntax_definition"),
        "typed_forms.ash",
        103,
        203,
    );
}

#[test]
fn fixed_i14_category_reports_retained_matcher_origins() {
    let human = run("category.ash", false);
    assert!(
        human.contains("This token is not allowed at this grammar position."),
        "{human}"
    );
    assert!(human.contains("category.ash"), "{human}");
    assert!(human.contains("category_forms.ash"), "{human}");
    assert!(human.contains("The syntax was invoked here"), "{human}");
    assert!(human.contains("The syntax was defined here"), "{human}");

    let json: serde_json::Value = serde_json::from_str(&run("category.ash", true)).unwrap();
    assert_eq!(json["reason"], "parse.unexpected-token");
    assert!(
        json["facts"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fact| fact["name"] == "found" && fact["value"] == "Int"),
        "{json}"
    );
    assert_span(&json["labels"][0], "category.ash", 45, 63);
    assert_span(label(&json, "syntax_invocation"), "category.ash", 45, 63);
    assert_span(
        label(&json, "syntax_definition"),
        "category_forms.ash",
        43,
        109,
    );
}

#[test]
fn declaration_duplicates_and_newtype_preserve_input_and_expansion_labels() {
    let root =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("docs/design/macros/fixtures/declarations");
    for (entry, reason, primary, first, definition) in [
        (
            "duplicate_operations.ash",
            "resolve.duplicate-global",
            ("duplicate_name", 82, 85),
            ("first_declaration", 71, 74),
            (764, 952),
        ),
        (
            "mismatched_newtype.ash",
            "resolve.newtype-constructor-name",
            ("incorrect_name", 79, 83),
            ("required_name_declaration", 63, 66),
            (156, 291),
        ),
    ] {
        let human = run_declaration(&root.join(entry), false, "en");
        assert!(human.contains(reason), "{human}");
        assert!(human.contains("The syntax was invoked here"), "{human}");
        assert!(human.contains("The syntax was defined here"), "{human}");
        let json: serde_json::Value =
            serde_json::from_str(&run_declaration(&root.join(entry), true, "en")).unwrap();
        assert_eq!(json["reason"], reason);
        assert_eq!(json["responsibility"], "source");
        assert_span(label(&json, primary.0), entry, primary.1, primary.2);
        assert_span(label(&json, first.0), entry, first.1, first.2);
        let invocation = if entry == "duplicate_operations.ash" {
            (45, 85)
        } else {
            (46, 83)
        };
        assert_span(
            label(&json, "syntax_invocation"),
            entry,
            invocation.0,
            invocation.1,
        );
        assert_span(
            label(&json, "syntax_definition"),
            "extra_forms.ash",
            definition.0,
            definition.1,
        );

        let control = format!("control_{entry}");
        let ordinary: serde_json::Value =
            serde_json::from_str(&run_declaration(&root.join(&control), true, "en")).unwrap();
        assert_eq!(ordinary["reason"], reason);
        assert!(
            ordinary["labels"]
                .as_array()
                .unwrap()
                .iter()
                .all(|label| label["relationship"] != "syntax_invocation"
                    && label["relationship"] != "syntax_definition")
        );
    }

    for entry in ["duplicate_methods.ash", "duplicate_constructors.ash"] {
        let json: serde_json::Value =
            serde_json::from_str(&run_declaration(&root.join(entry), true, "en")).unwrap();
        label(&json, "syntax_invocation");
        label(&json, "syntax_definition");
    }
}

#[test]
fn contextual_unknown_type_and_constructor_keep_real_names_and_origins() {
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        &replace_once(
            &declaration_source("forms.ash"),
            "pub newtype $T = $C(Int)",
            "pub newtype $T = $C(Unknown)",
        ),
    );
    fixture.write("case_02.ash", &declaration_source("case_02.ash"));
    fixture.write(
        "control_02.ash",
        &replace_once(
            &declaration_source("control_02.ash"),
            "pub newtype Box = Box(Int)",
            "pub newtype Box = Box(Unknown)",
        ),
    );
    for (entry, generated) in [("case_02.ash", true), ("control_02.ash", false)] {
        let human = run_declaration(&fixture.0.join(entry), false, "en");
        assert!(human.contains("resolve.unknown-type"), "{human}");
        let json: serde_json::Value =
            serde_json::from_str(&run_declaration(&fixture.0.join(entry), true, "en")).unwrap();
        assert_eq!(json["reason"], "resolve.unknown-type");
        assert_eq!(fact(&json, "name")["value"], "Unknown");
        assert_eq!(fact(&json, "lookup_scope")["value"], "type");
        if generated {
            assert_span(label(&json, "unresolved_name"), "forms.ash", 228, 235);
            assert_span(label(&json, "syntax_invocation"), entry, 36, 68);
            assert_span(label(&json, "syntax_definition"), "forms.ash", 130, 238);
        } else {
            assert_span(label(&json, "unresolved_name"), entry, 22, 29);
        }
    }

    fixture.write(
        "forms.ash",
        "pub syntax declaration: (emit) $name:ident => {\n    pub $name : Int -> Int\n    $name Missing = 42\n}\n",
    );
    fixture.write(
        "generated.ash",
        "import forms (syntax emit)\nemit f\nmain : Unit -> Int\nmain () = f(0)\n",
    );
    fixture.write(
        "control.ash",
        "f : Int -> Int\nf Missing = 42\nmain : Unit -> Int\nmain () = f(0)\n",
    );
    for (entry, generated) in [("generated.ash", true), ("control.ash", false)] {
        let human = run_declaration(&fixture.0.join(entry), false, "en");
        assert!(human.contains("resolve.unknown-constructor"), "{human}");
        let json: serde_json::Value =
            serde_json::from_str(&run_declaration(&fixture.0.join(entry), true, "en")).unwrap();
        assert_eq!(json["reason"], "resolve.unknown-constructor");
        assert_eq!(fact(&json, "name")["value"], "Missing");
        assert_eq!(fact(&json, "lookup_scope")["value"], "constructor");
        if generated {
            assert_span(label(&json, "unresolved_name"), "forms.ash", 85, 92);
            assert_span(label(&json, "syntax_invocation"), entry, 27, 33);
            assert_span(label(&json, "syntax_definition"), "forms.ash", 0, 99);
        } else {
            assert_span(label(&json, "unresolved_name"), entry, 17, 24);
        }
    }
}

#[test]
fn foreign_profile_causes_present_in_both_catalogues_with_real_locations() {
    for (duplicate, cause, english, bulgarian, definition_end) in [
        (
            false,
            "missing-supported-profile",
            "One supported foreign profile is required.",
            "Необходим е един поддържан профил за външната библиотека.",
            785,
        ),
        (
            true,
            "unsupported-member",
            "This foreign library member is not supported.",
            "Този член на външната библиотека не се поддържа.",
            871,
        ),
    ] {
        let fixture = Fixture::new();
        let generated_profile = "        profile \"x86_64-unknown-linux-gnu\"\n";
        let ordinary_profile = "    profile \"x86_64-unknown-linux-gnu\"\n";
        fixture.write(
            "forms.ash",
            &replace_once(
                &declaration_source("forms.ash"),
                generated_profile,
                &generated_profile.repeat(usize::from(duplicate) * 2),
            ),
        );
        fixture.write("case_06.ash", &declaration_source("case_06.ash"));
        fixture.write(
            "control_06.ash",
            &replace_once(
                &declaration_source("control_06.ash"),
                ordinary_profile,
                &ordinary_profile.repeat(usize::from(duplicate) * 2),
            ),
        );
        for (entry, generated) in [("case_06.ash", true), ("control_06.ash", false)] {
            for (locale, expected) in [("en", english), ("bg", bulgarian)] {
                let human = run_declaration(&fixture.0.join(entry), false, locale);
                assert!(human.contains(expected), "{human}");
                let json: serde_json::Value =
                    serde_json::from_str(&run_declaration(&fixture.0.join(entry), true, locale))
                        .unwrap();
                assert_eq!(json["reason"], "foreign.contract");
                assert_eq!(json["responsibility"], "source");
                assert_eq!(fact(&json, "contract_cause")["value"], cause);
                assert!(
                    !json["facts"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|f| f["name"] == "lookup_scope")
                );
                if generated {
                    assert_span(label(&json, "foreign_contract"), entry, 36, 68);
                    assert_span(label(&json, "syntax_invocation"), entry, 36, 68);
                    assert_span(
                        label(&json, "syntax_definition"),
                        "forms.ash",
                        618,
                        definition_end,
                    );
                } else {
                    let end = if duplicate { 199 } else { 121 };
                    assert_span(label(&json, "foreign_contract"), entry, 30, end);
                }
            }
        }
    }
}
