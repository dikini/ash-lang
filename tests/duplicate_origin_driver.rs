use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "ash-duplicate-driver-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, text).unwrap();
        path
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn check(
    entry: &Path,
    reason: &str,
    ranges: &[(u32, u32)],
    invocations: &[(u32, u32)],
    definition: &str,
    definition_end: u32,
) {
    for format in ["human", "json"] {
        let output = Command::new(env!("CARGO_BIN_EXE_ash"))
            .args(["--message-format", format, "--locale", "en-US"])
            .arg(entry)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        if format == "human" {
            let text = String::from_utf8(output.stderr).unwrap();
            assert!(text.contains(reason), "{text}");
            assert!(text.contains(definition), "{text}");
            assert_eq!(
                text.matches("The syntax was invoked here.").count(),
                invocations.len(),
                "{text}"
            );
            assert_eq!(
                text.matches(definition).count(),
                invocations.len(),
                "{text}"
            );
            assert!(
                text.matches("The syntax was defined here.").count() >= invocations.len(),
                "{text}"
            );
        } else {
            let json: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
            assert_eq!(json["reason"], reason);
            let labels = json["labels"].as_array().unwrap();
            for (index, (start, end)) in ranges.iter().enumerate() {
                assert_eq!(
                    labels[index]["role"],
                    if index == 0 { "primary" } else { "related" }
                );
                if index == 1 {
                    assert_eq!(labels[index]["relationship"], "first_declaration");
                }
                if index == 2 {
                    assert_eq!(labels[index]["relationship"], "first_definition");
                }
                assert!(
                    Path::new(labels[index]["path"].as_str().unwrap())
                        .ends_with(entry.file_name().unwrap())
                );
                assert_eq!(labels[index]["byte_start"], *start);
                assert_eq!(labels[index]["byte_end"], *end);
            }
            let invocation_labels: Vec<_> = labels
                .iter()
                .filter(|l| l["relationship"] == "syntax_invocation")
                .collect();
            let definition_labels: Vec<_> = labels
                .iter()
                .filter(|l| l["relationship"] == "syntax_definition")
                .collect();
            assert_eq!(invocation_labels.len(), invocations.len());
            assert_eq!(definition_labels.len(), invocations.len());
            for (start, end) in invocations {
                assert!(invocation_labels.iter().any(|l| l["role"] == "related"
                    && Path::new(l["path"].as_str().unwrap()).ends_with(entry.file_name().unwrap())
                    && l["byte_start"] == *start
                    && l["byte_end"] == *end));
            }
            for label in definition_labels {
                assert_eq!(label["role"], "related");
                assert!(label["path"].as_str().unwrap().ends_with(definition));
                assert_eq!(label["byte_start"], 0);
                assert_eq!(label["byte_end"], definition_end);
            }
        }
    }
}

#[test]
fn duplicate_global_origins_reach_the_cli() {
    let root =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("docs/design/macros/fixtures/hygiene");
    check(
        &root.join("early_terms_duplicate.ash"),
        "resolve.duplicate-global",
        &[(106, 118), (69, 81), (46, 81)],
        &[(82, 118), (46, 81)],
        "early_terms_forms.ash",
        190,
    );
    check(
        &root.join("early_terms_handwritten_duplicate.ash"),
        "resolve.duplicate-global",
        &[(114, 120), (106, 112), (82, 112)],
        &[(82, 112)],
        "early_terms_forms.ash",
        190,
    );
    let fixture = Fixture::new();
    fixture.write(
        "early_terms_forms.ash",
        include_str!("../docs/design/macros/fixtures/hygiene/early_terms_forms.ash"),
    );
    let source = "import early_terms_forms (syntax make_value)\nhelper : Unit -> Int\nhelper () = 0\nmake_value first using helper\n";
    let first = source.find("helper :").unwrap() as u32;
    let invocation = source.find("make_value first").unwrap() as u32;
    let generated = source.rfind("helper").unwrap() as u32;
    let entry = fixture.write("entry.ash", source);
    check(
        &entry,
        "resolve.duplicate-global",
        &[
            (generated, generated + 6),
            (first, first + 6),
            (first, invocation - 1),
        ],
        &[(invocation, source.len() as u32 - 1)],
        "early_terms_forms.ash",
        190,
    );
}

#[test]
fn duplicate_nominal_origins_reach_the_cli() {
    let source = include_str!("../docs/design/macros/fixtures/hygiene/private_types.ash");
    let forms = include_str!("../docs/design/macros/fixtures/hygiene/private_type_forms.ash");
    let target = "private_type second using HiddenSecond constructor HiddenSecond";
    assert_eq!(source.matches(target).count(), 1);
    for (replacement, reason, ranges) in [
        (
            "private_type second using HiddenFirst constructor HiddenSecond",
            "resolve.duplicate-type",
            [(136, 147), (74, 85)],
        ),
        (
            "private_type second using HiddenSecond constructor HiddenFirst",
            "resolve.duplicate-constructor",
            [(161, 172), (98, 109)],
        ),
    ] {
        let fixture = Fixture::new();
        fixture.write("private_type_forms.ash", forms);
        let entry = fixture.write("private_types.ash", &source.replace(target, replacement));
        check(
            &entry,
            reason,
            &ranges,
            &[(110, 172), (49, 109)],
            "private_type_forms.ash",
            242,
        );
    }
}

#[test]
fn handwritten_duplicate_controls_have_no_expansion_frames() {
    for (source, reason) in [
        (
            include_str!("fixtures/first-stratum/resolve/r002-duplicate-global.ash"),
            "resolve.duplicate-global",
        ),
        (
            "type Item = First\ntype Item = Second\n",
            "resolve.duplicate-type",
        ),
        (
            "type Left = Same\ntype Right = Same\n",
            "resolve.duplicate-constructor",
        ),
    ] {
        let fixture = Fixture::new();
        let entry = fixture.write("entry.ash", source);
        for format in ["human", "json"] {
            let output = Command::new(env!("CARGO_BIN_EXE_ash"))
                .args(["--message-format", format, "--locale", "en-US"])
                .arg(&entry)
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(1));
            assert!(output.stdout.is_empty());
            if format == "human" {
                let text = String::from_utf8(output.stderr).unwrap();
                assert!(text.contains(reason));
                assert!(!text.contains("The syntax was invoked here."));
                assert!(!text.contains("The syntax was defined here."));
            } else {
                let json: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
                assert_eq!(json["reason"], reason);
                let labels = json["labels"].as_array().unwrap();
                assert_eq!(labels[0]["role"], "primary");
                assert_eq!(labels[1]["relationship"], "first_declaration");
                assert!(
                    labels
                        .iter()
                        .all(|l| l["relationship"] != "syntax_invocation"
                            && l["relationship"] != "syntax_definition")
                );
            }
        }
    }
}

#[test]
fn mixed_nominal_origins_reach_the_cli_in_both_orders() {
    let forms = include_str!("../docs/design/macros/fixtures/hygiene/private_type_forms.ash");
    for (written, generated, reason) in [
        (
            "type HiddenFirst = Written",
            "private_type first using HiddenFirst constructor Other",
            "resolve.duplicate-type",
        ),
        (
            "type Written = HiddenFirst",
            "private_type first using Other constructor HiddenFirst",
            "resolve.duplicate-constructor",
        ),
    ] {
        for generated_first in [false, true] {
            let fixture = Fixture::new();
            fixture.write("private_type_forms.ash", forms);
            let (first, second) = if generated_first {
                (generated, written)
            } else {
                (written, generated)
            };
            let source =
                format!("import private_type_forms (syntax private_type)\n{first}\n{second}\n");
            let names: Vec<u32> = source
                .match_indices("HiddenFirst")
                .map(|(n, _)| n as u32)
                .collect();
            assert_eq!(names.len(), 2);
            let invocation = source.find("private_type first").unwrap() as u32;
            let entry = fixture.write("entry.ash", &source);
            check(
                &entry,
                reason,
                &[(names[1], names[1] + 11), (names[0], names[0] + 11)],
                &[(invocation, invocation + generated.len() as u32)],
                "private_type_forms.ash",
                242,
            );
        }
    }
}
