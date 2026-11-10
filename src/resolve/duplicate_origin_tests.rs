use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use crate::{
    driver::{PipelineFailure, RunConfiguration, compile_path},
    message::{Catalogue, Locale},
    module::ModuleRoots,
    presentation::{compile_resolve_diagnostic, write_human, write_json},
    resolve::ResolveReason,
};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "ash-duplicate-origin-{}-{}",
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
    entry: PathBuf,
    reason: ResolveReason,
    ranges: &[(u32, u32)],
    frames: &[Option<((u32, u32), (u32, u32))>],
    definition: Option<&str>,
) {
    let failure = compile_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect_err("the duplicate must reject");
    let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
        panic!("expected resolution failure: {failure:?}")
    };
    assert_eq!(error.reason, reason);
    let labels: Vec<_> = std::iter::once(&error.primary)
        .chain(&error.related)
        .collect();
    assert_eq!(labels.len(), ranges.len());
    let caller = failure
        .sources()
        .iter()
        .find(|s| s.id() == labels[0].span().source())
        .unwrap();
    for ((label, &(start, end)), frame) in labels.iter().zip(ranges).zip(frames) {
        assert_eq!(label.span().source(), caller.id());
        assert_eq!(
            (label.span().range().start(), label.span().range().end()),
            (start, end)
        );
        match (label.diagnostic_location(), frame) {
            (None, None) => {}
            (Some(location), Some((invocation, definition_range))) => {
                assert_eq!(location.frames.len(), 1);
                let frame = &location.frames[0];
                assert_eq!(frame.invocation.source(), caller.id());
                assert_eq!(
                    (
                        frame.invocation.range().start(),
                        frame.invocation.range().end()
                    ),
                    *invocation
                );
                let source = failure
                    .sources()
                    .iter()
                    .find(|s| s.id() == frame.definition.source())
                    .unwrap();
                assert!(source.display_path().ends_with(definition.unwrap()));
                assert_eq!(
                    (
                        frame.definition.range().start(),
                        frame.definition.range().end()
                    ),
                    *definition_range
                );
            }
            other => panic!("unexpected label location: {other:?}"),
        }
    }
    let sources: Vec<_> = failure.sources().iter().collect();
    let view = compile_resolve_diagnostic(error, &sources).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &view).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    assert_eq!(json["reason"], reason.to_string());
    let out = json["labels"].as_array().unwrap();
    assert_eq!(out[0]["role"], "primary");
    assert_eq!(out[1]["relationship"], "first_declaration");
    if ranges.len() == 3 {
        assert_eq!(out[2]["relationship"], "first_definition");
    }
    for ((start, end), label) in ranges.iter().zip(out) {
        assert_eq!(label["path"], caller.display_path());
        assert_eq!(label["byte_start"], *start);
        assert_eq!(label["byte_end"], *end);
    }
    for ((inv_start, inv_end), (def_start, def_end)) in frames.iter().flatten() {
        for (relationship, path, start, end) in [
            (
                "syntax_invocation",
                caller.display_path(),
                *inv_start,
                *inv_end,
            ),
            (
                "syntax_definition",
                definition.unwrap(),
                *def_start,
                *def_end,
            ),
        ] {
            assert!(
                out.iter().any(|label| label["role"] == "related"
                    && label["relationship"] == relationship
                    && label["path"].as_str().unwrap().ends_with(path)
                    && label["byte_start"] == start
                    && label["byte_end"] == end),
                "missing {relationship}: {out:?}"
            );
        }
    }
    let expected_frames = frames.iter().flatten().count();
    assert_eq!(
        out.iter()
            .filter(|v| v["relationship"] == "syntax_invocation")
            .count(),
        expected_frames
    );
    assert_eq!(
        out.iter()
            .filter(|v| v["relationship"] == "syntax_definition")
            .count(),
        expected_frames
    );
    let mut human = Vec::new();
    write_human(&mut human, &view, &Catalogue::new(Locale::English).unwrap()).unwrap();
    let human = String::from_utf8(human).unwrap();
    assert_eq!(
        human.matches("The syntax was invoked here.").count(),
        expected_frames,
        "{human}"
    );
    if let Some(definition) = definition {
        assert_eq!(
            human.matches(definition).count(),
            expected_frames,
            "{human}"
        );
        assert!(
            human.matches("The syntax was defined here.").count() >= expected_frames,
            "{human}"
        );
    } else {
        assert!(!human.contains("The syntax was defined here."), "{human}");
    }
}

#[test]
fn duplicate_globals_carry_each_real_origin() {
    let root =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("docs/design/macros/fixtures/hygiene");
    check(
        root.join("early_terms_duplicate.ash"),
        ResolveReason::DuplicateGlobal,
        &[(106, 118), (69, 81), (46, 81)],
        &[
            Some(((82, 118), (0, 190))),
            Some(((46, 81), (0, 190))),
            None,
        ],
        Some("early_terms_forms.ash"),
    );
    check(
        root.join("early_terms_handwritten_duplicate.ash"),
        ResolveReason::DuplicateGlobal,
        &[(114, 120), (106, 112), (82, 112)],
        &[None, Some(((82, 112), (0, 190))), None],
        Some("early_terms_forms.ash"),
    );
    let fixture = Fixture::new();
    fixture.write(
        "early_terms_forms.ash",
        include_str!("../../docs/design/macros/fixtures/hygiene/early_terms_forms.ash"),
    );
    let source = "import early_terms_forms (syntax make_value)\nhelper : Unit -> Int\nhelper () = 0\nmake_value first using helper\n";
    let first = source.find("helper :").unwrap() as u32;
    let invocation = source.find("make_value first").unwrap() as u32;
    let generated = source.rfind("helper").unwrap() as u32;
    check(
        fixture.write("entry.ash", source),
        ResolveReason::DuplicateGlobal,
        &[
            (generated, generated + 6),
            (first, first + 6),
            (first, invocation - 1),
        ],
        &[
            Some(((invocation, source.len() as u32 - 1), (0, 190))),
            None,
            None,
        ],
        Some("early_terms_forms.ash"),
    );

    let fixture = Fixture::new();
    let source =
        include_str!("../../tests/fixtures/first-stratum/resolve/r002-duplicate-global.ash");
    let starts: Vec<_> = source
        .match_indices("value")
        .map(|(n, _)| n as u32)
        .collect();
    // The second definition is the `fn` declaration; its first complete definition is the signature/equation pair.
    let failure = compile_path(RunConfiguration {
        entry: fixture.write("entry.ash", source),
        roots: ModuleRoots::empty(),
    })
    .unwrap_err();
    let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
        panic!()
    };
    assert_eq!(error.reason, ResolveReason::DuplicateGlobal);
    assert_eq!(error.primary.span().range().start(), starts[2]);
    let ranges: Vec<_> = std::iter::once(&error.primary)
        .chain(&error.related)
        .map(|l| (l.span().range().start(), l.span().range().end()))
        .collect();
    check(
        fixture.0.join("entry.ash"),
        ResolveReason::DuplicateGlobal,
        &ranges,
        &vec![None; ranges.len()],
        None,
    );
}

#[test]
fn duplicate_nominals_carry_each_real_origin() {
    let source = include_str!("../../docs/design/macros/fixtures/hygiene/private_types.ash");
    let forms = include_str!("../../docs/design/macros/fixtures/hygiene/private_type_forms.ash");
    let target = "private_type second using HiddenSecond constructor HiddenSecond";
    assert_eq!(source.matches(target).count(), 1);
    for (replacement, reason, ranges) in [
        (
            "private_type second using HiddenFirst constructor HiddenSecond",
            ResolveReason::DuplicateType,
            [(136, 147), (74, 85)],
        ),
        (
            "private_type second using HiddenSecond constructor HiddenFirst",
            ResolveReason::DuplicateConstructor,
            [(161, 172), (98, 109)],
        ),
    ] {
        let fixture = Fixture::new();
        fixture.write("private_type_forms.ash", forms);
        check(
            fixture.write("entry.ash", &source.replace(target, replacement)),
            reason,
            &ranges,
            &[Some(((110, 172), (0, 242))), Some(((49, 109), (0, 242)))],
            Some("private_type_forms.ash"),
        );
    }
    for (text, reason) in [
        (
            "type Item = First\ntype Item = Second\n",
            ResolveReason::DuplicateType,
        ),
        (
            "type Left = Same\ntype Right = Same\n",
            ResolveReason::DuplicateConstructor,
        ),
    ] {
        let fixture = Fixture::new();
        let failure = compile_path(RunConfiguration {
            entry: fixture.write("entry.ash", text),
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("{failure:?}")
        };
        assert_eq!(error.reason, reason);
        let ranges: Vec<_> = std::iter::once(&error.primary)
            .chain(&error.related)
            .map(|l| (l.span().range().start(), l.span().range().end()))
            .collect();
        check(
            fixture.0.join("entry.ash"),
            reason,
            &ranges,
            &vec![None; ranges.len()],
            None,
        );
    }
}

#[test]
fn mixed_nominal_origins_follow_each_actual_declaration() {
    let forms = include_str!("../../docs/design/macros/fixtures/hygiene/private_type_forms.ash");
    for (written, generated, reason) in [
        (
            "type HiddenFirst = Written",
            "private_type first using HiddenFirst constructor Other",
            ResolveReason::DuplicateType,
        ),
        (
            "type Written = HiddenFirst",
            "private_type first using Other constructor HiddenFirst",
            ResolveReason::DuplicateConstructor,
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
            let frame = Some(((invocation, invocation + generated.len() as u32), (0, 242)));
            let frames = if generated_first {
                [None, frame]
            } else {
                [frame, None]
            };
            check(
                fixture.write("entry.ash", &source),
                reason,
                &[(names[1], names[1] + 11), (names[0], names[0] + 11)],
                &frames,
                Some("private_type_forms.ash"),
            );
        }
    }
}

#[test]
fn duplicate_label_retains_its_span_when_origin_primary_differs() {
    use crate::{
        diagnostic::SourceLabel,
        source::{ByteRange, SourceFile},
        syntax::DiagnosticLocation,
    };
    let source = SourceFile::new("unequal.ash", "first second").unwrap();
    let name = source.span(ByteRange::new(0, 5).unwrap()).unwrap();
    let origin = source.span(ByteRange::new(6, 12).unwrap()).unwrap();
    let location = DiagnosticLocation::new(origin.into());
    let label = SourceLabel::new(name, "name").with_location_preserving_span(Some(&location));
    assert_eq!(label.span(), name);
    assert_eq!(
        label.diagnostic_location().unwrap().primary.primary(),
        origin
    );
}

#[test]
fn unequal_origin_is_rendered_alongside_the_ordinary_duplicate_label() {
    use crate::{
        diagnostic::{Diagnostic, SourceLabel},
        resolve::ResolveError,
        source::{ByteRange, SourceFile},
        syntax::{DiagnosticLocation, ExpansionFrame},
    };
    use std::sync::Arc;
    let caller = SourceFile::new("unequal-caller.ash", "first second").unwrap();
    let forms = SourceFile::new("unequal-forms.ash", "definition").unwrap();
    let name = caller.span(ByteRange::new(0, 5).unwrap()).unwrap();
    let origin = caller.span(ByteRange::new(6, 12).unwrap()).unwrap();
    let definition = forms.span(ByteRange::new(0, 10).unwrap()).unwrap();
    let mut location = DiagnosticLocation::new(origin.into());
    location.add_frame(&Arc::new(ExpansionFrame {
        invocation: origin,
        definition,
    }));
    let mut diagnostic = Diagnostic::new(
        ResolveReason::DuplicateType,
        SourceLabel::new(name, "name").with_location_preserving_span(Some(&location)),
    );
    diagnostic.related.push(SourceLabel::new(origin, "first"));
    diagnostic.found = Some("first".into());
    let error: ResolveError = diagnostic.into();
    let view = compile_resolve_diagnostic(&error, &[&caller, &forms]).unwrap();
    let mut json = Vec::new();
    write_json(&mut json, &view).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    assert_eq!(labels[0]["byte_start"], 0);
    assert_eq!(labels[0]["byte_end"], 5);
    for (relationship, path, start, end) in [
        ("syntax_cause", "unequal-caller.ash", 6, 12),
        ("syntax_invocation", "unequal-caller.ash", 6, 12),
        ("syntax_definition", "unequal-forms.ash", 0, 10),
    ] {
        assert!(
            labels.iter().any(|l| l["role"] == "related"
                && l["relationship"] == relationship
                && l["path"] == path
                && l["byte_start"] == start
                && l["byte_end"] == end),
            "{labels:?}"
        );
    }
    let mut human = Vec::new();
    write_human(&mut human, &view, &Catalogue::new(Locale::English).unwrap()).unwrap();
    let human = String::from_utf8(human).unwrap();
    assert!(human.contains("unequal-caller.ash"));
    assert!(human.contains("unequal-forms.ash"));
    assert!(human.contains("This location contributed to the rejection."));
    assert!(human.contains("The syntax was invoked here."));
    assert!(human.contains("The syntax was defined here."));
}
