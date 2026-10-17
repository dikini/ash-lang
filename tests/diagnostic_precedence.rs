use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, compile_path},
    elaborate::TypeError,
    kind::KindFailure,
    module::ModuleRoots,
};

static NEXT_ID: AtomicU64 = AtomicU64::new(0);
const MAIN: &str = "main : Unit -> Int\nmain () = 0\n";
const BAD_ARITY: &str =
    "interface C<A> {\n    c : A -> Int\n}\nbad : Unit -> Unit where C<Int, Bool>\nbad () = ()\n";
const BAD_DETERMINATION: &str =
    "interface Invalid<A, B, C> where A -> B {\n    invalid : A -> B\n}\n";

struct Fixture(PathBuf);

impl Fixture {
    fn new(source: &str) -> Self {
        loop {
            let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir().join(format!(
                "ash-diagnostic-precedence-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join("entry.ash");
                    fs::write(&path, source).unwrap();
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("precedence fixture: {error}"),
            }
        }
    }

    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.clone(),
            roots: ModuleRoots::empty(),
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(self.0.parent().unwrap()).unwrap();
    }
}

fn rejected(source: &str, reason: &str, primary: &str) -> FileFailure {
    let fixture = Fixture::new(source);
    let failure = compile_path(fixture.configuration()).expect_err("invalid source must reject");
    let pipeline = failure.pipeline_failure().expect("source pipeline failure");
    assert_eq!(pipeline.reason_code(), reason, "source:\n{source}");
    assert!(pipeline.is_source_rejection(), "source:\n{source}");
    let span = match pipeline {
        PipelineFailure::Kind(KindFailure::Source(error)) => {
            if reason == "kind.expected-type" {
                assert_eq!(error.expected_kind(), Some(&ash::types::Kind::Type));
                assert_eq!(
                    error.found_kind(),
                    Some(&ash::types::Kind::Arrow(
                        Box::new(ash::types::Kind::Type),
                        Box::new(ash::types::Kind::Type),
                    ))
                );
                if matches!(primary, "F" | "G") {
                    assert_eq!(error.related.len(), 1);
                    let start = source.find(&format!("<{primary}")).unwrap() + 1;
                    let related = error.related[0].span().range();
                    assert_eq!(related.start() as usize, start);
                    assert_eq!(related.end() as usize, start + primary.len());
                    let occurrence = source.rfind(&format!("({primary})")).unwrap() + 1;
                    assert_eq!(error.primary.span().range().start() as usize, occurrence);
                    assert_eq!(
                        error.primary.span().range().end() as usize,
                        occurrence + primary.len()
                    );
                }
            } else if reason == "kind.argument" {
                assert_eq!(error.found_kind(), Some(&ash::types::Kind::Type));
                assert!(matches!(
                    error.expected_kind(),
                    Some(ash::types::Kind::Arrow(_, _))
                ));
            }
            error.primary.span()
        }
        PipelineFailure::Typing(TypeError::Source(error)) => error.primary.span(),
        PipelineFailure::Typing(TypeError::Interface(error)) => error.primary.span(),
        other => panic!("unexpected diagnostic owner: {other:?}"),
    };
    assert_eq!(
        &source[span.range().start() as usize..span.range().end() as usize],
        primary,
        "the earlier stage must retain its causal span: {source}"
    );
    failure
}

#[test]
fn representation_kinds_precede_interface_arity_in_both_declaration_orders() {
    for representation in [
        "newtype Wrong<F : Type -> Type> = Wrong(F)\n",
        "type Wrong<F : Type -> Type> = Wrong(F)\n",
    ] {
        for declarations in [
            format!("{representation}{BAD_ARITY}"),
            format!("{BAD_ARITY}{representation}"),
        ] {
            rejected(&format!("{declarations}{MAIN}"), "kind.expected-type", "F");
        }
    }
}

#[test]
fn representation_kinds_precede_invalid_determination() {
    rejected(
        &format!("{BAD_DETERMINATION}newtype Wrong<F : Type -> Type> = Wrong(F)\n{MAIN}"),
        "kind.expected-type",
        "F",
    );
}

#[test]
fn nested_representation_effect_argument_kind_precedes_interface_arity() {
    let effect = "effect Tag<F : Type -> Type> {\n    emit : Unit -> Unit\n}\n";
    for representation in [
        "newtype Wrong = Wrong(Unit -> Unit ! {Tag<Int>})\n",
        "type Wrong = Wrong((Int, Unit -> Unit ! {Tag<Int>}))\n",
    ] {
        rejected(
            &format!("{effect}{BAD_ARITY}{representation}{MAIN}"),
            "kind.argument",
            "Int",
        );
    }
}

#[test]
fn written_nested_effect_arity_is_a_source_failure_before_interface_checks() {
    for later in ["", BAD_ARITY] {
        let failure = rejected(
            &format!(
                "effect Tag<A> {{\n    emit : Unit -> Unit\n}}\nnewtype Wrong = Wrong(Unit -> Unit ! {{Tag<Int, Bool>}})\n{later}{MAIN}"
            ),
            "effect.argument-count",
            "Tag<Int, Bool>",
        );
        let PipelineFailure::Kind(KindFailure::Source(error)) = failure.pipeline_failure().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(error.related.len(), 1);
        assert_eq!(error.argument_counts(), Some((1, 2)));
        assert_eq!(error.expected_kind(), None);
        assert_eq!(error.found_kind(), None);
        let header = error.related[0].span().range();
        assert_eq!(header.start(), 0);
        assert_eq!(
            header.end() as usize,
            "effect Tag<A> {\n    emit : Unit -> Unit\n}".len()
        );
        use ash::{
            message::{Catalogue, Locale},
            presentation::{compile_kind_diagnostic, write_human, write_json},
        };
        let sources: Vec<_> = failure.sources().iter().collect();
        let view = compile_kind_diagnostic(error, &sources).unwrap();
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_human(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
            let output = String::from_utf8(output).unwrap();
            assert!(output.contains("1"), "{output}");
            assert!(output.contains("2"), "{output}");
            assert!(output.contains("Tag<Int, Bool>"), "{output}");
        }
        let mut output = Vec::new();
        write_json(&mut output, &view).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["reason"], "effect.argument-count");
        assert_eq!(json["responsibility"], "source");
        assert_eq!(json["facts"][0]["name"], "expected_count");
        assert_eq!(json["facts"][0]["value"], 1);
        assert_eq!(json["facts"][1]["name"], "supplied_count");
        assert_eq!(json["facts"][1]["value"], 2);
        assert_eq!(json["labels"][0]["relationship"], "effect_application");
        assert_eq!(json["labels"][1]["relationship"], "effect_parameters");
    }
}

#[test]
fn nested_row_and_zero_argument_effect_arity_keep_their_written_sites() {
    let effects = concat!(
        "effect Tag<A> {\n    emit : Unit -> Unit\n}\n",
        "effect Outer<Rows : EffectRow> {\n    wrap : Unit -> Unit\n}\n",
    );
    for (representation, application, supplied) in [
        (
            "Unit -> Unit ! {Outer<{Tag<Int, Bool>}>}",
            "Tag<Int, Bool>",
            2,
        ),
        ("Int -> (Unit -> Unit ! {Tag})", "Tag", 0),
        ("Unit -> Unit ! {Outer<{Tag}>}", "Tag", 0),
    ] {
        let failure = rejected(
            &format!("{effects}newtype Wrong = Wrong({representation})\n{BAD_ARITY}{MAIN}"),
            "effect.argument-count",
            application,
        );
        let PipelineFailure::Kind(KindFailure::Source(error)) = failure.pipeline_failure().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(error.argument_counts(), Some((1, supplied)));
        assert_eq!(
            error.primary.span().range().start() as usize,
            effects.len()
                + "newtype Wrong = Wrong(".len()
                + representation.find(application).unwrap()
        );
    }
}

#[test]
fn imported_effect_arity_labels_the_application_and_original_header() {
    let entry = concat!(
        "import dependency as Dependency\n",
        "newtype Wrong = Wrong(Unit -> Unit ! {Dependency.Tag<Int, Bool>})\n",
        "main : Unit -> Int\nmain () = 0\n",
    );
    let dependency = "pub effect Tag<A> {\n    emit : Unit -> Unit\n}\n";
    let fixture = Fixture::new(entry);
    fs::write(
        fixture.0.parent().unwrap().join("dependency.ash"),
        dependency,
    )
    .unwrap();
    let failure = compile_path(fixture.configuration()).expect_err("written imported arity");
    let Some(PipelineFailure::Kind(KindFailure::Source(error))) = failure.pipeline_failure() else {
        panic!("a written source instance must retain source responsibility")
    };
    assert_eq!(error.reason.to_string(), "effect.argument-count");
    assert_eq!(error.argument_counts(), Some((1, 2)));
    let primary = error.primary.span();
    let start = entry.find("Dependency.Tag<Int, Bool>").unwrap();
    assert_eq!(primary.range().start() as usize, start);
    assert_eq!(
        primary.range().end() as usize,
        start + "Dependency.Tag<Int, Bool>".len()
    );
    let [related] = error.related.as_slice() else {
        panic!("original effect header")
    };
    assert_ne!(primary.source(), related.span().source());
    assert_eq!(related.span().range().start(), 0);
    assert_eq!(
        related.span().range().end() as usize,
        dependency.trim_end().len()
    );
    let sources: Vec<_> = failure.sources().iter().collect();
    let view = ash::presentation::compile_kind_diagnostic(error, &sources).unwrap();
    let mut json = Vec::new();
    ash::presentation::write_json(&mut json, &view).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    assert_eq!(json["responsibility"], "source");
    assert_eq!(json["labels"][1]["relationship"], "effect_parameters");
}

#[test]
fn module_representation_kinds_precede_earlier_global_and_local_kinds() {
    for earlier in [
        "type Box<A> = Box(A)\nbad : Unit -> Box\nbad () = Box(1)\n",
        "bad : Unit -> Unit\nbad () = {\n    newtype Local<F : Type -> Type> = Local(F)\n    ()\n}\n",
    ] {
        let source = format!("{earlier}newtype Wrong<G : Type -> Type> = Wrong(G)\n{MAIN}");
        rejected(&source, "kind.expected-type", "G");
    }
}

#[test]
fn representation_cycles_precede_remaining_global_effect_and_interface_checks() {
    for later in [
        "type Box<A> = Box(A)\nbad : Unit -> Box\nbad () = Box(1)\n",
        "type Box<A> = Box(A)\neffect Invalid {\n    use : Box -> Unit\n}\n",
        BAD_ARITY,
        BAD_DETERMINATION,
    ] {
        let failure = rejected(
            &format!("newtype Loop = Loop(Loop)\n{later}{MAIN}"),
            "newtype.recursive-representation",
            "Loop",
        );
        let PipelineFailure::Typing(TypeError::Source(error)) = failure.pipeline_failure().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(error.primary.span().range().start(), 20);
        assert_eq!(error.primary.span().range().end(), 24);
        assert_eq!(
            error.primary.message(),
            "this newtype representation closes a recursive representation cycle"
        );
        assert_eq!(error.related.len(), 1);
        assert_eq!(error.related[0].span().range().start(), 0);
        assert_eq!(error.related[0].span().range().end(), 25);
        assert_eq!(
            error.related[0].message(),
            "this declaration participates in the recursive representation cycle"
        );
    }
}

#[test]
fn remaining_effect_kinds_precede_determination_and_method_kinds() {
    for earlier in [
        BAD_DETERMINATION,
        "interface Invalid<F : Type -> Type> {\n    invalid : F -> Unit\n}\n",
    ] {
        rejected(
            &format!(
                "type Box<A> = Box(A)\n{earlier}effect Later {{\n    use : Box -> Unit\n}}\n{MAIN}"
            ),
            "kind.expected-type",
            "Box",
        );
    }
}

#[test]
fn repairing_an_earlier_stage_keeps_later_failures_reachable() {
    rejected(
        &format!("newtype Good<F : Type -> Type> = Good(F<Int>)\n{BAD_ARITY}{MAIN}"),
        "interface.argument-count",
        "C<Int, Bool>",
    );
    rejected(
        &format!(
            "newtype Loop = Loop(Int)\ntype Box<A> = Box(A)\nbad : Unit -> Box\nbad () = Box(1)\n{MAIN}"
        ),
        "kind.expected-type",
        "Box",
    );
    rejected(
        &format!("{BAD_DETERMINATION}{MAIN}"),
        "interface.determination-parameter",
        "where A -> B",
    );
}

#[test]
fn well_kinded_acyclic_declarations_still_compile_through_core() {
    let fixture = Fixture::new(&format!(
        "type Box<A> = Box(A)\nnewtype Good<F : Type -> Type> = Good(F<Int>)\nnewtype Loop = Loop(Box<Int>)\ninterface Valid<A, B> where A -> B {{\n    valid : A -> B\n}}\neffect Tag<A> {{\n    emit : Unit -> A\n}}\n{MAIN}"
    ));
    compile_path(fixture.configuration()).expect("all staged checks should accept valid source");
}
