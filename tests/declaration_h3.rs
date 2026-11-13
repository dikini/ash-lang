use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{PipelineFailure, RunConfiguration, compile_path, execute},
    elaborate::{TypeError, TypeReason},
    module::ModuleRoots,
    resolve::ResolveReason,
};

fn fixed_fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/hygiene")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-h3-nominal-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, text: &str) {
        fs::write(self.0.join(name), text).unwrap();
    }

    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn i12_caller_selected_private_types_reach_the_ordinary_driver() {
    for name in ["private_types.ash", "control_private_types.ash"] {
        let program = compile_path(fixed_fixture(name)).expect("the fixed I12 case compiles");
        assert_eq!(execute(&program).unwrap().value_display(), "84");
    }
}

#[test]
fn i12_duplicate_private_types_and_constructors_reach_ordinary_resolution() {
    let original = include_str!("../docs/design/macros/fixtures/hygiene/private_types.ash");
    let forms = include_str!("../docs/design/macros/fixtures/hygiene/private_type_forms.ash");
    let target = "private_type second using HiddenSecond constructor HiddenSecond";
    assert_eq!(original.matches(target).count(), 1);
    for (replacement, reason, expected) in [
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
        fixture.write("entry.ash", &original.replace(target, replacement));
        let failure = compile_path(fixture.configuration()).expect_err("the duplicate must reject");
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("expected ordinary resolution failure: {failure:?}");
        };
        assert_eq!(error.reason, reason);
        let entry = fs::canonicalize(fixture.0.join("entry.ash")).unwrap();
        let source = failure
            .sources()
            .iter()
            .find(|source| Path::new(source.display_path()) == entry)
            .expect("the caller source is retained");
        let [first] = error.related.as_slice() else {
            panic!("expected the earlier declaration");
        };
        for (label, (start, end)) in [&error.primary, first].into_iter().zip(expected) {
            let span = label.span();
            assert_eq!(span.source(), source.id());
            assert_eq!((span.range().start(), span.range().end()), (start, end));
        }
    }
}

#[test]
fn generated_nominal_families_remain_distinct_in_ordinary_checking() {
    let forms = "pub syntax declaration: (family) $typename:ident constructor $constructor:ident make $make:ident consume $consume:ident => {\n    type $typename = $constructor\n    $make : Unit -> $typename\n    $make () = $constructor\n    $consume : $typename -> Int\n    $consume value = match value {\n        $constructor => 42\n    }\n}\n";
    let generated = "import forms (syntax family)\nfamily One constructor One make make_one consume consume_one\nfamily Two constructor Two make make_two consume consume_two\nmain : Unit -> Int\nmain () = consume_one(make_one(())) + consume_two(make_two(()))\n";
    let handwritten = "type One = One\ntype Two = Two\nmake_one : Unit -> One\nmake_one () = One\nconsume_one : One -> Int\nconsume_one value = match value {\n    One => 42\n}\nmake_two : Unit -> Two\nmake_two () = Two\nconsume_two : Two -> Int\nconsume_two value = match value {\n    Two => 42\n}\nmain : Unit -> Int\nmain () = consume_one(make_one(())) + consume_two(make_two(()))\n";
    let positive = "consume_one(make_one(())) + consume_two(make_two(()))";
    for entry in [generated, handwritten] {
        assert_eq!(entry.matches(positive).count(), 1);
        let fixture = Fixture::new();
        fixture.write("forms.ash", forms);
        fixture.write("entry.ash", entry);
        let program = compile_path(fixture.configuration()).expect("both nominal families compile");
        assert_eq!(execute(&program).unwrap().value_display(), "84");

        fixture.write(
            "entry.ash",
            &entry.replace(positive, "consume_one(make_two(()))"),
        );
        let failure =
            compile_path(fixture.configuration()).expect_err("crossed families must reject");
        let Some(PipelineFailure::Typing(TypeError::Source(error))) = failure.pipeline_failure()
        else {
            panic!("expected ordinary source type failure: {failure:?}");
        };
        assert_eq!(error.reason, TypeReason::Argument);
        assert_eq!(error.expected.as_deref(), Some("One"));
        assert_eq!(error.found.as_deref(), Some("Two"));
    }
}
