use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::driver::{PipelineFailure, RunConfiguration, run_path};
use ash::module::ModuleRoots;
use ash::resolve::ResolveReason;

static IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);
impl Fixture {
    fn new(source: &str) -> Self {
        loop {
            let id = IDS.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("ash-source-native-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => {
                    fs::write(path.join("entry.ash"), source).unwrap();
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("source-native fixture: {error}"),
            }
        }
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

const CONTRACT: &str = r#"import @builtin.foreign as Foreign
pub foreign library C {
    profile "x86_64-unknown-linux-gnu"
    repr CInt = signed(32)
    symbol Abs<Before : EffectRow, T, After : EffectRow> : Int -> Foreign.Call<Int> {
        name "abs"
        abi (CInt) -> CInt
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Stop : Unit -> Foreign.Call<Unit> {
        name "stop"
        abi () -> void
        outcome otherwise {}
    }
}
"#;

#[test]
fn source_native_declarations_are_passive_and_check_complete_parameter_vectors() {
    let fixture = Fixture::new(&format!("{CONTRACT}main : Unit -> Int\nmain () = 42\n"));
    let observation = run_path(fixture.configuration()).unwrap();
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn published_native_effects_keep_their_complete_kinds_through_imports() {
    let fixture = Fixture::new("import native as Native\nmain : Unit -> Int\nmain () = 42\n");
    fs::write(fixture.0.join("native.ash"), CONTRACT).unwrap();
    assert_eq!(
        run_path(fixture.configuration()).unwrap().value_display(),
        "42"
    );
    fs::write(fixture.0.join("entry.ash"), "import native as Native\nprobe : Unit -> Int ! {Native.Abs<Int, Int, Int>}\nprobe () = 42\nmain : Unit -> Int\nmain () = 42\n").unwrap();
    assert!(
        run_path(fixture.configuration()).is_err(),
        "Type arguments must not stand in for row arguments"
    );
}

#[test]
fn native_descriptors_follow_selected_and_reexported_effect_facts() {
    for (native, entry, facade) in [
        (
            CONTRACT.replace("pub foreign library", "foreign library"),
            "import native (answer)\nmain : Unit -> Int\nmain () = answer ()\n",
            None,
        ),
        (
            CONTRACT.to_owned(),
            "import native (answer)\nmain : Unit -> Int\nmain () = answer ()\n",
            None,
        ),
        (
            CONTRACT.to_owned(),
            "import facade (Halt)\nprobe : Unit -> Unit ! {Halt}\nprobe () = ()\nmain : Unit -> Int\nmain () = 42\n",
            Some("pub import native (Stop as Halt)\n"),
        ),
        (
            CONTRACT.to_owned(),
            "import native (Stop as Halt)\nprobe : Unit -> Unit ! {Halt}\nprobe () = ()\nmain : Unit -> Int\nmain () = 42\n",
            None,
        ),
        (
            format!(
                "{}pub unused : Unit -> Unit ! {{Stop}}\nunused () = ()\n",
                CONTRACT.replace("pub foreign library", "foreign library")
            ),
            "import native (unused)\nmain : Unit -> Int\nmain () = 42\n",
            None,
        ),
        (
            CONTRACT.to_owned(),
            "import facade as Facade\nimport native as Native\nprobe : Unit -> Unit ! {Facade.Absolute<{}, Int, {}>}\nprobe () = ()\nmain : Unit -> Int\nmain () = 42\n",
            Some("pub import native (Abs as Absolute)\n"),
        ),
    ] {
        let fixture = Fixture::new(entry);
        fs::write(
            fixture.0.join("native.ash"),
            format!("{native}pub answer : Unit -> Int\nanswer () = 42\n"),
        )
        .unwrap();
        if let Some(facade) = facade {
            fs::write(fixture.0.join("facade.ash"), facade).unwrap();
        }
        assert_eq!(
            run_path(fixture.configuration()).unwrap().value_display(),
            "42"
        );
    }
}

#[test]
fn a_public_signature_does_not_publish_private_native_member_names() {
    for entry in [
        "import native (Stop)\nmain : Unit -> Int\nmain () = 42\n",
        "pub import native (Stop)\nmain : Unit -> Int\nmain () = 42\n",
    ] {
        let fixture = Fixture::new(entry);
        fs::write(
            fixture.0.join("native.ash"),
            format!(
                "{}pub unused : Unit -> Unit ! {{Stop}}\nunused () = ()\n",
                CONTRACT.replace("pub foreign library", "foreign library")
            ),
        )
        .unwrap();
        assert!(matches!(
            run_path(fixture.configuration())
                .unwrap_err()
                .pipeline_failure(),
            Some(PipelineFailure::Resolution(_))
        ));
    }
}

#[test]
fn same_named_result_types_and_incorrect_codomains_grant_no_native_authority() {
    for text in [
        CONTRACT.replace("Foreign.Call<Int>", "Int"),
        CONTRACT.replace(
            "import @builtin.foreign as Foreign",
            "import donor as Foreign",
        ),
        CONTRACT.replace("Foreign.Call<Unit>", "Foreign.Call<Int>"),
    ] {
        let fixture = Fixture::new(&format!("{text}main : Unit -> Int\nmain () = 42\n"));
        fs::write(fixture.0.join("donor.ash"), "pub opaque type ConversionError = Hidden\npub type Call<T> = Returned(T)\n    | ConversionFailed(ConversionError)\n").unwrap();
        let failure = run_path(fixture.configuration()).unwrap_err();
        assert!(
            matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error)) if error.reason == ResolveReason::ForeignContract),
            "{failure:?}"
        );
    }
}

#[test]
fn foreign_and_ordinary_effect_names_share_the_collision_boundary() {
    let fixture = Fixture::new(&format!(
        "{CONTRACT}effect Abs {{\ncall : Int -> Int\n}}\nmain : Unit -> Int\nmain () = 42\n"
    ));
    let failure = run_path(fixture.configuration()).unwrap_err();
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error)) if error.reason == ResolveReason::DuplicateType),
        "{failure:?}"
    );
}

#[test]
fn libraries_require_disjoint_member_spellings_including_abi_only_members() {
    let fixture = Fixture::new(&format!(
        "{CONTRACT}foreign library Other {{\n    profile \"x86_64-unknown-linux-gnu\"\n    repr CInt = signed(32)\n}}\nmain : Unit -> Int\nmain () = 42\n"
    ));
    let failure = run_path(fixture.configuration()).unwrap_err();
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error))
        if error.reason == ResolveReason::ForeignContract && error.related.len() == 1),
        "{failure:?}"
    );
}
