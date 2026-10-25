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

const CONTRACT: &str = r#"import @builtin.foreign as F
pub foreign library C {
    profile "x86_64-unknown-linux-gnu"
    symbol Echo : F.Address -> F.Address { name "absent_echo" }
    symbol Stop : Unit -> Unit { name "absent_stop" }
    symbol Inspect : Bytes -> F.Address { name "absent_inspect" }
}
"#;

#[test]
fn source_native_declarations_and_imports_are_passive() {
    for imported in [false, true] {
        let entry = if imported {
            "import native as Native\nmain : Unit -> Int\nmain () = 42\n".to_owned()
        } else {
            format!("{CONTRACT}main : Unit -> Int\nmain () = 42\n")
        };
        let fixture = Fixture::new(&entry);
        if imported {
            fs::write(fixture.0.join("native.ash"), CONTRACT).unwrap();
        }
        assert_eq!(
            run_path(fixture.configuration()).unwrap().value_display(),
            "42"
        );
    }
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
            "import facade as Facade\nimport native as Native\nprobe : Unit -> Unit ! {Facade.Halt}\nprobe () = ()\nmain : Unit -> Int\nmain () = 42\n",
            Some("pub import native (Stop as Halt)\n"),
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
fn selected_and_reexported_operations_keep_the_defining_handler_identity() {
    for through_facade in [false, true] {
        let selected = if through_facade { "facade" } else { "native" };
        let fixture = Fixture::new(&format!(
            r"import @builtin.foreign as F
import native as Native
import {selected} (Echo as Forward)
main : Unit -> Bool
main () = F.is_null (handle (perform Forward.call (F.null ())) with Native.Echo {{
    call address => resume address
}})
"
        ));
        fs::write(fixture.0.join("native.ash"), CONTRACT).unwrap();
        if through_facade {
            fs::write(fixture.0.join("facade.ash"), "pub import native (Echo)\n").unwrap();
        }
        assert_eq!(
            run_path(fixture.configuration())
                .expect("the defining effect handles the renamed operation")
                .value_display(),
            "true"
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
        let failure = run_path(fixture.configuration()).unwrap_err();
        assert!(
            matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error)) if error.reason == ResolveReason::UnavailableExport),
            "{failure:?}"
        );
    }
}

#[test]
fn same_named_address_type_has_no_builtin_pointer_mapping() {
    let fixture = Fixture::new(&format!(
        "{}main : Unit -> Int\nmain () = 42\n",
        CONTRACT.replace("import @builtin.foreign as F", "import donor as F")
    ));
    fs::write(
        fixture.0.join("donor.ash"),
        "pub opaque type Address = Hidden\n",
    )
    .unwrap();
    let failure = run_path(fixture.configuration()).unwrap_err();
    let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
        panic!("foreign signature admission must reject the ordinary nominal: {failure:?}")
    };
    assert_eq!(error.reason, ResolveReason::ForeignContract);
    assert_eq!(
        error.diagnostic().primary.message(),
        "unsupported or inconsistent foreign signature: InvalidSignature"
    );
}

#[test]
fn foreign_and_ordinary_effect_names_share_the_collision_boundary() {
    let fixture = Fixture::new(&format!(
        "{CONTRACT}effect Echo {{\n    call : Unit -> Unit\n}}\nmain : Unit -> Int\nmain () = 42\n"
    ));
    let failure = run_path(fixture.configuration()).unwrap_err();
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error)) if error.reason == ResolveReason::DuplicateEffect),
        "{failure:?}"
    );
}

#[test]
fn foreign_libraries_require_disjoint_symbol_spellings() {
    let fixture = Fixture::new(&format!(
        r#"{CONTRACT}foreign library Other {{
    profile "x86_64-unknown-linux-gnu"
    symbol Stop : Unit -> Unit {{ name "absent_other_stop" }}
}}
main : Unit -> Int
main () = 42
"#
    ));
    let failure = run_path(fixture.configuration()).unwrap_err();
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error)) if error.reason == ResolveReason::DuplicateEffect),
        "{failure:?}"
    );
}

#[test]
fn interleaved_foreign_libraries_and_ordinary_effects_preserve_source_declaration_order() {
    let fixture = Fixture::new(
        r#"import @builtin.foreign as F
pub effect Before<T> {
    request : T -> T
}
pub foreign library First {
    profile "x86_64-unknown-linux-gnu"
    symbol FirstStop : Unit -> Unit { name "absent_first_stop" }
    symbol NextStop : F.Address -> Unit { name "absent_next_stop" }
}
pub effect Between<T> {
    request : T -> T
}
pub foreign library Second {
    profile "x86_64-unknown-linux-gnu"
    symbol LastStop : Bytes -> F.Address { name "absent_last_stop" }
}
pub effect After {
    request : Unit -> Unit
}
probe : Unit -> Unit ! {Before<Int>, FirstStop, NextStop, Between<Bool>, LastStop, After}
probe () = ()
main : Unit -> Int
main () = 42
"#,
    );
    assert_eq!(
        run_path(fixture.configuration()).unwrap().value_display(),
        "42",
        "passive declarations survive independent linked validation in source order"
    );
}
