//! The byte/address boundary uses ordinary values and source effect handlers.
use ash::{
    driver::{EntryReason, PipelineFailure, RunConfiguration, compile_path, execute, run_path},
    eval::RuntimeFailure,
    module::ModuleRoots,
    resolve::ResolveReason,
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new(source: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let directory = std::env::temp_dir().join(format!(
            "ash-slim-ffi-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("entry.ash"), source).unwrap();
        Self(directory)
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
fn address_is_an_opaque_ordinary_captured_value() {
    let fixture = Fixture::new(
        r"import @builtin.foreign as F
keep : F.Address -> (Unit -> F.Address)
keep address = fn(ignored) {
    address
}
main : Unit -> Bool
main () = F.equal ((keep (F.null ())) (), F.null ())
",
    );
    let observation = run_path(fixture.configuration()).unwrap();
    assert_eq!(observation.value_display(), "true");
}

#[test]
fn foreign_symbol_effect_can_be_handled_by_ordinary_source() {
    let fixture = Fixture::new(
        r#"import @builtin.foreign as F
pub foreign library Test {
    profile "x86_64-unknown-linux-gnu"
    symbol Make : Unit -> F.Address { name "absent_native_symbol" }
}
main : Unit -> Bool
main () = F.is_null (handle (perform Make.call ()) with Make {
    call ignored => resume (F.null ())
})
"#,
    );
    let observation = run_path(fixture.configuration()).unwrap();
    assert_eq!(observation.value_display(), "true");
}

#[test]
fn passive_import_accepts_supported_pointer_and_void_signatures() {
    let fixture = Fixture::new(
        r"import @builtin.foreign as F
import native as Native
probe : F.Address -> Unit ! {Native.Release}
probe address = perform Native.Release.call address
main : Unit -> Int
main () = 42
",
    );
    fs::write(
        fixture.0.join("native.ash"),
        r#"import @builtin.foreign as F
pub foreign library Test {
    profile "x86_64-unknown-linux-gnu"
    symbol Make : Unit -> F.Address { name "absent_make" }
    symbol Stop : Unit -> Unit { name "absent_stop" }
    symbol Echo : F.Address -> F.Address { name "absent_echo" }
    symbol EchoBytes : Bytes -> F.Address { name "absent_echo_bytes" }
    symbol Release : F.Address -> Unit { name "absent_release" }
    symbol Consume : Bytes -> Unit { name "absent_consume" }
    symbol Pair : (F.Address, F.Address) -> F.Address { name "absent_pair" }
    symbol Mixed : (F.Address, Bytes) -> Unit { name "absent_mixed" }
    symbol Triple : (Bytes, F.Address, Bytes) -> F.Address { name "absent_triple" }
}
"#,
    )
    .unwrap();
    compile_path(fixture.configuration())
        .expect("passive imports admit supported pointer/void signatures without linking");
}

#[test]
fn unit_returning_foreign_symbol_keeps_its_ordinary_source_effect() {
    let fixture = Fixture::new(
        r#"import @builtin.foreign as F
pub foreign library Test {
    profile "x86_64-unknown-linux-gnu"
    symbol Release : F.Address -> Unit { name "absent_native_symbol" }
}
main : Unit -> Unit
main () = handle (perform Release.call (F.null ())) with Release {
    call address => resume ()
}
"#,
    );
    let observation = run_path(fixture.configuration())
        .expect("an ordinary source handler implements a void-returning foreign operation");
    assert_eq!(observation.value_display(), "()");
}

#[test]
fn unsupported_signature_shapes_have_the_foreign_signature_diagnostic() {
    for (case, signature) in [
        ("numeric result", "Unit -> Int"),
        ("numeric argument", "Int -> F.Address"),
        ("Bytes result", "Unit -> Bytes"),
        ("Unit tuple component", "(F.Address, Unit) -> Unit"),
        ("nested tuple", "((F.Address, Bytes), F.Address) -> Unit"),
        ("callback argument", "(F.Address -> Unit) -> Unit"),
        ("function result", "Unit -> (F.Address -> Unit)"),
    ] {
        let fixture = Fixture::new(&format!(
            r#"import @builtin.foreign as F
pub foreign library Test {{
    profile "x86_64-unknown-linux-gnu"
    symbol Unsupported : {signature} {{ name "absent_native_symbol" }}
}}
main : Unit -> Int
main () = 0
"#
        ));
        let failure = compile_path(fixture.configuration())
            .expect_err("unsupported shapes fail even when the symbol is unused");
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("{case} should reach foreign signature admission: {failure:?}");
        };
        assert_eq!(error.reason, ResolveReason::ForeignContract, "{case}");
        assert_eq!(
            error.diagnostic().primary.message(),
            "unsupported or inconsistent foreign signature: InvalidSignature",
            "{case}",
        );
    }
}

#[test]
fn unbound_address_and_void_calls_require_native_bindings() {
    for (signature, result, invocation) in [
        ("Unit -> F.Address", "F.Address", "perform Invoke.call ()"),
        (
            "F.Address -> Unit",
            "Unit",
            "perform Invoke.call (F.null ())",
        ),
    ] {
        let fixture = Fixture::new(&format!(
            r#"import @builtin.foreign as F
pub foreign library Test {{
    profile "x86_64-unknown-linux-gnu"
    symbol Invoke : {signature} {{ name "absent_native_symbol" }}
}}
main : Unit -> {result} ! {{Invoke}}
main () = {invocation}
"#
        ));
        let compiled = compile_path(fixture.configuration())
            .expect("the ordinary foreign effect is admitted before native bindings are supplied");
        let failure =
            execute(&compiled).expect_err("default execution supplies no native symbol bindings");
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::Runtime(RuntimeFailure::ForeignBinding))
            ),
            "{signature}: {failure:?}",
        );
    }
}

#[test]
fn native_entry_does_not_discharge_an_ordinary_effect() {
    let fixture = Fixture::new(
        r#"import @builtin.foreign as F
pub foreign library Test {
    profile "x86_64-unknown-linux-gnu"
    symbol Stop : Unit -> Unit { name "absent_native_symbol" }
}
effect Ask {
    ask : Unit -> Unit
}
main : Unit -> Unit ! {Stop, Ask}
main () = {
    let ignored = perform Ask.ask ()
    perform Stop.call ()
}
"#,
    );
    let failure = compile_path(fixture.configuration())
        .expect_err("native symbols discharge only their own effects");
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Entry(error)) if error.reason() == EntryReason::MainEffects),
        "{failure:?}",
    );
}
