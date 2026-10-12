//! Public source admission evidence; unused contracts supply no activation.

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new(source: &str) -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-owner-admission-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("entry.ash"), source).unwrap();
        Self(path)
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

const SOURCE: &str = r#"import @builtin.foreign as Foreign
pub foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = opaque
    owner State<T, R> {
        representation Address
        owned R
        teardown Free
    }
    symbol Allocate<Before : EffectRow, R, T, After : EffectRow> : Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<T, R>>>> {
        name "malloc"
        abi (Size) -> pointer(Address)
        operand 0 from 0 scalar
        output result as owner(State<T, R>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol Free<T, Before : EffectRow, R, After : EffectRow> : (Int, State<T, R>) -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Address)) -> void
        operand 0 from 1 current
        retained_dependents block
        outcome otherwise { consumed 1 }
    }
}
main : Unit -> Int
main () = 42
"#;

#[test]
fn type_only_source_owner_admission_keeps_mixed_symbol_vectors_and_nonfirst_owned_slot() {
    let fixture = Fixture::new(SOURCE);
    let compiled =
        compile_path(fixture.configuration()).expect("owner contracts have defining authority");
    let result = execute(&compiled).expect("unused owner contracts do not require acquisition");
    assert_eq!(result.value_display(), "42");
}

#[test]
fn source_byte_owner_admission_checks_initialized_extent_against_source_signature() {
    let source = SOURCE
        .replace("repr Address = opaque", "repr Address = bytes")
        .replace(" : Int ->", " : (Int, Int) ->")
        .replace(
            "outcome result nonnull { readable result }",
            "outcome result nonnull { readable result, initialized_bytes result from 1 }",
        );
    let fixture = Fixture::new(&source);
    assert!(compile_path(fixture.configuration()).is_ok());
    // An unchanged prepared source path must not authenticate a Bool extent.
    let source = source.replace(" : (Int, Int) ->", " : (Int, Bool) ->");
    let fixture = Fixture::new(&source);
    assert!(compile_path(fixture.configuration()).is_err());
}

#[test]
fn source_owner_result_shape_and_current_state_are_reconstructed_from_original_roles() {
    for invalid in [
        SOURCE.replace(
            "Foreign.Output<Foreign.Nullable<State<T, R>>>",
            "State<T, R>",
        ),
        SOURCE.replace("(Int, State<T, R>) ->", "(Int, Int) ->"),
        SOURCE.replace("Foreign.Disposition<Unit>", "Unit"),
        SOURCE.replace(
            "Foreign.Nullable<State<T, R>>",
            "Foreign.Nullable<State<R, T>>",
        ),
    ] {
        let fixture = Fixture::new(&invalid);
        assert!(compile_path(fixture.configuration()).is_err(), "{invalid}");
    }
}

#[test]
fn passive_owner_preparation_does_not_allow_ordinary_acquisition_calls() {
    let source = SOURCE.replace("main : Unit -> Int\nmain () = 42",
        "main : Unit -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<Int, Int>>>> ! {Allocate<{}, Int, Int, {}>}\nmain () = perform Allocate<{}, Int, Int, {}>.call 8");
    let fixture = Fixture::new(&source);
    assert!(compile_path(fixture.configuration()).is_err());
}

#[test]
fn row_bearing_owner_families_remain_an_explicit_canonical_admission_refusal() {
    let source = SOURCE
        .replace("owner State<T, R>", "owner State<T : EffectRow, R>")
        .replace("State<T, R>", "State<{| T}, R>")
        .replace(" R, T, After", " R, T : EffectRow, After")
        .replace("symbol Free<T,", "symbol Free<T : EffectRow,");
    let fixture = Fixture::new(&source);
    assert!(compile_path(fixture.configuration()).is_err());
}
