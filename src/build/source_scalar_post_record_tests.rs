//! One injected Machine continuation-work witness, separate from real C evidence.

use super::*;
use crate::{
    driver::{RunConfiguration, compile_path},
    eval::{RuntimeFailure, source_scalar_post_record_test},
    foreign::source_runtime::{NativeScalarCallError, NativeScalarReply, NativeScalarValue},
    module::ModuleRoots,
    types::TypeWorkBudget,
};
use std::{
    cell::Cell,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

thread_local! {
    static PROVIDER: Cell<Option<(PrivateNativeCoordinates, &'static [u8])>> = const { Cell::new(None) };
    static RUST_CALLBACK_CALLS: Cell<usize> = const { Cell::new(0) };
}

fn typed_rust_test_callback(
    arguments: &[NativeScalarValue],
) -> Result<NativeScalarReply, NativeScalarCallError> {
    let [NativeScalarValue::I8(value)] = arguments else {
        return Err(NativeScalarCallError::ArgumentContract);
    };
    RUST_CALLBACK_CALLS.set(RUST_CALLBACK_CALLS.get() + 1);
    Ok(NativeScalarReply::Scalar(NativeScalarValue::I8(*value)))
}

fn original_test_provider() -> PrivateNativeBridge {
    let (coordinates, facts) = PROVIDER
        .get()
        .expect("emitter-selected passive fixture facts");
    __private_native_bridge(coordinates, facts, typed_rust_test_callback)
}

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        loop {
            let id = IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-scalar-post-record-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("scalar boundary fixture: {error}"),
            }
        }
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const SOURCE: &str = r#"import @builtin.foreign as Foreign
foreign library Counter {
    profile "x86_64-unknown-linux-gnu"
    repr I8 = signed(8)
    symbol Echo<Before : EffectRow, T, After : EffectRow> : Int -> Foreign.Call<Int> {
        name "ash_counter_machine_echo_i8"
        abi (I8) -> I8
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
main : Unit -> Int ! {Echo<{}, Int, {}>}
main () = match perform Echo<{}, Int, {}>.call 41 {
    Foreign.Returned(value) => {
        let ignored = "ordinary continuation"
        value + 1
    }
    Foreign.ConversionFailed(error) => 900
}
"#;

#[test]
fn injected_post_record_continuation_refusal_does_not_replay_and_fresh_activation_calls_once() {
    let fixture = Fixture::new();
    let entry = fixture.0.join("entry.ash");
    fs::write(&entry, SOURCE).unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("ordinary source/contracts and mandatory interpreter must compile");
    let compilation_work = *compiled.compilation_work();
    let (program, provenance) = compiled.effect_build_input().unwrap();
    let mut preparation = TypeWorkBudget::default();
    let image =
        image::encode_effect_for_build(program, provenance, NATIVE_TARGET, &mut preparation)
            .expect("same image/emitter selection as the actual native build path");
    assert_eq!(image.libraries.len(), 1);
    assert_eq!(image.bridges.len(), 1);
    let library = &image.libraries[0];
    assert_eq!(library.members.as_slice(), [0]);
    let bridge = &image.bridges[0];
    let coordinates = PrivateNativeCoordinates {
        image_library: library.image_library,
        library_module: library.module,
        library_ordinal: library.ordinal,
        image_symbol: bridge.image_symbol,
        symbol_index: bridge.symbol_index,
        operation_module: bridge.operation_module,
        operation_effect: bridge.operation_effect,
        operation_local: bridge.operation_local,
    };
    let bytes = image.image.encode_bytes(&mut preparation).unwrap();
    // Generated providers refer to a static EXPECTED_FACTS byte array. This one
    // small fixture payload deliberately lives for the test-process lifetime.
    let facts: &'static [u8] = Box::leak(
        image
            .image
            .encode_native_expectations(&mut preparation)
            .unwrap()
            .into_boxed_slice(),
    );
    assert_eq!(*compiled.compilation_work(), compilation_work);
    fs::remove_file(entry).unwrap();
    drop(image);
    drop(compiled);

    assert!(PROVIDER.get().is_none());
    PROVIDER.set(Some((coordinates, facts)));
    RUST_CALLBACK_CALLS.set(0);
    struct ProviderScope;
    impl Drop for ProviderScope {
        fn drop(&mut self) {
            PROVIDER.set(None);
        }
    }
    let scope = ProviderScope;
    let members = [PrivateNativeMember {
        coordinates,
        provider: original_test_provider,
    }];
    let libraries = [PrivateNativeLibrary {
        image_library: coordinates.image_library,
        module: coordinates.library_module,
        ordinal: coordinates.library_ordinal,
        members: &members,
    }];

    // Both runs use real decode/reconstruction, independent Effect validation,
    // whole-library normalized source comparison, sealed exact member admission,
    // table registration and program admission. There is no forged Core receipt
    // or manifest. The injection changes only the Machine ledger AFTER return.
    let (refused, observed) = source_scalar_post_record_test::observe(true, || {
        __run_private_effect_image(&runtime_fingerprint(), &bytes, facts, &libraries)
    });
    let Err(PrivateProgramFailure(PrivateFailure::Evaluation(RuntimeFailure::Report(report)))) =
        refused
    else {
        panic!("expected caught ordinary work refusal after native recording");
    };
    assert_eq!(
        report.primary.reason_code(),
        "runtime.work-budget-exhausted"
    );
    let resource = report.primary.resource().unwrap();
    assert_eq!(resource.phase, crate::eval::RuntimePhase::Evaluation);
    assert_eq!(resource.resource, crate::eval::RuntimeResource::WorkUnits);
    assert_eq!(resource.requested, Some("ordinary continuation".len()));
    assert_eq!(resource.available, Some(0));
    assert_eq!(
        RUST_CALLBACK_CALLS.get(),
        1,
        "one invocation before terminal refusal"
    );
    assert_eq!(observed.returned, 1);
    assert_eq!(
        observed.recorded, 1,
        "Returned must record before ordinary continuation refusal"
    );
    assert!(observed.recorded_with_zero_shared_work);
    assert_eq!(
        observed.reported, 1,
        "valid native report uses its prepaid allowance"
    );
    assert!(observed.report_slot_published);
    assert_eq!(
        RUST_CALLBACK_CALLS.get(),
        1,
        "disposal cannot replay the call"
    );

    let (fresh, fresh_observed) = source_scalar_post_record_test::observe(false, || {
        __run_private_effect_image(&runtime_fingerprint(), &bytes, facts, &libraries)
    });
    assert_eq!(fresh.unwrap().to_string(), "42");
    assert_eq!(fresh_observed.returned, 1);
    assert_eq!(fresh_observed.recorded, 1);
    assert_eq!(fresh_observed.reported, 1);
    assert_eq!(
        RUST_CALLBACK_CALLS.get(),
        2,
        "fresh activation invokes once again"
    );
    drop(scope);
}
