//! Injected owner continuation-work witnesses, separate from real C evidence.

use super::{
    __private_native_bridge, __private_native_owner_acquire_bridge,
    __private_native_owner_teardown_bridge, __run_private_effect_image, NATIVE_TARGET,
    PrivateFailure, PrivateNativeBridge, PrivateNativeCoordinates, PrivateNativeLibrary,
    PrivateNativeMember, PrivateProgramFailure, bridge, image, runtime_fingerprint,
};
use crate::{
    driver::{RunConfiguration, compile_path},
    eval::{RuntimeFailure, source_owner_post_record_test},
    foreign::source_runtime::{
        NativeOwnerCallReturned, NativeOwnerGuardReady, NativeScalarCallError, NativeScalarReply,
        NativeScalarValue,
    },
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
    static PROVIDERS:Cell<Option<([PrivateNativeCoordinates;2], &'static [u8])>>=const { Cell::new(None) };
    static NEGATIVE_PROVIDER:Cell<Option<(PrivateNativeCoordinates, &'static [u8])>>=const { Cell::new(None) };
    static ACQUIRES:Cell<usize>=const {Cell::new(0)};
    static RELEASES:Cell<usize>=const {Cell::new(0)};
}
fn injected_acquire(
    arguments: &[NativeScalarValue],
    readiness: NativeOwnerGuardReady,
) -> Result<NativeOwnerCallReturned, NativeScalarCallError> {
    let [NativeScalarValue::USize(42)] = arguments else {
        return Err(NativeScalarCallError::ArgumentContract);
    };
    ACQUIRES.set(ACQUIRES.get() + 1);
    // No native allocation/dereference: a safe opaque sentinel models only the
    // exact ownership edge and counted destructor behind the sealed test gate.
    Ok(readiness.returned(std::ptr::NonNull::<u8>::dangling().as_ptr().cast()))
}
fn injected_release(address: *mut core::ffi::c_void) {
    assert!(!address.is_null());
    RELEASES.set(RELEASES.get() + 1);
}
fn acquire_provider() -> PrivateNativeBridge {
    let (coordinates, facts) = PROVIDERS.get().expect("emitter-selected owner facts");
    __private_native_owner_acquire_bridge(coordinates[0], facts, injected_acquire)
}
fn teardown_provider() -> PrivateNativeBridge {
    let (coordinates, facts) = PROVIDERS.get().expect("emitter-selected owner facts");
    __private_native_owner_teardown_bridge(coordinates[1], facts, injected_release)
}
fn injected_negative(
    arguments: &[NativeScalarValue],
) -> Result<NativeScalarReply, NativeScalarCallError> {
    if !arguments.is_empty() {
        return Err(NativeScalarCallError::ArgumentContract);
    }
    Ok(NativeScalarReply::Scalar(NativeScalarValue::I64(-1)))
}
fn negative_provider() -> PrivateNativeBridge {
    let (coordinates, facts) = NEGATIVE_PROVIDER
        .get()
        .expect("emitter-selected scalar facts");
    __private_native_bridge(coordinates, facts, injected_negative)
}
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-owner-post-record-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
const ENTRY: &str = r#"import owner as Owner
main : Unit -> Owner.Scope<Unit, Unit, Int>
main () = resource Owner.Probe<{}, Fresh, {}> owner = 42 {
    Owner.read owner
}
"#;
#[test]
fn injected_owner_post_record_refusal_destroys_once_and_fresh_activation_does_not_replay() {
    owner_post_record_case(
        include_str!("../../tests/fixtures/source-owner/owner.ash"),
        None,
        ExtentOutcome::Ready,
    );
}

fn byte_owner_source(extent: &str) -> String {
    include_str!("../../tests/fixtures/source-owner/owner.ash")
        .replace("repr Address = opaque", "repr Address = bytes")
        .replace(
            ": Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
            ": (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>>",
        )
        .replace(
            "outcome result nonnull { readable result }",
            "outcome result nonnull { readable result, initialized_bytes result from 1 }",
        )
        .replace(".call size {", &format!(".call (size, ({extent})) {{"))
}

#[test]
fn initialized_byte_owner_records_unmapped_source_extent_before_post_return_failure() {
    // The ABI operand and private data are 42, while the independently selected
    // source leaf promises seven initialized bytes. No native memory is read.
    owner_post_record_case(&byte_owner_source("7"), Some(7), ExtentOutcome::Ready);
}

#[test]
fn zero_initialized_extent_keeps_a_nonnull_owner_and_its_destruction_obligation() {
    owner_post_record_case(&byte_owner_source("0"), Some(0), ExtentOutcome::Ready);
}

#[test]
fn initialized_byte_extent_refusal_precedes_acquisition_and_creates_no_owner() {
    owner_post_record_case(
        &byte_owner_source("(9223372036854775807 + 1) * 2"),
        None,
        ExtentOutcome::ConversionRefused,
    );
    let owner = byte_owner_source("extent")
        .replace("input Int", "input (Int, Int)")
        .replace("acquire size =>", "acquire (size, extent) =>")
        .replace(
            "    repr Size = size_t",
            r#"    repr Size = size_t
    repr Signed = signed(64)
    symbol NegativeInput : Unit -> Foreign.Call<Int> {
        name "ash_owner_negative_input"
        abi () -> Signed
        output result as scalar
        outcome otherwise { readable result }
    }"#,
        );
    let entry = r#"import @builtin.foreign as Foreign
import owner as Owner
main : Unit -> Owner.Scope<Unit, Unit, Int> ! {Owner.NegativeInput}
main () = {
    let extent = match perform Owner.NegativeInput.call () {
        Foreign.Returned(value) => value
        Foreign.ConversionFailed(_) => 0
    }
    resource Owner.Probe<{}, Fresh, {}> owner = (42, extent) {
        Owner.read owner
    }
}
"#;
    owner_post_record_case_with_entry(&owner, entry, None, ExtentOutcome::ConversionRefused);
}

#[derive(Clone, Copy)]
enum ExtentOutcome {
    Ready,
    ConversionRefused,
    WorkRefused,
}

#[test]
fn initialized_byte_extent_work_refusal_precedes_acquisition_and_creates_no_owner() {
    owner_post_record_case(&byte_owner_source("7"), Some(7), ExtentOutcome::WorkRefused);
}

fn owner_post_record_case(owner: &str, initialized_bytes: Option<usize>, outcome: ExtentOutcome) {
    owner_post_record_case_with_entry(owner, ENTRY, initialized_bytes, outcome);
}

fn owner_post_record_case_with_entry(
    owner: &str,
    entry_source: &str,
    initialized_bytes: Option<usize>,
    outcome: ExtentOutcome,
) {
    let fixture = Fixture::new();
    fs::write(fixture.0.join("owner.ash"), owner).unwrap();
    let entry = fixture.0.join("entry.ash");
    fs::write(&entry, entry_source).unwrap();
    let compiled = compile_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .unwrap();
    let compilation_work = *compiled.compilation_work();
    let (program, provenance) = compiled.effect_build_input().unwrap();
    let mut work = TypeWorkBudget::default();
    let build =
        image::encode_effect_for_build(program, provenance, NATIVE_TARGET, &mut work).unwrap();
    assert_eq!(build.libraries.len(), 1);
    let negative = entry_source != ENTRY;
    assert_eq!(build.bridges.len(), if negative { 3 } else { 2 });
    let library = &build.libraries[0];
    let coordinates = [
        bridge::TargetBridgeCall::OwnerAcquire,
        bridge::TargetBridgeCall::OwnerTeardown,
    ]
    .map(|role| {
        let bridge = build
            .bridges
            .iter()
            .find(|bridge| bridge.plan.call() == role)
            .unwrap();
        PrivateNativeCoordinates {
            image_library: library.image_library,
            library_module: library.module,
            library_ordinal: library.ordinal,
            image_symbol: bridge.image_symbol,
            symbol_index: bridge.symbol_index,
            operation_module: bridge.operation_module,
            operation_effect: bridge.operation_effect,
            operation_local: bridge.operation_local,
        }
    });
    let negative_coordinates = negative.then(|| {
        let bridge = build
            .bridges
            .iter()
            .find(|bridge| bridge.plan.call() == bridge::TargetBridgeCall::Scalar)
            .unwrap();
        PrivateNativeCoordinates {
            image_library: library.image_library,
            library_module: library.module,
            library_ordinal: library.ordinal,
            image_symbol: bridge.image_symbol,
            symbol_index: bridge.symbol_index,
            operation_module: bridge.operation_module,
            operation_effect: bridge.operation_effect,
            operation_local: bridge.operation_local,
        }
    });
    let bytes = build.image.encode_bytes(&mut work).unwrap();
    // Models the generated static original EXPECTED_FACTS allocation. It holds
    // passive bytes, with no resource owner or executable Core capability.
    let facts: &'static [u8] = Box::leak(
        build
            .image
            .encode_native_expectations(&mut work)
            .unwrap()
            .into_boxed_slice(),
    );
    assert_eq!(*compiled.compilation_work(), compilation_work);
    fs::remove_file(entry).unwrap();
    fs::remove_file(fixture.0.join("owner.ash")).unwrap();
    drop(build);
    drop(compiled);
    assert!(PROVIDERS.get().is_none());
    PROVIDERS.set(Some((coordinates, facts)));
    NEGATIVE_PROVIDER.set(negative_coordinates.map(|coordinates| (coordinates, facts)));
    ACQUIRES.set(0);
    RELEASES.set(0);
    struct Providers;
    impl Drop for Providers {
        fn drop(&mut self) {
            PROVIDERS.set(None);
            NEGATIVE_PROVIDER.set(None);
        }
    }
    let providers = Providers;
    let mut members = vec![
        PrivateNativeMember {
            coordinates: coordinates[0],
            provider: acquire_provider,
        },
        PrivateNativeMember {
            coordinates: coordinates[1],
            provider: teardown_provider,
        },
    ];
    if let Some(coordinates) = negative_coordinates {
        members.push(PrivateNativeMember {
            coordinates,
            provider: negative_provider,
        });
    }
    let libraries = [PrivateNativeLibrary {
        image_library: coordinates[0].image_library,
        module: coordinates[0].library_module,
        ordinal: coordinates[0].library_ordinal,
        members: &members,
    }];
    if matches!(outcome, ExtentOutcome::ConversionRefused) {
        let (refused, observed) = source_owner_post_record_test::observe(false, || {
            __run_private_effect_image(&runtime_fingerprint(), &bytes, facts, &libraries)
        });
        assert_eq!(refused.unwrap().to_string(), "NotAcquired(())");
        assert_eq!(observed.returned, 0);
        assert_eq!(observed.recorded, 0);
        assert_eq!(ACQUIRES.get(), 0);
        assert_eq!(RELEASES.get(), 0);
        drop(providers);
        return;
    }
    if matches!(outcome, ExtentOutcome::WorkRefused) {
        let (refused, observed) = source_owner_post_record_test::observe_extent_preflight(|| {
            __run_private_effect_image(&runtime_fingerprint(), &bytes, facts, &libraries)
        });
        let Err(PrivateProgramFailure(PrivateFailure::Evaluation(RuntimeFailure::Report(report)))) =
            refused
        else {
            panic!("expected work refusal before initialized extent admission; got {refused:?}");
        };
        assert_eq!(report.primary.reason_code(), "runtime.environment-capacity");
        let resource = report.primary.resource().unwrap();
        assert_eq!(
            resource.cause,
            crate::eval::ResourceFailureCause::WorkBudgetExhausted
        );
        assert_eq!(resource.resource, crate::eval::RuntimeResource::WorkUnits);
        assert_eq!(resource.available, Some(0));
        assert_eq!(observed.returned, 0);
        assert_eq!(observed.recorded, 0);
        assert_eq!(ACQUIRES.get(), 0);
        assert_eq!(RELEASES.get(), 0);
        // A fresh activation has a fresh ledger and cannot replay the refused call.
        let (fresh, _) = source_owner_post_record_test::observe(false, || {
            __run_private_effect_image(&runtime_fingerprint(), &bytes, facts, &libraries)
        });
        assert_eq!(fresh.unwrap().to_string(), "Completed(42, Closed)");
        assert_eq!(ACQUIRES.get(), 1);
        assert_eq!(RELEASES.get(), 1);
        drop(providers);
        return;
    }
    // Each evaluation restores the same original templates, validates final
    // copied Core, seals exact native members and admits the entire program.
    // Injection exhausts only the Machine ledger after its selected native return.
    let (refused, observed) = source_owner_post_record_test::observe(true, || {
        __run_private_effect_image(&runtime_fingerprint(), &bytes, facts, &libraries)
    });
    let Err(PrivateProgramFailure(PrivateFailure::Evaluation(RuntimeFailure::Report(report)))) =
        refused
    else {
        panic!(
            "expected ordinary work refusal after guarded owner recording; got {refused:?}, observation {observed:?}"
        );
    };
    assert_eq!(
        report.primary.reason_code(),
        "runtime.work-budget-exhausted"
    );
    let resource = report.primary.resource().unwrap();
    assert_eq!(resource.resource, crate::eval::RuntimeResource::WorkUnits);
    assert_eq!(resource.available, Some(0));
    assert_eq!(observed.returned, 1);
    assert_eq!(observed.recorded, 1);
    assert!(observed.recorded_with_zero_shared_work);
    assert!(observed.recorded_live_owner);
    assert_eq!(observed.initialized_bytes, initialized_bytes);
    assert_eq!(
        observed.reported, 1,
        "prepaid report follows infallible guarded recording"
    );
    assert!(observed.report_slot_published);
    assert_eq!(
        ACQUIRES.get(),
        1,
        "terminal disposal cannot replay acquisition"
    );
    assert_eq!(
        RELEASES.get(),
        1,
        "terminal disposal destroys the unique live owner once"
    );
    let (fresh, observed) = source_owner_post_record_test::observe(false, || {
        __run_private_effect_image(&runtime_fingerprint(), &bytes, facts, &libraries)
    });
    assert_eq!(fresh.unwrap().to_string(), "Completed(42, Closed)");
    assert_eq!(observed.returned, 1);
    assert_eq!(observed.recorded, 1);
    assert_eq!(observed.reported, 1);
    assert!(observed.recorded_live_owner);
    assert_eq!(observed.initialized_bytes, initialized_bytes);
    assert_eq!(
        ACQUIRES.get(),
        2,
        "one acquisition for each fresh admitted activation"
    );
    assert_eq!(
        RELEASES.get(),
        2,
        "fresh finish consumes once; Drop cannot repeat its destructor"
    );
    // Reuse the same image and providers. This refusal occurs after the native
    // destructor returned, rather than after acquisition or before teardown.
    let (refused, observed) = source_owner_post_record_test::observe_teardown(true, || {
        __run_private_effect_image(&runtime_fingerprint(), &bytes, facts, &libraries)
    });
    let Err(PrivateProgramFailure(PrivateFailure::Evaluation(RuntimeFailure::Report(report)))) =
        refused
    else {
        panic!(
            "expected ordinary work refusal after recorded native consumption; got {refused:?}, observation {observed:?}"
        );
    };
    assert_eq!(
        report.primary.reason_code(),
        "runtime.work-budget-exhausted"
    );
    let resource = report.primary.resource().unwrap();
    assert_eq!(resource.resource, crate::eval::RuntimeResource::WorkUnits);
    assert_eq!(resource.available, Some(0));
    assert_eq!(observed.returned, 1);
    assert_eq!(observed.recorded, 1);
    assert_eq!(observed.reported, 1);
    assert_eq!(observed.teardown_returned, 1);
    assert_eq!(observed.teardown_recorded, 1);
    assert!(observed.teardown_recorded_with_zero_shared_work);
    assert_eq!(
        observed.teardown_reported, 1,
        "consumed reporting uses prepaid storage"
    );
    assert!(observed.teardown_consumed_report_published);
    assert_eq!(ACQUIRES.get(), 3, "teardown refusal cannot reacquire");
    assert_eq!(
        RELEASES.get(),
        3,
        "terminal disposal cannot repeat consumed teardown"
    );

    let (fresh, observed) = source_owner_post_record_test::observe_teardown(false, || {
        __run_private_effect_image(&runtime_fingerprint(), &bytes, facts, &libraries)
    });
    assert_eq!(fresh.unwrap().to_string(), "Completed(42, Closed)");
    assert_eq!(observed.teardown_returned, 1);
    assert_eq!(observed.teardown_recorded, 1);
    assert_eq!(observed.teardown_reported, 1);
    assert!(observed.teardown_consumed_report_published);
    assert_eq!(
        ACQUIRES.get(),
        4,
        "fresh evaluation owns its own acquisition"
    );
    assert_eq!(RELEASES.get(), 4, "fresh activation consumes exactly once");
    drop(providers);
}
