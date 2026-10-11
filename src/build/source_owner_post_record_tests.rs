//! Injected owner continuation-work witnesses, separate from real C evidence.

use super::{
    __private_native_owner_acquire_bridge, __private_native_owner_teardown_bridge,
    __run_private_effect_image, NATIVE_TARGET, PrivateFailure, PrivateNativeBridge,
    PrivateNativeCoordinates, PrivateNativeLibrary, PrivateNativeMember, PrivateProgramFailure,
    bridge, image, runtime_fingerprint,
};
use crate::{
    driver::{RunConfiguration, compile_path},
    eval::{RuntimeFailure, source_owner_post_record_test},
    foreign::source_runtime::{
        NativeOwnerCallReturned, NativeOwnerGuardReady, NativeScalarCallError, NativeScalarValue,
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
    perform Owner.ProbeOps<Fresh>.read ()
}
"#;
#[test]
fn injected_owner_post_record_refusal_destroys_once_and_fresh_activation_does_not_replay() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("owner.ash"),
        include_str!("../../tests/fixtures/source-owner/owner.ash"),
    )
    .unwrap();
    let entry = fixture.0.join("entry.ash");
    fs::write(&entry, ENTRY).unwrap();
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
    assert_eq!(build.bridges.len(), 2);
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
    ACQUIRES.set(0);
    RELEASES.set(0);
    struct Providers;
    impl Drop for Providers {
        fn drop(&mut self) {
            PROVIDERS.set(None);
        }
    }
    let providers = Providers;
    let members = [
        PrivateNativeMember {
            coordinates: coordinates[0],
            provider: acquire_provider,
        },
        PrivateNativeMember {
            coordinates: coordinates[1],
            provider: teardown_provider,
        },
    ];
    let libraries = [PrivateNativeLibrary {
        image_library: coordinates[0].image_library,
        module: coordinates[0].library_module,
        ordinal: coordinates[0].library_ordinal,
        members: &members,
    }];
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
