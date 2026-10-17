//! Connected startup admission evidence. Passive providers stand in for typed
//! emitted wrappers only to make invocation observable; all source/image/fact
//! data comes from canonical compilation and the actual private build encoder.

use std::{
    cell::Cell,
    fs,
    path::PathBuf,
    sync::{
        OnceLock,
        atomic::{AtomicU64, AtomicUsize, Ordering},
    },
};

use super::*;
use crate::{
    driver::{RunConfiguration, compile_path},
    foreign::source_runtime::{NativeScalarCallError, NativeScalarReply, NativeScalarValue},
    module::ModuleRoots,
    types::TypeWorkBudget,
};

const NATIVE: &str = r#"import @builtin.foreign as Foreign

pub foreign library Arithmetic {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    const Input : I32 = 40
    const Donor : I32 = 40
    symbol PlusOne : Unit -> Foreign.Call<Int> {
        name "ash_native_gate_plus_one"
        abi (I32) -> I32
        operand 0 from constant Input
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol PlusTwo : Int -> Foreign.Call<Int> {
        name "ash_native_gate_plus_two"
        abi (I32) -> I32
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
"#;
const ENTRY: &str = r#"import @builtin.foreign as Foreign
import native as Native

main : Unit -> Int ! {Native.PlusOne, Native.PlusTwo}
main () = match perform Native.PlusOne.call () {
    Foreign.Returned(first) => match perform Native.PlusTwo.call first {
        Foreign.Returned(second) => second
        Foreign.ConversionFailed(error) => 902
    }
    Foreign.ConversionFailed(error) => 901
}
"#;

struct Sources(PathBuf);
impl Sources {
    fn new() -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        loop {
            let id = IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-native-startup-gates-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("source fixture: {error}"),
            }
        }
    }
}
impl Drop for Sources {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct EmittedFixture {
    image: Vec<u8>,
    expected: &'static [u8],
    plus_one: PrivateNativeCoordinates,
    plus_two: PrivateNativeCoordinates,
}
static FIXTURE: OnceLock<EmittedFixture> = OnceLock::new();
// Image execution invokes these callbacks synchronously. Keep each parallel
// test's observations on its calling thread, independent of the shared fixture.
thread_local! {
    static CALLBACKS: Cell<usize> = const { Cell::new(0) };
}

fn emitted_fixture() -> &'static EmittedFixture {
    FIXTURE.get_or_init(|| {
        let sources = Sources::new();
        fs::write(sources.0.join("native.ash"), NATIVE).unwrap();
        fs::write(sources.0.join("entry.ash"), ENTRY).unwrap();
        let compiled = compile_path(RunConfiguration {
            entry: sources.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        let compilation_work = *compiled.compilation_work();
        // Canonical provenance is retained by compilation; image preparation
        // and every startup below must succeed/refuse without source reopening.
        fs::remove_file(sources.0.join("native.ash")).unwrap();
        fs::remove_file(sources.0.join("entry.ash")).unwrap();
        let (core, provenance) = compiled.effect_build_input().unwrap();
        let mut work = TypeWorkBudget::default();
        let build =
            image::encode_effect_for_build(core, provenance, NATIVE_TARGET, &mut work).unwrap();
        assert_eq!(*compiled.compilation_work(), compilation_work);
        assert_eq!(build.libraries.len(), 1);
        assert_eq!(build.bridges.len(), 2);
        let library = &build.libraries[0];
        assert_eq!(library.members.len(), 2);
        let select = |native_name: &str| {
            let bridge = build
                .bridges
                .iter()
                .find(|bridge| bridge.plan.symbol().symbol().native_name() == native_name)
                .unwrap();
            // The counterexample is not caught by operand/result tag checks:
            // these distinct original symbols deliberately have identical ABIs.
            assert_eq!(
                bridge.plan.operands(),
                &[bridge::TargetOperand::Scalar(bridge::TargetScalar::I32)]
            );
            assert_eq!(
                bridge.plan.result(),
                bridge::TargetResult::Scalar(bridge::TargetScalar::I32)
            );
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
        };
        let plus_one = select("ash_native_gate_plus_one");
        let plus_two = select("ash_native_gate_plus_two");
        assert_ne!(plus_one.image_symbol, plus_two.image_symbol);
        assert_ne!(plus_one.symbol_index, plus_two.symbol_index);
        assert_ne!(plus_one.operation_effect, plus_two.operation_effect);
        let image = build.image.encode_bytes(&mut work).unwrap();
        // One leaked immutable passive byte allocation models generated static
        // EXPECTED_FACTS. It holds no Core/type/resource owner and is shared by
        // the fixed provider bodies, never supplied as a provider argument.
        let expected: &'static [u8] = Box::leak(
            build
                .image
                .encode_native_expectations(&mut work)
                .unwrap()
                .into_boxed_slice(),
        );
        EmittedFixture {
            image,
            expected,
            plus_one,
            plus_two,
        }
    })
}

fn plus_one_callback(
    arguments: &[NativeScalarValue],
) -> Result<NativeScalarReply, NativeScalarCallError> {
    CALLBACKS.set(CALLBACKS.get() + 1);
    let [NativeScalarValue::I32(value)] = arguments else {
        return Err(NativeScalarCallError::ArgumentContract);
    };
    Ok(NativeScalarReply::Scalar(NativeScalarValue::I32(value + 1)))
}
fn plus_two_callback(
    arguments: &[NativeScalarValue],
) -> Result<NativeScalarReply, NativeScalarCallError> {
    CALLBACKS.set(CALLBACKS.get() + 1);
    let [NativeScalarValue::I32(value)] = arguments else {
        return Err(NativeScalarCallError::ArgumentContract);
    };
    Ok(NativeScalarReply::Scalar(NativeScalarValue::I32(value + 2)))
}

// Each zero-argument provider is fixed to its OWN original symbol and callback.
// There is no generic provider accepting a caller-selected identity to bless it.
fn plus_one_provider() -> PrivateNativeBridge {
    let emitted = emitted_fixture();
    __private_native_bridge(emitted.plus_one, emitted.expected, plus_one_callback)
}
fn wrong_owner_role_callback(
    _arguments: &[crate::foreign::source_runtime::NativeOwnerOperand],
    _readiness: crate::foreign::source_runtime::NativeOwnerGuardReady,
) -> Result<crate::foreign::source_runtime::NativeOwnerCallReturned, NativeScalarCallError> {
    CALLBACKS.set(CALLBACKS.get() + 1);
    Err(NativeScalarCallError::ArgumentContract)
}
fn wrong_owner_role_provider() -> PrivateNativeBridge {
    let emitted = emitted_fixture();
    __private_native_owner_acquire_bridge(
        emitted.plus_one,
        emitted.expected,
        wrong_owner_role_callback,
    )
}
fn plus_two_provider() -> PrivateNativeBridge {
    let emitted = emitted_fixture();
    __private_native_bridge(emitted.plus_two, emitted.expected, plus_two_callback)
}
fn members() -> [PrivateNativeMember; 2] {
    let emitted = emitted_fixture();
    [
        PrivateNativeMember {
            coordinates: emitted.plus_one,
            provider: plus_one_provider,
        },
        PrivateNativeMember {
            coordinates: emitted.plus_two,
            provider: plus_two_provider,
        },
    ]
}
fn run(
    expected: &'static [u8],
    members: &[PrivateNativeMember],
) -> Result<PrivateProgramOutput, PrivateProgramFailure> {
    let emitted = emitted_fixture();
    let library = PrivateNativeLibrary {
        image_library: emitted.plus_one.image_library,
        module: emitted.plus_one.library_module,
        ordinal: emitted.plus_one.library_ordinal,
        members,
    };
    __run_private_effect_image(&runtime_fingerprint(), &emitted.image, expected, &[library])
}

#[test]
fn native_image_startup_rejects_swapped_providers_stale_facts_and_missing_bindings_before_callbacks()
 {
    let emitted = emitted_fixture();
    let mut selected = members();
    CALLBACKS.set(0);
    assert_eq!(run(emitted.expected, &selected).unwrap().to_string(), "43");
    assert_eq!(CALLBACKS.get(), 2);

    // Keep ALL separately selected coordinates/original image/ABI facts intact;
    // swap only the providers, which continue to return their OWN expectations.
    let [first, second] = &mut selected;
    std::mem::swap(&mut first.provider, &mut second.provider);
    CALLBACKS.set(0);
    let error = run(emitted.expected, &selected).unwrap_err();
    assert!(
        matches!(
            &error.0,
            PrivateFailure::Image(image::ImageFailure::InvalidRecord)
        ),
        "wrong swapped-provider refusal: {error}"
    );
    assert_eq!(CALLBACKS.get(), 0);

    // Exact original coordinates and ABI facts cannot grant a different
    // generated callback role. This fails before readiness or native entry.
    let mut wrong_role = members();
    wrong_role[0].provider = wrong_owner_role_provider;
    CALLBACKS.set(0);
    let error = run(emitted.expected, &wrong_role).unwrap_err();
    assert!(
        matches!(
            &error.0,
            PrivateFailure::Evaluation(crate::eval::RuntimeFailure::ForeignBinding)
        ),
        "wrong callback-role refusal: {error}"
    );
    assert_eq!(CALLBACKS.get(), 0);

    // Alter a real native-name fact, not magic/framing, in the INDEPENDENT payload.
    // The executable IMAGE and original source graph remain untouched. Same-size
    // valid UTF-8 means this remains a decodable flat image; correspondence must
    // reject it before source/native callbacks, independently of wire validity.
    let mut altered = emitted.expected.to_vec();
    let native_name = b"ash_native_gate_plus_one";
    let start = altered
        .windows(native_name.len())
        .rposition(|bytes| bytes == native_name)
        .unwrap();
    altered[start + native_name.len() - 2] = b'x';
    let altered: &'static [u8] = Box::leak(altered.into_boxed_slice());
    image::PureImage::decode_bytes(altered, &mut TypeWorkBudget::default()).unwrap();
    let selected = members();
    CALLBACKS.set(0);
    let error = run(altered, &selected).unwrap_err();
    assert!(
        matches!(
            &error.0,
            PrivateFailure::Image(image::ImageFailure::InvalidRecord)
        ),
        "wrong independent-fact refusal: {error}"
    );
    assert_eq!(CALLBACKS.get(), 0);

    // The first supplied member is valid and WOULD run first. Whole-program
    // required-member admission must detect the absent second binding BEFORE it.
    CALLBACKS.set(0);
    let error = run(emitted.expected, &selected[..1]).unwrap_err();
    assert!(
        matches!(
            &error.0,
            PrivateFailure::Evaluation(crate::eval::RuntimeFailure::ForeignBinding)
        ),
        "wrong missing-binding refusal: {error}"
    );
    assert_eq!(CALLBACKS.get(), 0);

    // The refused attempts do not poison a subsequent fresh admitted execution.
    assert_eq!(run(emitted.expected, &selected).unwrap().to_string(), "43");
    assert_eq!(CALLBACKS.get(), 2);
}

#[test]
fn native_constant_image_correspondence_rejects_value_sign_representation_and_equal_value_donor() {
    let emitted = emitted_fixture();
    let selected = members();
    for mutation in 0..4 {
        let library = PrivateNativeLibrary {
            image_library: emitted.plus_one.image_library,
            module: emitted.plus_one.library_module,
            ordinal: emitted.plus_one.library_ordinal,
            members: &selected,
        };
        let mut work = TypeWorkBudget::default();
        let mut image = image::PureImage::decode_bytes(&emitted.image, &mut work).unwrap();
        assert!(image.corrupt_declared_constant_for_test(mutation));
        let bytes = image.encode_bytes(&mut work).unwrap();
        CALLBACKS.set(0);
        let refusal = __run_private_effect_image(
            &runtime_fingerprint(),
            &bytes,
            emitted.expected,
            &[library],
        )
        .unwrap_err();
        assert!(
            matches!(
                refusal.0,
                PrivateFailure::Image(_) | PrivateFailure::ForeignAdmission(_)
            ),
            "{refusal}"
        );
        assert_eq!(CALLBACKS.get(), 0);
    }
    CALLBACKS.set(0);
    assert_eq!(run(emitted.expected, &selected).unwrap().to_string(), "43");
    assert_eq!(CALLBACKS.get(), 2);
}

struct SentinelFixture {
    image: Vec<u8>,
    expected: &'static [u8],
    coordinates: PrivateNativeCoordinates,
}
static SENTINEL_FIXTURE: OnceLock<SentinelFixture> = OnceLock::new();
static SENTINEL_CALLBACKS: AtomicUsize = AtomicUsize::new(0);
fn sentinel_fixture() -> &'static SentinelFixture {
    SENTINEL_FIXTURE.get_or_init(|| {
        let sources = Sources::new();
        fs::write(sources.0.join("native.ash"), r#"import @builtin.foreign as Foreign
pub foreign library Fixed {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    repr Destructor = function_address
    sentinel Transient : Destructor = all_bits_one
    sentinel SameBits : Destructor = all_bits_one
    symbol Check<Before : EffectRow, T, After : EffectRow> : Unit -> Foreign.Call<Int> {
        name "ash_counter_noncallable_sentinel"
        abi (Destructor) -> I32
        operand 0 from constant Transient
        output result as scalar
        outcome otherwise { readable result }
    }
}
"#).unwrap();
        fs::write(sources.0.join("entry.ash"), "import @builtin.foreign as Foreign\nimport native as Native\nmain : Unit -> Foreign.Call<Int> ! {Native.Check<{}, Int, {}>}\nmain () = perform Native.Check<{}, Int, {}>.call ()\n").unwrap();
        let compiled = compile_path(RunConfiguration { entry: sources.0.join("entry.ash"), roots: ModuleRoots::empty() }).unwrap();
        let (core, provenance) = compiled.effect_build_input().unwrap();
        let mut work = TypeWorkBudget::default();
        let build = image::encode_effect_for_build(core, provenance, NATIVE_TARGET, &mut work).unwrap();
        let library = &build.libraries[0];
        let bridge = &build.bridges[0];
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
        let bytes = build.image.encode_bytes(&mut work).unwrap();
        let expected = Box::leak(build.image.encode_native_expectations(&mut work).unwrap().into_boxed_slice());
        SentinelFixture { image: bytes, expected, coordinates }
    })
}
fn sentinel_callback(
    arguments: &[NativeScalarValue],
) -> Result<NativeScalarReply, NativeScalarCallError> {
    let [NativeScalarValue::FunctionAddressAllBitsOne] = arguments else {
        return Err(NativeScalarCallError::ArgumentContract);
    };
    SENTINEL_CALLBACKS.fetch_add(1, Ordering::SeqCst);
    Ok(NativeScalarReply::Scalar(NativeScalarValue::I32(7)))
}
fn sentinel_provider() -> PrivateNativeBridge {
    let fixture = sentinel_fixture();
    __private_native_bridge(fixture.coordinates, fixture.expected, sentinel_callback)
}

#[test]
fn sentinel_image_refuses_same_bits_donor_role_representation_and_coordinate_before_callback() {
    let fixture = sentinel_fixture();
    let members = [PrivateNativeMember {
        coordinates: fixture.coordinates,
        provider: sentinel_provider,
    }];
    let library = || PrivateNativeLibrary {
        image_library: fixture.coordinates.image_library,
        module: fixture.coordinates.library_module,
        ordinal: fixture.coordinates.library_ordinal,
        members: &members,
    };
    SENTINEL_CALLBACKS.store(0, Ordering::SeqCst);
    assert_eq!(
        __run_private_effect_image(
            &runtime_fingerprint(),
            &fixture.image,
            fixture.expected,
            &[library()]
        )
        .unwrap()
        .to_string(),
        "Returned(7)"
    );
    assert_eq!(SENTINEL_CALLBACKS.load(Ordering::SeqCst), 1);
    for mutation in 0..5 {
        let mut work = TypeWorkBudget::default();
        let mut image = image::PureImage::decode_bytes(&fixture.image, &mut work).unwrap();
        assert!(image.corrupt_declared_sentinel_for_test(mutation));
        let bytes = image.encode_bytes(&mut work).unwrap();
        // A same-representation donor is structurally well formed. It changes
        // a passive original-member claim, so the independent canonical facts
        // gate below must refuse it before any generated callback can run.
        let structural = image.restore_effect(&mut TypeWorkBudget::default());
        if mutation == 1 {
            assert!(structural.is_ok());
        } else {
            assert!(
                structural.is_err(),
                "malformed sentinel mutation {mutation}"
            );
        }
        SENTINEL_CALLBACKS.store(0, Ordering::SeqCst);
        assert!(
            __run_private_effect_image(
                &runtime_fingerprint(),
                &bytes,
                fixture.expected,
                &[library()]
            )
            .is_err()
        );
        assert_eq!(SENTINEL_CALLBACKS.load(Ordering::SeqCst), 0);
    }
    SENTINEL_CALLBACKS.store(0, Ordering::SeqCst);
    assert_eq!(
        __run_private_effect_image(
            &runtime_fingerprint(),
            &fixture.image,
            fixture.expected,
            &[library()]
        )
        .unwrap()
        .to_string(),
        "Returned(7)"
    );
    assert_eq!(SENTINEL_CALLBACKS.load(Ordering::SeqCst), 1);
}
