//! Connected native startup correspondence with identical pointer signatures.
//! Fixtures use canonical compilation and the actual private build encoder.
use super::*;
use crate::{
    driver::{RunConfiguration, compile_path},
    foreign::source_runtime::{NativeArgument, NativeCallError, NativeReply},
    module::ModuleRoots,
    types::TypeWorkBudget,
};
use std::{
    cell::Cell,
    fs,
    path::PathBuf,
    sync::{
        OnceLock,
        atomic::{AtomicU64, Ordering},
    },
};
const NATIVE: &str = r#"import @builtin.foreign as F
pub foreign library Pointers {
    profile "x86_64-unknown-linux-gnu"
    symbol One : F.Address -> F.Address { name "ash_native_gate_one" }
    symbol Two : F.Address -> F.Address { name "ash_native_gate_two" }
}
"#;
const ENTRY: &str = r#"import @builtin.foreign as F
import native as Native
main : Unit -> Bool ! {Native.One, Native.Two}
main () = {
    let first = perform Native.One.call (F.null ())
    let second = perform Native.Two.call first
    F.equal (first, second)
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
    one: PrivateNativeCoordinates,
    two: PrivateNativeCoordinates,
}
static FIXTURE: OnceLock<EmittedFixture> = OnceLock::new();
thread_local! { static CALLBACKS: Cell<usize> = const { Cell::new(0) }; }
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
            // Identical C shape does not authenticate a different original symbol.
            assert_eq!(
                bridge.plan.symbol().arguments(),
                &[crate::foreign::checked_source::NativeArgument::Address]
            );
            assert_eq!(
                bridge.plan.symbol().result(),
                crate::foreign::checked_source::NativeResult::Address
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
        let one = select("ash_native_gate_one");
        let two = select("ash_native_gate_two");
        assert_ne!(one.image_symbol, two.image_symbol);
        assert_ne!(one.symbol_index, two.symbol_index);
        assert_ne!(one.operation_effect, two.operation_effect);
        let image = build.image.encode_bytes(&mut work).unwrap();
        let expected = Box::leak(
            build
                .image
                .encode_native_expectations(&mut work)
                .unwrap()
                .into_boxed_slice(),
        );
        EmittedFixture {
            image,
            expected,
            one,
            two,
        }
    })
}
fn one_callback(arguments: &[NativeArgument]) -> Result<NativeReply, NativeCallError> {
    let [NativeArgument(address)] = arguments else {
        return Err(NativeCallError);
    };
    CALLBACKS.set(CALLBACKS.get() + 1);
    Ok(NativeReply::Address(*address))
}
fn two_callback(arguments: &[NativeArgument]) -> Result<NativeReply, NativeCallError> {
    let [NativeArgument(address)] = arguments else {
        return Err(NativeCallError);
    };
    CALLBACKS.set(CALLBACKS.get() + 1);
    Ok(NativeReply::Address(*address))
}
// Zero-argument providers retain their OWN original coordinate and callback.
fn one_provider() -> PrivateNativeBridge {
    let fixture = emitted_fixture();
    __private_native_bridge(fixture.one, fixture.expected, one_callback)
}
fn two_provider() -> PrivateNativeBridge {
    let fixture = emitted_fixture();
    __private_native_bridge(fixture.two, fixture.expected, two_callback)
}
fn members() -> [PrivateNativeMember; 2] {
    let fixture = emitted_fixture();
    [
        PrivateNativeMember {
            coordinates: fixture.one,
            provider: one_provider,
        },
        PrivateNativeMember {
            coordinates: fixture.two,
            provider: two_provider,
        },
    ]
}
fn run(
    expected: &'static [u8],
    members: &[PrivateNativeMember],
) -> Result<PrivateProgramOutput, PrivateProgramFailure> {
    let fixture = emitted_fixture();
    let library = PrivateNativeLibrary {
        image_library: fixture.one.image_library,
        module: fixture.one.library_module,
        ordinal: fixture.one.library_ordinal,
        members,
    };
    __run_private_effect_image(
        &runtime_fingerprint(),
        &fixture.image,
        expected,
        &[library],
        None,
    )
}
#[test]
fn native_image_restores_from_embedded_originals_and_repeats_after_source_removal() {
    let fixture = emitted_fixture();
    for _ in 0..2 {
        CALLBACKS.set(0);
        assert_eq!(
            run(fixture.expected, &members()).unwrap().to_string(),
            "true"
        );
        assert_eq!(CALLBACKS.get(), 2);
    }
}
#[test]
fn same_pointer_shape_donor_coordinates_and_provider_substitution_refuse_before_callback() {
    let fixture = emitted_fixture();
    for mutation in 0..10 {
        let mut selected = members();
        match mutation {
            0 => selected[0].coordinates.image_library = fixture.one.image_library.wrapping_add(1),
            1 => {
                selected[0].coordinates.library_module = fixture.one.library_module.wrapping_add(1)
            }
            2 => {
                selected[0].coordinates.library_ordinal =
                    fixture.one.library_ordinal.wrapping_add(1)
            }
            3 => selected[0].coordinates.image_symbol = fixture.two.image_symbol,
            4 => selected[0].coordinates.symbol_index = fixture.two.symbol_index,
            5 => {
                selected[0].coordinates.operation_module =
                    fixture.one.operation_module.wrapping_add(1)
            }
            6 => selected[0].coordinates.operation_effect = fixture.two.operation_effect,
            7 => {
                selected[0].coordinates.operation_local =
                    fixture.one.operation_local.wrapping_add(1)
            }
            8 => selected[0].provider = two_provider,
            9 => selected[1].coordinates = fixture.one,
            _ => unreachable!(),
        }
        CALLBACKS.set(0);
        assert!(
            run(fixture.expected, &selected).is_err(),
            "mutation {mutation}"
        );
        assert_eq!(CALLBACKS.get(), 0, "mutation {mutation}");
    }
    CALLBACKS.set(0);
    assert_eq!(
        run(fixture.expected, &members()).unwrap().to_string(),
        "true"
    );
    assert_eq!(CALLBACKS.get(), 2);
}
#[test]
fn native_image_framing_runtime_and_independent_facts_refuse_before_callback() {
    let fixture = emitted_fixture();
    let selected = members();
    for mutation in 0..4 {
        let mut bytes = fixture.image.clone();
        match mutation {
            0 => bytes[0] ^= 0x80,
            1 => {
                bytes.pop();
            }
            2 => bytes.push(0),
            3 => bytes.clear(),
            _ => unreachable!(),
        }
        let library = PrivateNativeLibrary {
            image_library: fixture.one.image_library,
            module: fixture.one.library_module,
            ordinal: fixture.one.library_ordinal,
            members: &selected,
        };
        CALLBACKS.set(0);
        assert!(
            __run_private_effect_image(
                &runtime_fingerprint(),
                &bytes,
                fixture.expected,
                &[library],
                None
            )
            .is_err()
        );
        assert_eq!(CALLBACKS.get(), 0);
    }
    let mut runtime = runtime_fingerprint();
    runtime[0] ^= 1;
    let library = PrivateNativeLibrary {
        image_library: fixture.one.image_library,
        module: fixture.one.library_module,
        ordinal: fixture.one.library_ordinal,
        members: &selected,
    };
    CALLBACKS.set(0);
    assert!(
        __run_private_effect_image(&runtime, &fixture.image, fixture.expected, &[library], None)
            .is_err()
    );
    assert_eq!(CALLBACKS.get(), 0);
    let mut expected = fixture.expected.to_vec();
    expected[0] ^= 1;
    let expected = Box::leak(expected.into_boxed_slice());
    CALLBACKS.set(0);
    assert!(run(expected, &selected).is_err());
    assert_eq!(CALLBACKS.get(), 0);
}
#[test]
fn changed_original_native_declarations_refuse_the_canonical_fact_payload() {
    let fixture = emitted_fixture();
    for native in [
        NATIVE.replace("ash_native_gate_one", "ash_native_gate_donor"),
        NATIVE.replace("library Pointers", "library Donor"),
    ] {
        let sources = Sources::new();
        fs::write(sources.0.join("native.ash"), native).unwrap();
        fs::write(sources.0.join("entry.ash"), ENTRY).unwrap();
        let compiled = compile_path(RunConfiguration {
            entry: sources.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        let (core, provenance) = compiled.effect_build_input().unwrap();
        let mut work = TypeWorkBudget::default();
        let build =
            image::encode_effect_for_build(core, provenance, NATIVE_TARGET, &mut work).unwrap();
        let bytes = build.image.encode_bytes(&mut work).unwrap();
        CALLBACKS.set(0);
        let selected = members();
        let library = PrivateNativeLibrary {
            image_library: fixture.one.image_library,
            module: fixture.one.library_module,
            ordinal: fixture.one.library_ordinal,
            members: &selected,
        };
        assert!(
            __run_private_effect_image(
                &runtime_fingerprint(),
                &bytes,
                fixture.expected,
                &[library],
                None
            )
            .is_err()
        );
        assert_eq!(CALLBACKS.get(), 0);
    }
}
