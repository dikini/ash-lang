//! Native hosts containing matching-compiler private Core construction data.
//!
//! Supports the established monomorphic Pure subset and a closed owner-free
//! scalar/void native Effect slice. Both preserve the existing evaluator and
//! independently validate reconstructed Core. There is no runtime Ash compiler
//! or stable Core file format; ownership/access remain explicit exclusions.

mod artifacts;
mod bridge;
mod emit;
mod host;
mod image;

pub use host::{
    BuildConfiguration, BuildFailure, BuiltProgram, NATIVE_TARGET, NativeLinkInput,
    PreparedProgramBuild, build_path, build_prepared, prepare_program,
};

use std::{error::Error, fmt};

/// Result owner used only by matching-compiler generated hosts.
#[doc(hidden)]
#[derive(Debug)]
pub struct PrivateProgramOutput(crate::eval::Evaluation);

impl fmt::Display for PrivateProgramOutput {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0.value, formatter)
    }
}

/// Startup failure from private data admission or the existing evaluator.
#[doc(hidden)]
#[derive(Debug)]
pub struct PrivateProgramFailure(PrivateFailure);

#[derive(Debug)]
enum PrivateFailure {
    RuntimeMismatch,
    Image(image::ImageFailure),
    Evaluation(crate::eval::RuntimeFailure),
    ForeignAdmission(crate::foreign::checked_source::ForeignAdmissionError),
}

impl fmt::Display for PrivateProgramFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            PrivateFailure::RuntimeMismatch => {
                formatter.write_str("embedded program requires its matching compiler/runtime")
            }
            PrivateFailure::Image(error) => error.fmt(formatter),
            PrivateFailure::Evaluation(error) => error.fmt(formatter),
            PrivateFailure::ForeignAdmission(error) => write!(
                formatter,
                "embedded native binding admission refused: {:?}",
                error.reason()
            ),
        }
    }
}

impl Error for PrivateProgramFailure {}

pub(crate) const fn runtime_fingerprint() -> [u8; 32] {
    let bytes = env!("ASH_RUNTIME_FINGERPRINT").as_bytes();
    let mut fingerprint = [0; 32];
    let mut index = 0;
    while index < fingerprint.len() {
        const fn nibble(byte: u8) -> u8 {
            match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'f' => byte - b'a' + 10,
                _ => panic!("build-time fingerprint is hexadecimal"),
            }
        }
        fingerprint[index] = (nibble(bytes[index * 2]) << 4) | nibble(bytes[index * 2 + 1]);
        index += 1;
    }
    fingerprint
}

/// Checks generated-host compatibility at Rust compilation and again at startup.
///
/// This private protocol grants no Core or native-call authority. Generated
/// hosts use it in a constant assertion so a mismatched dependency fails to
/// compile, before the build API can publish an executable.
#[doc(hidden)]
#[must_use]
pub const fn __private_runtime_matches(expected: &[u8; 32]) -> bool {
    let actual = runtime_fingerprint();
    let mut index = 0;
    while index < actual.len() {
        if actual[index] != expected[index] {
            return false;
        }
        index += 1;
    }
    true
}

/// Restores unvalidated matching-compiler private data and runs checked Core.
///
/// This entry is for generated hosts; it provides no stable image format or
/// unchecked executable capability. Fingerprint admission precedes decoding.
/// One cumulative bounded meter covers decoding, reconstruction and independent
/// validation before evaluation, with fresh program/runtime identities per call.
///
/// # Errors
/// Refuses mismatched runtimes, malformed/unsupported Core, work/storage
/// exhaustion, and existing evaluator failures. It reads no original source path.
#[doc(hidden)]
pub fn __run_private_pure_image(
    expected_runtime: &[u8; 32],
    image: &[u8],
) -> Result<PrivateProgramOutput, PrivateProgramFailure> {
    if !__private_runtime_matches(expected_runtime) {
        return Err(PrivateProgramFailure(PrivateFailure::RuntimeMismatch));
    }
    let mut work = crate::types::TypeWorkBudget::default();
    let image = image::PureImage::decode_bytes(image, &mut work)
        .map_err(|error| PrivateProgramFailure(PrivateFailure::Image(error)))?;
    let checked = image
        .restore(&mut work)
        .map_err(|error| PrivateProgramFailure(PrivateFailure::Image(error)))?;
    crate::eval::evaluate(&checked)
        .map(PrivateProgramOutput)
        .map_err(|error| PrivateProgramFailure(PrivateFailure::Evaluation(error)))
}

// This is the only native cross-crate entry. Generated Rust never names private
// registry/image/seal constructors. PrivateProgramOutput retains Evaluation's heap.

#[doc(hidden)]
pub type PrivateNativeScalarCallback = fn(
    &[crate::foreign::source_runtime::NativeScalarValue],
) -> Result<
    crate::foreign::source_runtime::NativeScalarReply,
    crate::foreign::source_runtime::NativeScalarCallError,
>;

/// Passive original coordinates baked separately into selection and provider.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrivateNativeCoordinates {
    pub image_library: u32,
    pub library_module: u32,
    pub library_ordinal: u32,
    pub image_symbol: u32,
    pub symbol_index: u32,
    pub operation_module: u32,
    pub operation_effect: u32,
    pub operation_local: u32,
}

/// Opaque PASSIVE emitter data; it has no executable-symbol authority.
/// The generated typed provider binds its own literal expectation and callback.
#[doc(hidden)]
pub struct PrivateNativeBridge {
    coordinates: PrivateNativeCoordinates,
    expected_facts: &'static [u8],
    callback: PrivateNativeCallback,
}

enum PrivateNativeCallback {
    Scalar(PrivateNativeScalarCallback),
    OwnerAcquire(crate::foreign::source_runtime::NativeOwnerAcquireCallback),
    ByteOwnerAcquire(
        crate::foreign::source_runtime::NativeOwnerAcquireCallback,
        crate::foreign::source_runtime::NativeByteCallbacks,
    ),
    OwnerTeardown(crate::foreign::source_runtime::NativeOwnerTeardownCallback),
}

/// Constructs passive generated data, never a checked registry/symbol or binding.
///
/// Matching emitter code is trusted to supply its typed call site. Runtime fact
/// checks cannot prove an arbitrary fn pointer's or external binary's semantics.
/// Only the private Core/original-contract gate can register this data.
#[doc(hidden)]
pub fn __private_native_bridge(
    coordinates: PrivateNativeCoordinates,
    expected_facts: &'static [u8],
    callback: PrivateNativeScalarCallback,
) -> PrivateNativeBridge {
    PrivateNativeBridge {
        coordinates,
        expected_facts,
        callback: PrivateNativeCallback::Scalar(callback),
    }
}

/// Passive generated owner acquisition member; only checked scope admission can
/// grant its callback an executable lifecycle request.
#[doc(hidden)]
pub fn __private_native_owner_acquire_bridge(
    coordinates: PrivateNativeCoordinates,
    expected_facts: &'static [u8],
    callback: crate::foreign::source_runtime::NativeOwnerAcquireCallback,
) -> PrivateNativeBridge {
    PrivateNativeBridge {
        coordinates,
        expected_facts,
        callback: PrivateNativeCallback::OwnerAcquire(callback),
    }
}

/// Passive generated byte-owner callbacks. Only checked byte representation and
/// initialized acquisition contracts can admit this bundle before native entry.
#[doc(hidden)]
pub fn __private_native_byte_owner_acquire_bridge(
    coordinates: PrivateNativeCoordinates,
    expected_facts: &'static [u8],
    callback: crate::foreign::source_runtime::NativeOwnerAcquireCallback,
    read: crate::foreign::source_runtime::NativeByteReadCallback,
    write: crate::foreign::source_runtime::NativeByteWriteCallback,
) -> PrivateNativeBridge {
    PrivateNativeBridge {
        coordinates,
        expected_facts,
        callback: PrivateNativeCallback::ByteOwnerAcquire(
            callback,
            crate::foreign::source_runtime::NativeByteCallbacks { read, write },
        ),
    }
}

/// Passive generated unconditional owner teardown member.
#[doc(hidden)]
pub fn __private_native_owner_teardown_bridge(
    coordinates: PrivateNativeCoordinates,
    expected_facts: &'static [u8],
    callback: crate::foreign::source_runtime::NativeOwnerTeardownCallback,
) -> PrivateNativeBridge {
    PrivateNativeBridge {
        coordinates,
        expected_facts,
        callback: PrivateNativeCallback::OwnerTeardown(callback),
    }
}

#[doc(hidden)]
pub type PrivateNativeBridgeProvider = fn() -> PrivateNativeBridge;

/// Separately selected original coordinate, with no mutable callback field.
#[doc(hidden)]
pub struct PrivateNativeMember {
    pub coordinates: PrivateNativeCoordinates,
    pub provider: PrivateNativeBridgeProvider,
}

/// Emitter-selected original library coordinates and typed wrappers. The whole
/// normalized ABI/source fact payload remains in IMAGE, encoded once.
#[doc(hidden)]
pub struct PrivateNativeLibrary<'members> {
    pub image_library: u32,
    pub module: u32,
    pub ordinal: u32,
    pub members: &'members [PrivateNativeMember],
}

#[doc(hidden)]
pub fn __run_private_effect_image(
    expected_runtime: &[u8; 32],
    bytes: &[u8],
    expected_facts: &'static [u8],
    libraries: &[PrivateNativeLibrary<'_>],
) -> Result<PrivateProgramOutput, PrivateProgramFailure> {
    use crate::foreign::checked_source::{
        admit_executable_foreign_symbol, check_executable_foreign_library_in_program,
    };
    use crate::foreign::source_bindings::{SourceNativeBindings, admit_source_native_program};
    use std::collections::HashSet;
    if !__private_runtime_matches(expected_runtime) {
        return Err(PrivateProgramFailure(PrivateFailure::RuntimeMismatch));
    }
    if !cfg!(all(
        target_arch = "x86_64",
        target_os = "linux",
        target_env = "gnu",
        target_pointer_width = "64"
    )) {
        return Err(PrivateProgramFailure(PrivateFailure::Evaluation(
            crate::eval::RuntimeFailure::ForeignBinding,
        )));
    }
    let image_error = |error| PrivateProgramFailure(PrivateFailure::Image(error));
    let foreign_error = |error| PrivateProgramFailure(PrivateFailure::ForeignAdmission(error));
    let runtime_error = |error| PrivateProgramFailure(PrivateFailure::Evaluation(error));
    let mut work = crate::types::TypeWorkBudget::default();
    let image = image::PureImage::decode_bytes(bytes, &mut work).map_err(image_error)?;
    let facts = image
        .admit_expected_native_facts(expected_facts, &mut work)
        .map_err(image_error)?;
    let restored = image.restore_effect(&mut work).map_err(image_error)?;
    // Source admission, reconstruction and independent validation have now
    // completed. The correspondence gate consumes that inaccessible phase.
    let mut seen_libraries = HashSet::new();
    work.charge(libraries.len())
        .map_err(|()| image_error(image::ImageFailure::Resource))?;
    seen_libraries
        .try_reserve(libraries.len())
        .map_err(|_| image_error(image::ImageFailure::Resource))?;
    let mut bindings = SourceNativeBindings::default();
    for library in libraries {
        work.charge(2)
            .map_err(|()| image_error(image::ImageFailure::Resource))?;
        if !seen_libraries.insert(library.image_library) {
            return Err(image_error(image::ImageFailure::InvalidRecord));
        }
        let slot = usize::try_from(library.image_library)
            .map_err(|_| image_error(image::ImageFailure::InvalidRecord))?;
        let original = restored
            .prepared
            .get(slot)
            .ok_or_else(|| image_error(image::ImageFailure::InvalidRecord))?;
        let expected = facts
            .library(library.image_library, &restored, &mut work)
            .map_err(image_error)?;
        let identity = restored
            .relocate_library(library.module, library.ordinal, &mut work)
            .map_err(image_error)?;
        work.charge(1)
            .map_err(|()| image_error(image::ImageFailure::Resource))?;
        let checked = check_executable_foreign_library_in_program(
            identity,
            std::sync::Arc::clone(original),
            &expected,
            host::NATIVE_TARGET,
            &restored.program,
            &mut work,
        )
        .map_err(foreign_error)?;
        work.charge(library.members.len())
            .map_err(|()| image_error(image::ImageFailure::Resource))?;
        for member in library.members {
            // This fn constructs only passive metadata; generated code never
            // invokes a native call here. Its own fixed expectation cannot be
            // chosen by a caller passing a different identity into a provider.
            let bridge = (member.provider)();
            work.charge(12)
                .map_err(|()| image_error(image::ImageFailure::Resource))?;
            if bridge.coordinates != member.coordinates
                || bridge.coordinates.image_library != library.image_library
                || bridge.coordinates.library_module != library.module
                || bridge.coordinates.library_ordinal != library.ordinal
                || !std::ptr::eq(bridge.expected_facts, expected_facts)
            {
                return Err(image_error(image::ImageFailure::InvalidRecord));
            }
            let coordinates = bridge.coordinates;
            let slot = usize::try_from(coordinates.image_symbol)
                .map_err(|_| image_error(image::ImageFailure::InvalidRecord))?;
            let source = restored
                .symbols
                .get(slot)
                .ok_or_else(|| image_error(image::ImageFailure::InvalidRecord))?;
            let operation = restored
                .relocate_operation(
                    coordinates.operation_module,
                    coordinates.operation_effect,
                    coordinates.operation_local,
                    &mut work,
                )
                .map_err(image_error)?;
            let index = usize::try_from(coordinates.symbol_index)
                .map_err(|_| image_error(image::ImageFailure::InvalidRecord))?;
            let checked_symbol =
                admit_executable_foreign_symbol(&checked, source, index, operation, &mut work)
                    .map_err(foreign_error)?;
            // Consume the private callback only after original fact/identity
            // checks; it cannot be replaced through a public member field.
            match bridge.callback {
                PrivateNativeCallback::Scalar(callback) => {
                    bindings.insert_checked(checked_symbol, callback, &mut work)
                }
                PrivateNativeCallback::OwnerAcquire(callback) => bindings.insert_owner_checked(
                    checked_symbol,
                    crate::foreign::source_bindings::SourceOwnerCallback::Acquire(callback),
                    &mut work,
                ),
                PrivateNativeCallback::ByteOwnerAcquire(callback, bytes) => bindings
                    .insert_owner_checked(
                        checked_symbol,
                        crate::foreign::source_bindings::SourceOwnerCallback::ByteAcquire(
                            callback, bytes,
                        ),
                        &mut work,
                    ),
                PrivateNativeCallback::OwnerTeardown(callback) => bindings.insert_owner_checked(
                    checked_symbol,
                    crate::foreign::source_bindings::SourceOwnerCallback::Teardown(callback),
                    &mut work,
                ),
            }
            .map_err(runtime_error)?;
        }
    }
    drop(facts);
    let program = restored.into_program();
    drop(image);
    let admitted =
        admit_source_native_program(&program, &mut bindings, &mut work).map_err(runtime_error)?;
    crate::eval::evaluate_effect_with_source_native_program(admitted)
        .map(PrivateProgramOutput)
        .map_err(runtime_error)
}

#[cfg(test)]
#[path = "source_scalar_post_record_tests.rs"]
mod source_scalar_post_record_tests;

#[cfg(test)]
#[cfg(all(
    target_arch = "x86_64",
    target_os = "linux",
    target_env = "gnu",
    target_pointer_width = "64"
))]
mod native_image_tests;

#[cfg(all(
    test,
    target_arch = "x86_64",
    target_os = "linux",
    target_env = "gnu",
    target_pointer_width = "64"
))]
#[path = "source_owner_post_record_tests.rs"]
mod source_owner_post_record_tests;
