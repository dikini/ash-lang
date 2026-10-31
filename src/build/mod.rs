//! Native hosts containing matching-compiler private Core construction data.
//!
//! Hosts reconstruct the compiler-validated Pure or Effect representation and
//! use the existing evaluator and generated native bridges. There is no runtime
//! Ash compiler or stable Core file format.

mod artifacts;
mod bridge;
mod emit;
mod gas;
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

/// Startup failure from private reconstruction or the existing evaluator.
#[doc(hidden)]
#[derive(Debug)]
pub struct PrivateProgramFailure(PrivateFailure);

#[derive(Debug)]
enum PrivateFailure {
    RuntimeMismatch,
    Image(image::ImageFailure),
    Evaluation(crate::eval::RuntimeFailure),
}

impl fmt::Display for PrivateProgramFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            PrivateFailure::RuntimeMismatch => {
                formatter.write_str("embedded program requires its matching compiler/runtime")
            }
            PrivateFailure::Image(error) => error.fmt(formatter),
            PrivateFailure::Evaluation(error) => error.fmt(formatter),
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

/// Reconstructs matching-compiler verified Core and runs it.
///
/// This entry is for generated hosts; it provides no stable image format.
/// Fingerprint compatibility precedes decoding.
/// One cumulative bounded meter covers decoding and reconstruction before
/// evaluation, with fresh program/runtime identities per call. The compiler
/// verifies the representation before producing the linked executable.
///
/// # Errors
/// Reports incompatible runtimes, decode or reconstruction failures,
/// work/storage exhaustion, and evaluator failures. It reads no original source
/// path.
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
pub type PrivateNativeScalarCallback = crate::foreign::source_runtime::NativeCallback;

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
    tuple_storage: Option<crate::eval::NativeTupleAdapter>,
) -> Result<PrivateProgramOutput, PrivateProgramFailure> {
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
    let runtime_error = |error| PrivateProgramFailure(PrivateFailure::Evaluation(error));
    let mut work = gas::startup(bytes.len(), expected_facts.len())
        .map_err(|()| image_error(image::ImageFailure::Resource))?;
    // Framing, fact comparison and reconstruction consume the same meter.
    let image = image::PureImage::decode_bytes(bytes, &mut work).map_err(image_error)?;
    image
        .admit_expected_native_facts(expected_facts, &mut work)
        .map_err(image_error)?;
    let restored = image.restore_effect(&mut work).map_err(image_error)?;
    // Reconstructed coordinates connect the compiler-generated bridge entries
    // to their fresh runtime symbols.
    let mut seen_libraries = HashSet::new();
    work.charge(libraries.len())
        .map_err(|()| image_error(image::ImageFailure::Resource))?;
    seen_libraries
        .try_reserve(libraries.len())
        .map_err(|_| image_error(image::ImageFailure::Resource))?;
    let mut bindings = SourceNativeBindings::default();
    bindings.tuple_storage = tuple_storage;
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
        let identity = restored
            .relocate_library(library.module, library.ordinal, &mut work)
            .map_err(image_error)?;
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
            if source.library() != identity
                || source.symbol_index() != index
                || source.operation() != operation
                || !std::sync::Arc::ptr_eq(source.prepared(), original)
            {
                return Err(image_error(image::ImageFailure::InvalidRecord));
            }
            // Consume the private callback only after original fact/identity
            // checks; it cannot be replaced through a public member field.
            let PrivateNativeCallback::Scalar(callback) = bridge.callback;
            bindings
                .insert(std::sync::Arc::clone(source), callback, &mut work)
                .map_err(runtime_error)?;
        }
    }
    let program = restored.into_program();
    drop(image);
    let admitted =
        admit_source_native_program(&program, &bindings, &mut work).map_err(runtime_error)?;
    let evaluated = crate::eval::evaluate_effect_with_source_native_program(admitted);
    evaluated.map(PrivateProgramOutput).map_err(runtime_error)
}

#[cfg(test)]
#[cfg(all(
    target_arch = "x86_64",
    target_os = "linux",
    target_env = "gnu",
    target_pointer_width = "64"
))]
mod native_image_tests;

// Static checked-image reconstruction test seam; no public build admission.

#[doc(hidden)]
pub type PrivateNativeBridgeProvider = fn() -> PrivateNativeBridge;
