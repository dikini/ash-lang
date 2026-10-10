//! Native hosts containing matching-compiler private Core construction data.
//!
//! The initial build path supports monomorphic Pure programs. It preserves the
//! existing evaluator and independently validates reconstructed Core; it has no
//! runtime Ash compilation or stable Core file format. Effect/foreign program
//! building remains an explicit unsupported case until its connected delivery.

#[cfg(test)]
mod bridge;
mod emit;
mod host;
mod image;

pub use host::{
    BuildConfiguration, BuildFailure, BuiltProgram, NATIVE_TARGET, PreparedProgramBuild,
    build_path, build_prepared, prepare_program,
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
