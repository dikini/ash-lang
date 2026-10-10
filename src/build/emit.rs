//! Rust host emission for matching-compiler private Pure program images.
//!
//! Only byte literals cross into the generated crate. Private image records
//! remain inside Ash; its hidden runtime entry independently restores and
//! validates them before invoking the existing evaluator.

use std::fmt;

use super::image::{ImageFailure, PureImage};
use crate::types::TypeWorkBudget;

#[derive(Debug)]
pub(crate) enum EmissionFailure {
    Image(ImageFailure),
    Resource,
}

impl fmt::Display for EmissionFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Image(error) => fmt::Display::fmt(error, formatter),
            Self::Resource => {
                formatter.write_str("Rust host emission work or storage admission refused")
            }
        }
    }
}

const HOST_START: &str = "#![forbid(unsafe_code)]\nconst RUNTIME_FINGERPRINT: [u8; 32] = [\n";
const BETWEEN_ARRAYS: &str = concat!(
    "];\n",
    "const _: () = assert!(ash::build::__private_runtime_matches(&RUNTIME_FINGERPRINT),\n",
    "    \"embedded program requires its matching compiler/runtime\");\n",
    "const IMAGE: &[u8] = &[\n",
);
const HOST_MAIN: &str = concat!(
    "];\n",
    "fn main() -> std::process::ExitCode {\n",
    "    match ash::build::__run_private_pure_image(&RUNTIME_FINGERPRINT, IMAGE) {\n",
    "        Ok(value) => {\n",
    "            println!(\"{value}\");\n",
    "            std::process::ExitCode::SUCCESS\n",
    "        }\n",
    "        Err(error) => {\n",
    "            eprintln!(\"{error}\");\n",
    "            std::process::ExitCode::FAILURE\n",
    "        }\n",
    "    }\n",
    "}\n",
);

fn array_length(bytes: usize) -> Result<usize, EmissionFailure> {
    let lines = bytes.div_ceil(16);
    bytes
        .checked_mul(5)
        .and_then(|length| {
            lines
                .checked_mul(5)
                .and_then(|extra| length.checked_add(extra))
        })
        .ok_or(EmissionFailure::Resource)
}

fn emit_array(output: &mut String, bytes: &[u8]) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for line in bytes.chunks(16) {
        output.push_str("    ");
        for byte in line {
            output.push('0');
            output.push('x');
            output.push(char::from(HEX[usize::from(byte >> 4)]));
            output.push(char::from(HEX[usize::from(byte & 15)]));
            output.push(',');
        }
        output.push('\n');
    }
}

/// Serializes a passive Pure image and emits a Rust main for the exact runtime.
///
/// The caller supplies the build-time runtime fingerprint. This function reads
/// no files and discovers no runtime identity. The hidden runtime entry must
/// reject fingerprint mismatches before decoding or execution.
pub(crate) fn pure_host(
    image: &PureImage,
    runtime_fingerprint: &[u8; 32],
    work: &mut TypeWorkBudget,
) -> Result<String, EmissionFailure> {
    let bytes = image.encode_bytes(work).map_err(EmissionFailure::Image)?;
    emit_encoded_host(&bytes, runtime_fingerprint, work)
}

fn emit_encoded_host(
    bytes: &[u8],
    runtime_fingerprint: &[u8; 32],
    work: &mut TypeWorkBudget,
) -> Result<String, EmissionFailure> {
    let length = HOST_START
        .len()
        .checked_add(BETWEEN_ARRAYS.len())
        .and_then(|length| length.checked_add(HOST_MAIN.len()))
        .and_then(|length| {
            array_length(runtime_fingerprint.len())
                .ok()
                .and_then(|extra| length.checked_add(extra))
        })
        .and_then(|length| {
            array_length(bytes.len())
                .ok()
                .and_then(|extra| length.checked_add(extra))
        })
        .ok_or(EmissionFailure::Resource)?;
    // Reserve and write charges share the caller's cumulative build allowance.
    work.charge(length.checked_mul(2).ok_or(EmissionFailure::Resource)?)
        .map_err(|()| EmissionFailure::Resource)?;
    let mut output = String::new();
    output
        .try_reserve_exact(length)
        .map_err(|_| EmissionFailure::Resource)?;
    output.push_str(HOST_START);
    emit_array(&mut output, runtime_fingerprint);
    output.push_str(BETWEEN_ARRAYS);
    emit_array(&mut output, bytes);
    output.push_str(HOST_MAIN);
    debug_assert_eq!(output.len(), length);
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_main_contains_only_literal_image_inputs_and_runtime_execution() {
        let fingerprint = [0xab; 32];
        let bytes = b"\"\\\n\0\xff";
        let mut work = TypeWorkBudget::default();
        let source = emit_encoded_host(bytes, &fingerprint, &mut work).unwrap();
        assert!(
            source.contains("ash::build::__run_private_pure_image(&RUNTIME_FINGERPRINT, IMAGE)")
        );
        assert!(source.contains("0x22,0x5c,0x0a,0x00,0xff,"));
        assert!(!source.contains("compile_path"));
        assert!(!source.contains("read_to_string"));
        assert_eq!(work.used(), source.len() * 2);
        assert_eq!(
            emit_encoded_host(
                bytes,
                &fingerprint,
                &mut TypeWorkBudget::with_limit(work.used())
            )
            .unwrap(),
            source
        );
        assert!(matches!(
            emit_encoded_host(
                bytes,
                &fingerprint,
                &mut TypeWorkBudget::with_limit(work.used() - 1)
            ),
            Err(EmissionFailure::Resource)
        ));
    }
}
