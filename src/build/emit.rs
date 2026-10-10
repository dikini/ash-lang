//! Rust host emission for matching-compiler private program images.
//!
//! Private byte payloads cross into the generated crate as literals or fixed
//! compile-time includes. Image records remain inside Ash; its hidden runtime
//! entry independently restores and validates them before invoking the existing
//! evaluator.

use std::fmt;

use super::image::{ImageFailure, PureImage};
use crate::types::TypeWorkBudget;

#[derive(Debug)]
pub(crate) enum EmissionFailure {
    Image(ImageFailure),
    Bridge(super::bridge::ForeignBridgeFailure),
    Resource,
}

impl fmt::Display for EmissionFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Image(error) => fmt::Display::fmt(error, formatter),
            Self::Bridge(error) => fmt::Display::fmt(error, formatter),
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

/// Fixed build-time payload roles. Source declarations cannot select filenames;
/// the completed preparation retains the exact private encoded payloads.
#[derive(Clone, Copy, Debug)]
pub(super) enum NativePayloadRole {
    ProgramImage,
    ExpectedFacts,
}
impl NativePayloadRole {
    pub(super) const fn file_name(self) -> &'static str {
        match self {
            Self::ProgramImage => "program-image.bin",
            Self::ExpectedFacts => "expected-facts.bin",
        }
    }
}

/// Exact encoded bytes retained by the completed preparation phase. Moving
/// these files into the tool stage does not serialize the image a second time.
#[derive(Debug)]
pub(super) struct NativePayloads {
    image: Vec<u8>,
    expected_facts: Vec<u8>,
}
impl NativePayloads {
    pub(super) fn into_files(self) -> [(NativePayloadRole, Vec<u8>); 2] {
        [
            (NativePayloadRole::ProgramImage, self.image),
            (NativePayloadRole::ExpectedFacts, self.expected_facts),
        ]
    }
}

#[derive(Debug)]
pub(super) struct NativeHostEmission {
    pub(super) rust_source: String,
    pub(super) payloads: NativePayloads,
}

const NATIVE_HOST_START: &str = "#![deny(unsafe_code)]\nconst RUNTIME_FINGERPRINT: [u8; 32] = [\n";

fn render_native_payloads(output: &mut impl fmt::Write) -> fmt::Result {
    output.write_str(concat!(
        "];\n",
        "const _: () = assert!(ash::build::__private_runtime_matches(&RUNTIME_FINGERPRINT),\n",
        "    \"embedded program requires its matching compiler/runtime\");\n",
    ))?;
    writeln!(
        output,
        "const IMAGE: &[u8] = include_bytes!({:?});",
        NativePayloadRole::ProgramImage.file_name()
    )?;
    writeln!(
        output,
        "static EXPECTED_FACTS: &[u8] = include_bytes!({:?});",
        NativePayloadRole::ExpectedFacts.file_name()
    )
}

const NATIVE_HOST_MAIN: &str = concat!(
    "];\n",
    "fn main() -> std::process::ExitCode {\n",
    "    match ash::build::__run_private_effect_image(&RUNTIME_FINGERPRINT, IMAGE, EXPECTED_FACTS, LIBRARIES) {\n",
    "        Ok(value) => { println!(\"{value}\"); std::process::ExitCode::SUCCESS }\n",
    "        Err(error) => { eprintln!(\"{error}\"); std::process::ExitCode::FAILURE }\n",
    "    }\n",
    "}\n",
);

fn render_coordinates(
    output: &mut impl fmt::Write,
    library: &super::image::NativeLibraryEmission,
    member: &super::image::NativeBridgeEmission,
) -> fmt::Result {
    write!(
        output,
        "ash::build::PrivateNativeCoordinates {{ image_library: {}, library_module: {}, library_ordinal: {}, image_symbol: {}, symbol_index: {}, operation_module: {}, operation_effect: {}, operation_local: {} }}",
        library.image_library,
        library.module,
        library.ordinal,
        member.image_symbol,
        member.symbol_index,
        member.operation_module,
        member.operation_effect,
        member.operation_local,
    )
}
fn render_native_suffix(
    output: &mut impl fmt::Write,
    build: &super::image::NativeBuildImage,
    wrappers: &[String],
) -> fmt::Result {
    output.write_str("#[allow(unsafe_code)]\nmod native_bridges {\n")?;
    for (library_index, library) in build.libraries.iter().enumerate() {
        for &member_index in &library.members {
            let member = &build.bridges[member_index];
            let name = member.plan.rust_function_name();
            // The ONLY unsafe text is the existing typed extern wrapper module.
            // Providers merely pair their own fixed literals with that wrapper.
            output.write_str(&wrappers[member_index])?;
            write!(
                output,
                "pub fn {name}__provide() -> ash::build::PrivateNativeBridge {{\n    ash::build::__private_native_bridge("
            )?;
            render_coordinates(output, library, member)?;
            writeln!(output, ", super::EXPECTED_FACTS, {name})\n}}")?;
        }
        writeln!(
            output,
            "pub const MEMBERS_{library_index}: &[ash::build::PrivateNativeMember] = &["
        )?;
        for &member_index in &library.members {
            let member = &build.bridges[member_index];
            output.write_str("    ash::build::PrivateNativeMember { coordinates: ")?;
            render_coordinates(output, library, member)?;
            writeln!(
                output,
                ", provider: {}__provide }},",
                member.plan.rust_function_name()
            )?;
        }
        output.write_str("];\n")?;
    }
    output.write_str("}\nconst LIBRARIES: &[ash::build::PrivateNativeLibrary<'static>] = &[\n")?;
    for (slot, library) in build.libraries.iter().enumerate() {
        writeln!(
            output,
            "    ash::build::PrivateNativeLibrary {{ image_library: {}, module: {}, ordinal: {}, members: native_bridges::MEMBERS_{slot} }},",
            library.image_library, library.module, library.ordinal
        )?;
    }
    output.write_str(NATIVE_HOST_MAIN)
}

/// One paid preparation pass emits exact image data, independent expectations,
/// typed wrappers and separately selected provider coordinates. Exact private
/// payloads are retained for compile-time inclusion; no runtime file read occurs.
pub(super) fn native_host(
    build: &super::image::NativeBuildImage,
    runtime_fingerprint: &[u8; 32],
    work: &mut TypeWorkBudget,
) -> Result<NativeHostEmission, EmissionFailure> {
    let bytes = build
        .image
        .encode_bytes(work)
        .map_err(EmissionFailure::Image)?;
    let facts = build
        .image
        .encode_native_expectations(work)
        .map_err(EmissionFailure::Image)?;
    work.charge(build.bridges.len())
        .map_err(|()| EmissionFailure::Resource)?;
    let mut wrappers = Vec::new();
    wrappers
        .try_reserve_exact(build.bridges.len())
        .map_err(|_| EmissionFailure::Resource)?;
    for bridge in &build.bridges {
        wrappers.push(
            super::bridge::emit_rust_bridge(&bridge.plan, work).map_err(EmissionFailure::Bridge)?,
        );
    }
    // Counting pays each exact Rust text fragment before visiting/copying it.
    // Coordinate formatting is fixed-width; this writer owns no text storage.
    struct Length<'work> {
        bytes: usize,
        work: &'work mut TypeWorkBudget,
    }
    impl fmt::Write for Length<'_> {
        fn write_str(&mut self, text: &str) -> fmt::Result {
            self.work.charge(text.len()).map_err(|()| fmt::Error)?;
            self.bytes = self.bytes.checked_add(text.len()).ok_or(fmt::Error)?;
            Ok(())
        }
    }
    let prefix = NATIVE_HOST_START
        .len()
        .checked_add(array_length(runtime_fingerprint.len())?)
        .ok_or(EmissionFailure::Resource)?;
    work.charge(prefix)
        .map_err(|()| EmissionFailure::Resource)?;
    let length = {
        let mut counter = Length {
            bytes: prefix,
            work,
        };
        render_native_payloads(&mut counter).map_err(|_| EmissionFailure::Resource)?;
        render_native_suffix(&mut counter, build, &wrappers)
            .map_err(|_| EmissionFailure::Resource)?;
        counter.bytes
    };
    work.charge(length.checked_mul(2).ok_or(EmissionFailure::Resource)?)
        .map_err(|()| EmissionFailure::Resource)?;
    let mut output = String::new();
    output
        .try_reserve_exact(length)
        .map_err(|_| EmissionFailure::Resource)?;
    output.push_str(NATIVE_HOST_START);
    emit_array(&mut output, runtime_fingerprint);
    render_native_payloads(&mut output).map_err(|_| EmissionFailure::Resource)?;
    render_native_suffix(&mut output, build, &wrappers).map_err(|_| EmissionFailure::Resource)?;
    debug_assert_eq!(output.len(), length);
    Ok(NativeHostEmission {
        rust_source: output,
        payloads: NativePayloads {
            image: bytes,
            expected_facts: facts,
        },
    })
}
