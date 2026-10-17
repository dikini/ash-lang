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

    // Prior materialization path is a test-only byte/cost oracle. Production
    // always renders the same typed plans directly into the complete host.
    fn materialized_native_host(
        build: &super::super::image::NativeBuildImage,
        fingerprint: &[u8; 32],
        work: &mut TypeWorkBudget,
    ) -> Result<NativeHostEmission, EmissionFailure> {
        let image = build
            .image
            .encode_bytes(work)
            .map_err(EmissionFailure::Image)?;
        let expected_facts = build
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
                super::super::bridge::emit_rust_bridge(&bridge.plan, work)
                    .map_err(EmissionFailure::Bridge)?,
            );
        }
        let rust_source = render_native_host_text(build, fingerprint, work, Some(&wrappers))?;
        Ok(NativeHostEmission {
            rust_source,
            payloads: NativePayloads {
                image,
                expected_facts,
            },
        })
    }

    #[test]
    fn product_wrapper_emission_costs_keep_the_normal_cumulative_preparation_limit() {
        use crate::{
            driver::{RunConfiguration, compile_path},
            module::ModuleRoots,
        };
        use std::{
            fs,
            sync::atomic::{AtomicU64, Ordering},
        };
        static IDS: AtomicU64 = AtomicU64::new(0);
        struct Fixture(std::path::PathBuf);
        impl Drop for Fixture {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let fixture = Fixture(std::env::temp_dir().join(format!(
            "ash-product-emission-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        )));
        fs::create_dir(&fixture.0).unwrap();
        fs::write(
            fixture.0.join("sqlite.ash"),
            include_str!("../../libraries/sqlite.ash"),
        )
        .unwrap();
        fs::write(fixture.0.join("entry.ash"), r#"import @ffi.sqlite as Sqlite
main : Unit -> Sqlite.Scope<Sqlite.OpenError, Sqlite.CloseError, Sqlite.Scope<Sqlite.PrepareError, Sqlite.FinalizeError, Sqlite.Result<Int>>> ! {Sqlite.Initialize}
main () = resource Sqlite.Connection<C> connection = Sqlite.InMemory {
    resource Sqlite.Statement<S, C> statement = (connection, "SELECT 42") {
        match Sqlite.step statement {
            Sqlite.Row => Sqlite.column_int (statement, 0)
            Sqlite.Done => Sqlite.Err Sqlite.MissingRow
            Sqlite.StepError(error) => Sqlite.Err error
        }
    }
}
"#).unwrap();
        let compiled = compile_path(RunConfiguration {
            entry: fixture.0.join("entry.ash"),
            roots: ModuleRoots::new([("ffi", &fixture.0)]).unwrap(),
        })
        .unwrap();
        let (core, provenance) = compiled.effect_build_input().unwrap();
        let mut construction =
            super::super::gas::preparation(provenance, core.node_count()).unwrap();
        let image = super::super::image::encode_effect_for_build(
            core,
            provenance,
            "x86_64-unknown-linux-gnu",
            &mut construction,
        )
        .unwrap();
        let construction_used = construction.used();
        let mut serialization = TypeWorkBudget::with_limit(construction.limit());
        let bytes = image.image.encode_bytes(&mut serialization).unwrap();
        let image_units = serialization.used();
        let facts = image
            .image
            .encode_native_expectations(&mut serialization)
            .unwrap();
        let facts_units = serialization.used() - image_units;
        let mut wrappers = TypeWorkBudget::with_limit(construction.limit());
        let mut wrapper_bytes = 0usize;
        for bridge in &image.bridges {
            wrapper_bytes += super::super::bridge::emit_rust_bridge(&bridge.plan, &mut wrappers)
                .unwrap()
                .len();
        }
        // These independent component ledgers measure required work only. Each
        // uses the adopted input-derived total; the cumulative call below
        // retains construction and its paid resident-source census.
        let mut emission = TypeWorkBudget::with_limit(construction.limit());
        let emitted = native_host(&image, &[0x42; 32], &mut emission).unwrap();
        let mut legacy = TypeWorkBudget::with_limit(construction.limit());
        let materialized = materialized_native_host(&image, &[0x42; 32], &mut legacy).unwrap();
        assert_eq!(
            emitted.rust_source, materialized.rust_source,
            "same exact typed bridge plans, coordinates and Rust bytes"
        );
        assert_eq!(emitted.payloads.image, materialized.payloads.image);
        assert_eq!(
            emitted.payloads.expected_facts,
            materialized.payloads.expected_facts
        );
        assert_eq!(
            legacy.used() - emission.used(),
            2 * wrapper_bytes,
            "only the removed intermediate storage/copy charge disappears"
        );
        let required = emission.used();
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
            short.charge(prefix).unwrap();
            assert!(native_host(&image, &[0x42; 32], &mut short).is_err());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + required);
                exact.charge(prefix).unwrap();
                let again = native_host(&image, &[0x42; 32], &mut exact).unwrap();
                assert_eq!(again.rust_source, emitted.rust_source);
                assert_eq!(exact.used(), prefix + required);
            }
        }
        println!(
            "product preparation component measurement: construction={construction_used}, image={image_units}/{}B, facts={facts_units}/{}B, bridges={}, wrapper_text={wrapper_bytes}B, wrapper_units={}, host={}B, legacy_emission={}, fused_emission_including_serialization={}, saved={}, required_component_sum={}, production_limit={}",
            bytes.len(),
            facts.len(),
            image.bridges.len(),
            wrappers.used(),
            emitted.rust_source.len(),
            legacy.used(),
            emission.used(),
            legacy.used() - emission.used(),
            construction_used + emission.used(),
            construction.limit()
        );
        assert_eq!(
            emitted.rust_source.matches("unsafe extern \"C\"").count(),
            image.bridges.len()
        );
        if construction_used + emission.used() > construction.limit() {
            assert!(
                native_host(&image, &[0x42; 32], &mut construction).is_err(),
                "separate diagnostic ledgers must not shift the production limit"
            );
        } else {
            native_host(&image, &[0x42; 32], &mut construction).unwrap();
            assert_eq!(construction.used(), construction_used + emission.used());
        }
    }

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
    wrappers: Option<&[String]>,
) -> fmt::Result {
    output.write_str("#[allow(unsafe_code)]\nmod native_bridges {\n")?;
    for (library_index, library) in build.libraries.iter().enumerate() {
        for &member_index in &library.members {
            let member = &build.bridges[member_index];
            let name = member.plan.rust_function_name();
            // The ONLY unsafe text is the existing typed extern wrapper module.
            // Providers merely pair their own fixed literals with that wrapper.
            if let Some(wrappers) = wrappers {
                output.write_str(&wrappers[member_index])?;
            } else {
                super::bridge::render_bridge(output, &member.plan)?;
            }
            let constructor = match member.plan.call() {
                super::bridge::TargetBridgeCall::Scalar => "__private_native_bridge",
                super::bridge::TargetBridgeCall::OwnerBorrow => {
                    "__private_native_owner_borrow_bridge"
                }
                super::bridge::TargetBridgeCall::WindowView => {
                    "__private_native_window_view_bridge"
                }
                super::bridge::TargetBridgeCall::OwnerAcquire
                | super::bridge::TargetBridgeCall::OwnerOutputAcquire => {
                    if member.plan.byte_owner() {
                        "__private_native_byte_owner_acquire_bridge"
                    } else {
                        "__private_native_owner_acquire_bridge"
                    }
                }
                super::bridge::TargetBridgeCall::OwnerTeardown => {
                    if matches!(member.plan.result(), super::bridge::TargetResult::Scalar(_)) {
                        "__private_native_owner_status_teardown_bridge"
                    } else {
                        "__private_native_owner_teardown_bridge"
                    }
                }
            };
            write!(
                output,
                "pub fn {name}__provide() -> ash::build::PrivateNativeBridge {{\n    ash::build::{constructor}("
            )?;
            render_coordinates(output, library, member)?;
            write!(output, ", super::EXPECTED_FACTS, {name}")?;
            if member.plan.call() == super::bridge::TargetBridgeCall::OwnerAcquire
                && member.plan.byte_owner()
            {
                write!(output, ", {name}__read, {name}__write")?;
            }
            writeln!(output, ")\n}}")?;
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
    for bridge in &build.bridges {
        super::bridge::admit_render_inspection(&bridge.plan, work)
            .map_err(EmissionFailure::Bridge)?;
    }
    let output = render_native_host_text(build, runtime_fingerprint, work, None)?;
    Ok(NativeHostEmission {
        rust_source: output,
        payloads: NativePayloads {
            image: bytes,
            expected_facts: facts,
        },
    })
}

fn render_native_host_text(
    build: &super::image::NativeBuildImage,
    runtime_fingerprint: &[u8; 32],
    work: &mut TypeWorkBudget,
    wrappers: Option<&[String]>,
) -> Result<String, EmissionFailure> {
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
        render_native_suffix(&mut counter, build, wrappers)
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
    render_native_suffix(&mut output, build, wrappers).map_err(|_| EmissionFailure::Resource)?;
    debug_assert_eq!(output.len(), length);
    Ok(output)
}
