#![deny(unsafe_code)]
const RUNTIME_FINGERPRINT: [u8; 32] = [
    0x42,0x58,0x67,0xf1,0x36,0xaa,0xe3,0x46,0x52,0xc2,0x5f,0x40,0x84,0x37,0xf6,0xa0,
    0x18,0x8c,0x32,0xc4,0x6c,0x54,0x15,0x75,0xf6,0x2c,0x15,0xe2,0x28,0xc3,0x71,0x8e,
];
const _: () = assert!(ash::build::__private_runtime_matches(&RUNTIME_FINGERPRINT),
    "embedded program requires its matching compiler/runtime");
const IMAGE: &[u8] = include_bytes!("program-image.bin");
static EXPECTED_FACTS: &[u8] = include_bytes!("expected-facts.bin");
#[allow(unsafe_code)]
mod native_bridges {
#[cfg(not(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu", target_pointer_width = "64")))]
compile_error!("unsupported Ash native bridge target");
unsafe extern "C" {
    #[link_name = "abs"]
    fn __ash_native_m313a30_e0_o0__ffi(arg0: i32) -> i32;
}
pub fn __ash_native_m313a30_e0_o0(arguments: &[ash::foreign::source_runtime::NativeScalarValue]) -> Result<ash::foreign::source_runtime::NativeScalarReply, ash::foreign::source_runtime::NativeScalarCallError> {
    let [ash::foreign::source_runtime::NativeScalarValue::I32(arg0)] = arguments else {
        return Err(ash::foreign::source_runtime::NativeScalarCallError::ArgumentContract);
    };
    // SAFETY: Exact preflight supplies these ABI values and live guarded addresses.
    // Linking assumes the authored synchronous native contract.
    let value = unsafe { __ash_native_m313a30_e0_o0__ffi(*arg0) };
    Ok(ash::foreign::source_runtime::NativeScalarReply::Scalar(ash::foreign::source_runtime::NativeScalarValue::I32(value)))
}
pub fn __ash_native_m313a30_e0_o0__provide() -> ash::build::PrivateNativeBridge {
    ash::build::__private_native_bridge(ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 0, symbol_index: 0, operation_module: 1, operation_effect: 0, operation_local: 0 }, super::EXPECTED_FACTS, __ash_native_m313a30_e0_o0)
}
pub const MEMBERS_0: &[ash::build::PrivateNativeMember] = &[
    ash::build::PrivateNativeMember { coordinates: ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 0, symbol_index: 0, operation_module: 1, operation_effect: 0, operation_local: 0 }, provider: __ash_native_m313a30_e0_o0__provide },
];
}
const LIBRARIES: &[ash::build::PrivateNativeLibrary<'static>] = &[
    ash::build::PrivateNativeLibrary { image_library: 0, module: 1, ordinal: 0, members: native_bridges::MEMBERS_0 },
];
fn main() -> std::process::ExitCode {
    match ash::build::__run_private_effect_image(&RUNTIME_FINGERPRINT, IMAGE, EXPECTED_FACTS, LIBRARIES) {
        Ok(value) => { println!("{value}"); std::process::ExitCode::SUCCESS }
        Err(error) => { eprintln!("{error}"); std::process::ExitCode::FAILURE }
    }
}
