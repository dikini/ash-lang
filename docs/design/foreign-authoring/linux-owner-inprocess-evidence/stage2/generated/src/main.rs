#![deny(unsafe_code)]
const RUNTIME_FINGERPRINT: [u8; 32] = [
    0x6e,0xd6,0x12,0x09,0x0a,0x3f,0xad,0xfb,0xcc,0x98,0x2c,0x0c,0xf4,0x1b,0x21,0x0c,
    0xb0,0x2e,0x2d,0x01,0xaf,0x7d,0xb5,0xa5,0x95,0x8e,0x63,0xa6,0xfc,0x52,0x7a,0x47,
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
    #[link_name = "malloc"]
    fn __ash_native_m313a31_e0_o0__ffi(arg0: usize) -> *mut core::ffi::c_void;
}
pub fn __ash_native_m313a31_e0_o0(arguments: &[ash::foreign::source_runtime::NativeOwnerOperand], readiness: ash::foreign::source_runtime::NativeOwnerGuardReady) -> Result<ash::foreign::source_runtime::NativeOwnerCallReturned, ash::foreign::source_runtime::NativeScalarCallError> {
    let [ash::foreign::source_runtime::NativeOwnerOperand::Scalar(ash::foreign::source_runtime::NativeScalarValue::USize(arg0))] = arguments else {
        return Err(ash::foreign::source_runtime::NativeScalarCallError::ArgumentContract);
    };
    // SAFETY: Exact preflight supplies these ABI values and live guarded addresses.
    // Linking assumes the authored synchronous native contract.
    let value = unsafe { __ash_native_m313a31_e0_o0__ffi(*arg0) };
    // Arm pre-admitted destruction before any Ash reporting step.
    Ok(readiness.returned(value))
}
pub fn __ash_native_m313a31_e0_o0__provide() -> ash::build::PrivateNativeBridge {
    ash::build::__private_native_owner_acquire_bridge(ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 0, symbol_index: 0, operation_module: 1, operation_effect: 0, operation_local: 0 }, super::EXPECTED_FACTS, __ash_native_m313a31_e0_o0)
}
#[cfg(not(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu", target_pointer_width = "64")))]
compile_error!("unsupported Ash native bridge target");
unsafe extern "C" {
    #[link_name = "free"]
    fn __ash_native_m313a31_e1_o0__ffi(arg0: *mut core::ffi::c_void);
}
pub fn __ash_native_m313a31_e1_o0(arguments: &[ash::foreign::source_runtime::NativeOwnerOperand]) {
    let [ash::foreign::source_runtime::NativeOwnerOperand::Address(arg0)] = arguments else {
        unreachable!("pre-admitted destruction operands");
    };
    // SAFETY: Exact preflight supplies these ABI values and live guarded addresses.
    // Linking assumes the authored synchronous native contract.
    let value = unsafe { __ash_native_m313a31_e1_o0__ffi(*arg0) };
    let () = value;
}
pub fn __ash_native_m313a31_e1_o0__provide() -> ash::build::PrivateNativeBridge {
    ash::build::__private_native_owner_teardown_bridge(ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 1, symbol_index: 1, operation_module: 1, operation_effect: 1, operation_local: 0 }, super::EXPECTED_FACTS, __ash_native_m313a31_e1_o0)
}
pub const MEMBERS_0: &[ash::build::PrivateNativeMember] = &[
    ash::build::PrivateNativeMember { coordinates: ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 0, symbol_index: 0, operation_module: 1, operation_effect: 0, operation_local: 0 }, provider: __ash_native_m313a31_e0_o0__provide },
    ash::build::PrivateNativeMember { coordinates: ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 1, symbol_index: 1, operation_module: 1, operation_effect: 1, operation_local: 0 }, provider: __ash_native_m313a31_e1_o0__provide },
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
