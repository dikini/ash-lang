#![deny(unsafe_code)]
const RUNTIME_FINGERPRINT: [u8; 32] = [
    0xd5,0x5f,0x40,0xc5,0x1f,0x6e,0x46,0x96,0x41,0xa5,0x0d,0x5e,0x60,0x92,0x8d,0x4a,
    0x39,0x96,0x8f,0x23,0x72,0x8f,0x8d,0xc7,0x4a,0xae,0xd6,0xbb,0x01,0x0d,0x4b,0x7b,
];
const _: () = assert!(ash::build::__private_runtime_matches(&RUNTIME_FINGERPRINT),
    "embedded program requires its matching compiler/runtime");
const IMAGE: &[u8] = include_bytes!("program-image.bin");
static EXPECTED_FACTS: &[u8] = include_bytes!("expected-facts.bin");
static CHECKED_POLICY: &[u8] = include_bytes!("checked-policy.bin");
#[allow(unsafe_code)]
mod native_bridges {
#[cfg(not(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu", target_pointer_width = "64")))]
compile_error!("unsupported Ash native bridge target");
unsafe extern "C" {
    #[link_name = "ash_checked_owner_view"]
    fn __ash_native_m313a32_e2_o0__ffi(arg0: *mut core::ffi::c_void, arg1: usize) -> *mut core::ffi::c_void;
}
pub fn __ash_native_m313a32_e2_o0(arguments: &[ash::foreign::source_runtime::NativeOwnerOperand]) -> Result<ash::foreign::source_runtime::NativeViewReturned, ash::foreign::source_runtime::NativeScalarCallError> {
    let [ash::foreign::source_runtime::NativeOwnerOperand::Address(arg0), ash::foreign::source_runtime::NativeOwnerOperand::Scalar(ash::foreign::source_runtime::NativeScalarValue::USize(arg1))] = arguments else {
        return Err(ash::foreign::source_runtime::NativeScalarCallError::ArgumentContract);
    };
    // SAFETY: Exact preflight supplies these ABI values and live guarded addresses.
    // Linking assumes the authored synchronous native contract.
    let value = unsafe { __ash_native_m313a32_e2_o0__ffi(*arg0, *arg1) };
    Ok(ash::foreign::source_runtime::NativeViewReturned::new(value, __ash_native_m313a32_e2_o0__read))
}
fn __ash_native_m313a32_e2_o0__read(address: *mut core::ffi::c_void, index: usize) -> u8 {
    // SAFETY: the exact live window admits the native initialized extent before reading.
    unsafe { *address.cast::<u8>().add(index) }
}
pub fn __ash_native_m313a32_e2_o0__provide() -> ash::build::PrivateNativeBridge {
    ash::build::__private_native_window_view_bridge(ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 2, symbol_index: 2, operation_module: 1, operation_effect: 2, operation_local: 0 }, super::EXPECTED_FACTS, __ash_native_m313a32_e2_o0)
}
#[cfg(not(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu", target_pointer_width = "64")))]
compile_error!("unsupported Ash native bridge target");
unsafe extern "C" {
    #[link_name = "ash_checked_owner_release"]
    fn __ash_native_m313a32_e1_o0__ffi(arg0: *mut core::ffi::c_void);
}
pub fn __ash_native_m313a32_e1_o0(arguments: &[ash::foreign::source_runtime::NativeOwnerOperand]) {
    let [ash::foreign::source_runtime::NativeOwnerOperand::Address(arg0)] = arguments else {
        unreachable!("pre-admitted destruction operands");
    };
    // SAFETY: Exact preflight supplies these ABI values and live guarded addresses.
    // Linking assumes the authored synchronous native contract.
    let value = unsafe { __ash_native_m313a32_e1_o0__ffi(*arg0) };
    let () = value;
}
pub fn __ash_native_m313a32_e1_o0__provide() -> ash::build::PrivateNativeBridge {
    ash::build::__private_native_owner_teardown_bridge(ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 1, symbol_index: 1, operation_module: 1, operation_effect: 1, operation_local: 0 }, super::EXPECTED_FACTS, __ash_native_m313a32_e1_o0)
}
#[cfg(not(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu", target_pointer_width = "64")))]
compile_error!("unsupported Ash native bridge target");
unsafe extern "C" {
    #[link_name = "ash_checked_owner_length"]
    fn __ash_native_m313a32_e3_o0__ffi(arg0: *mut core::ffi::c_void, arg1: usize) -> usize;
}
pub fn __ash_native_m313a32_e3_o0(arguments: &[ash::foreign::source_runtime::NativeOwnerOperand]) -> Result<ash::foreign::source_runtime::NativeScalarReply, ash::foreign::source_runtime::NativeScalarCallError> {
    let [ash::foreign::source_runtime::NativeOwnerOperand::Address(arg0), ash::foreign::source_runtime::NativeOwnerOperand::Scalar(ash::foreign::source_runtime::NativeScalarValue::USize(arg1))] = arguments else {
        return Err(ash::foreign::source_runtime::NativeScalarCallError::ArgumentContract);
    };
    // SAFETY: Exact preflight supplies these ABI values and live guarded addresses.
    // Linking assumes the authored synchronous native contract.
    let value = unsafe { __ash_native_m313a32_e3_o0__ffi(*arg0, *arg1) };
    Ok(ash::foreign::source_runtime::NativeScalarReply::Scalar(ash::foreign::source_runtime::NativeScalarValue::USize(value)))
}
pub fn __ash_native_m313a32_e3_o0__provide() -> ash::build::PrivateNativeBridge {
    ash::build::__private_native_owner_borrow_bridge(ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 3, symbol_index: 3, operation_module: 1, operation_effect: 3, operation_local: 0 }, super::EXPECTED_FACTS, __ash_native_m313a32_e3_o0)
}
pub fn __ash_native_m313a32_e0_o0__read(address: *mut core::ffi::c_void, index: usize) -> u8 {
    // SAFETY: The original live guard admits index below its initialized byte extent.
    unsafe { address.cast::<u8>().add(index).read() }
}
pub fn __ash_native_m313a32_e0_o0__write(address: *mut core::ffi::c_void, index: usize, byte: u8) {
    // SAFETY: The original unique guard admits index below its writable initialized extent.
    unsafe { address.cast::<u8>().add(index).write(byte) };
}
#[cfg(not(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu", target_pointer_width = "64")))]
compile_error!("unsupported Ash native bridge target");
unsafe extern "C" {
    #[link_name = "ash_checked_owner_acquire"]
    fn __ash_native_m313a32_e0_o0__ffi(arg0: usize, arg1: usize) -> *mut core::ffi::c_void;
}
pub fn __ash_native_m313a32_e0_o0(arguments: &[ash::foreign::source_runtime::NativeOwnerOperand], readiness: ash::foreign::source_runtime::NativeOwnerGuardReady) -> Result<ash::foreign::source_runtime::NativeOwnerCallReturned, ash::foreign::source_runtime::NativeScalarCallError> {
    let [ash::foreign::source_runtime::NativeOwnerOperand::Scalar(ash::foreign::source_runtime::NativeScalarValue::USize(arg0)), ash::foreign::source_runtime::NativeOwnerOperand::Scalar(ash::foreign::source_runtime::NativeScalarValue::USize(arg1))] = arguments else {
        return Err(ash::foreign::source_runtime::NativeScalarCallError::ArgumentContract);
    };
    // SAFETY: Exact preflight supplies these ABI values and live guarded addresses.
    // Linking assumes the authored synchronous native contract.
    let value = unsafe { __ash_native_m313a32_e0_o0__ffi(*arg0, *arg1) };
    // Arm pre-admitted destruction before any Ash reporting step.
    Ok(readiness.returned(value))
}
pub fn __ash_native_m313a32_e0_o0__provide() -> ash::build::PrivateNativeBridge {
    ash::build::__private_native_byte_owner_acquire_bridge(ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 0, symbol_index: 0, operation_module: 1, operation_effect: 0, operation_local: 0 }, super::EXPECTED_FACTS, __ash_native_m313a32_e0_o0, __ash_native_m313a32_e0_o0__read, __ash_native_m313a32_e0_o0__write)
}
pub const MEMBERS_0: &[ash::build::PrivateNativeMember] = &[
    ash::build::PrivateNativeMember { coordinates: ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 2, symbol_index: 2, operation_module: 1, operation_effect: 2, operation_local: 0 }, provider: __ash_native_m313a32_e2_o0__provide },
    ash::build::PrivateNativeMember { coordinates: ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 1, symbol_index: 1, operation_module: 1, operation_effect: 1, operation_local: 0 }, provider: __ash_native_m313a32_e1_o0__provide },
    ash::build::PrivateNativeMember { coordinates: ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 3, symbol_index: 3, operation_module: 1, operation_effect: 3, operation_local: 0 }, provider: __ash_native_m313a32_e3_o0__provide },
    ash::build::PrivateNativeMember { coordinates: ash::build::PrivateNativeCoordinates { image_library: 0, library_module: 1, library_ordinal: 0, image_symbol: 0, symbol_index: 0, operation_module: 1, operation_effect: 0, operation_local: 0 }, provider: __ash_native_m313a32_e0_o0__provide },
];
}
const LIBRARIES: &[ash::build::PrivateNativeLibrary<'static>] = &[
    ash::build::PrivateNativeLibrary { image_library: 0, module: 1, ordinal: 0, members: native_bridges::MEMBERS_0 },
];
fn main() -> std::process::ExitCode {
    std::hint::black_box(CHECKED_POLICY);
    match ash::build::__run_private_effect_image(&RUNTIME_FINGERPRINT, IMAGE, EXPECTED_FACTS, LIBRARIES) {
        Ok(value) => { println!("{value}"); std::process::ExitCode::SUCCESS }
        Err(error) => { eprintln!("{error}"); std::process::ExitCode::FAILURE }
    }
}
