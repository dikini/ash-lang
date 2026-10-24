//! Artifact-only root entry. Compilation is distinct from startup admission.
#![forbid(unsafe_code)]

pub(crate) mod transport {
    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/root-shim.rs"));
}

const IMAGE: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/src/program-image.bin"
));
const FACTS: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/src/expected-facts.bin"
));
const POLICY: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/src/checked-policy.bin"
));
#[used]
static CODE_IDENTITY: [u8; 32] = crate::build::runtime_fingerprint();

pub(super) fn main() -> std::process::ExitCode {
    // Keep the actual compile-time payloads in this image. Neither their bytes
    // nor the artifact cfg grant protected context or selected-call permission.
    std::hint::black_box((IMAGE, FACTS, POLICY));
    std::hint::black_box(&CODE_IDENTITY);
    // Actual safe transport entry addresses keep their native relocations in
    // the linked image without invoking an operation. This makes a missing
    // selected C definition a linker failure, even while startup stays closed.
    // These are private function addresses, not an admission table or handles.
    std::hint::black_box((
        transport::OwnerCell::vacant as fn() -> transport::OwnerCell,
        transport::OwnerCell::acquire
            as fn(&mut transport::OwnerCell, usize, usize) -> transport::AcquireObservation,
        transport::OwnerCell::query
            as fn(
                &transport::OwnerCell,
                usize,
            ) -> Result<
                Option<checked_owner_leaf::ViewDescriptor>,
                checked_owner_leaf::Refusal,
            >,
        transport::OwnerCell::length
            as fn(&transport::OwnerCell, usize) -> Result<usize, checked_owner_leaf::Refusal>,
        transport::OwnerCell::copy
            as fn(
                &transport::OwnerCell,
                &checked_owner_leaf::ViewDescriptor,
                usize,
                &mut [u8],
            ) -> Result<(), checked_owner_leaf::Refusal>,
        transport::OwnerCell::free as fn(transport::OwnerCell) -> transport::FreeObservation,
    ));
    std::hint::black_box(transport::OwnerCell::prepare_output_acquire
        as for<'s, 'i> fn(&'s mut transport::OwnerCell, &'i [u8])
            -> Result<checked_owner_leaf::PreparedOutputAcquire<'s, 'i>, checked_owner_leaf::Refusal>);
    std::hint::black_box(transport::OwnerCell::prepare_teardown
        as for<'s> fn(&'s mut transport::OwnerCell)
            -> Result<checked_owner_leaf::PreparedTeardown<'s>, checked_owner_leaf::Refusal>);
    std::hint::black_box(checked_owner_leaf::PreparedOutputAcquire::invoke
        as fn(checked_owner_leaf::PreparedOutputAcquire<'static, 'static>) -> checked_owner_leaf::OutputAcquireReturned);
    std::hint::black_box(checked_owner_leaf::PreparedTeardown::invoke
        as fn(checked_owner_leaf::PreparedTeardown<'static>) -> checked_owner_leaf::DisposalReturned);
    // The verifier constructs no caller token: it inspects this running object,
    // the protected approval/current context and fixed authenticated FD roles.
    // The ordinary unconfigured build still refuses MissingDeployment here.
    let result = ash_trusted_preparation::verify_running()
        .map_err(|_| ())
        .and_then(|verified| crate::build::checked_root_admission::RootProgram::restore(
            verified, IMAGE, FACTS, POLICY, &transport::CHECKED_ROLES, transport::CHECKED_PROFILE).map_err(|_| ()))
        .and_then(|program| program.run().map_err(|_| ()));
    if result.is_ok() { std::process::ExitCode::SUCCESS }
    else {
        eprintln!("checked owner startup or execution refused");
        std::process::ExitCode::FAILURE
    }
}
