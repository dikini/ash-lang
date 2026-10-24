//! External preparation callers need only public DATA types and bounds.
use ash::build::{ReceiptFailure, RequestLimits, assemble_checked_closure_data};

#[test]
fn external_closure_assembly_uses_public_limits_and_preserves_bounded_refusal() {
    // These external calls cannot compile if a crate-private meter leaks into
    // the required API arguments. Infer the function item without a duplicate
    // complex signature; use only public DATA and RequestLimits below.
    let assemble = assemble_checked_closure_data;
    let limits = RequestLimits {
        bytes: 4096,
        work: 4096,
    };
    assert_eq!(
        assemble(b"{}", [b"{}"; 6], limits),
        Err(ReceiptFailure::Malformed)
    );
    assert_eq!(
        assemble(b"{}", [b"{}"; 6], RequestLimits { work: 0, ..limits }),
        Err(ReceiptFailure::Resource)
    );
    assert_eq!(
        assemble(b"{}", [b"{}"; 6], RequestLimits { bytes: 1, ..limits }),
        Err(ReceiptFailure::Resource)
    );
    // A fresh sufficient meter still reports the actual malformed input.
    assert_eq!(
        assemble(b"{}", [b"{}"; 6], limits),
        Err(ReceiptFailure::Malformed)
    );
}
