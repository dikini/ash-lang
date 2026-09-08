# Ash native buffer

`ash-native-buffer` is a first-party runtime adapter for Ash's native byte-buffer
provider. It owns a block returned by the host C `calloc`
and releases that block with the matching `free`.

The safe API accepts only positive lengths no greater than `isize::MAX`. It
keeps the native pointer private, exposes checked single-byte reads and writes,
and releases through `Drop`. `NativeBuffer` is neither cloneable nor manually
releasable, so one successful allocation has one owning Rust value and one
release path. It provides no allocator abstraction, raw-pointer access, bulk
view, resizing, ownership transfer or provider registry.

## Unsafe and linking audit

The crate contains four kinds of unsafe operation: calling `calloc`, calling
`free`, reading one checked byte and writing one checked byte. The source states
the invariant beside each operation. Length validation prevents pointer-offset
overflow, every access checks the stored allocation length, the pointer remains
private and non-null after construction, mutable access requires `&mut self`,
and `Drop` is the only release path.

This crate has no Cargo dependencies or transitive package graph. Its role is
first-party runtime code. The private foreign symbol set and C ABI are fixed in
source and resolved through normal build-time linking with the target system C
runtime (`#[link(name = "c")]`); the crate performs no runtime symbol lookup.
It does not bundle or require a static libc archive. The selected Linux
distribution supplies, maintains and patches libc, so release packaging must
review that system component's source, version, advisories and license for the
chosen target. No compatibility claim can precede selection of Ash's license.

## Target evidence

The bridge is enabled only on Linux x86-64 and ARM64, whose supported C ABIs use
eight-bit bytes. Other targets fail at compile time instead of substituting a
Rust allocation or typed allocation failure. Unit tests on Linux x86-64 call
the real C allocator for positive cases and verify zeroed bytes and release.
Private test-only controls separately inject a null allocation result; counters
distinguish an adapter attempt from an actual `calloc` or `free` call.

The ARM64 package compile check is cross-target evidence only. Native execution
on an ARM64 Linux host remains required before claiming native ARM64 platform
conformance or releasing the provider there.
