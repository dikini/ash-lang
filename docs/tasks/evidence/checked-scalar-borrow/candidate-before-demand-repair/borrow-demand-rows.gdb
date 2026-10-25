set pagination off
set confirm off
set breakpoint pending on
set debuginfod enabled off
source /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/lib/rustlib/etc/gdb_load_rust_pretty_printers.py
set print elements 12
break src/core/provider/row/demand.rs:1169
run elaborate::checked_owner_lifecycle_tests::checked_scalar_borrow_tests::checked_scalar_borrow_source_retains_exact_native_owner_and_assumptions --exact --nocapture
print direct.atoms
print claimed.atoms
print proof.atoms
