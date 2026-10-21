set pagination off
set confirm off
set print thread-events off
set debuginfod enabled off
set auto-load python-scripts off
source /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/lib/rustlib/etc/gdb_load_rust_pretty_printers.py
set print elements 5
set print max-depth 5
break /home/dikini/Projects/ash-lang/.worktree/checked-ffi/src/resolved.rs:12271
run elaborate::checked_owner_lifecycle_tests::checked_owner_lifecycle_canonical_source_retains_originals --exact --nocapture
p constructor.id
p constructor.spelling
p *access
p family
p self.module
bt 5
quit
