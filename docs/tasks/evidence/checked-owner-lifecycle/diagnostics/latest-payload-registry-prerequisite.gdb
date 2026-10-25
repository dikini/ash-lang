set pagination off
set confirm off
set print thread-events off
set debuginfod enabled off
set auto-load python-scripts off
source /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/lib/rustlib/etc/gdb_load_rust_pretty_printers.py
set print elements 8
set print max-depth 5
break /home/dikini/Projects/ash-lang/.worktree/checked-ffi/src/core/validate.rs:4780
break /home/dikini/Projects/ash-lang/.worktree/checked-ffi/src/core/validate.rs:4792
break /home/dikini/Projects/ash-lang/.worktree/checked-ffi/src/core/validate.rs:4797
break /home/dikini/Projects/ash-lang/.worktree/checked-ffi/src/core/validate.rs:4805
break /home/dikini/Projects/ash-lang/.worktree/checked-ffi/src/core/validate.rs:4809
run elaborate::checked_owner_lifecycle_tests::checked_owner_lifecycle_latest_completion_e_retains_only_the_outer_owner --exact --nocapture
bt 6
info locals
quit
