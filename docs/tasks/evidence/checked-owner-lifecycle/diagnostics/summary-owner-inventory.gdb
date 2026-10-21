set pagination off
set confirm off
set print thread-events off
set debuginfod enabled off
set auto-load python-scripts off
source /home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/lib/rustlib/etc/gdb_load_rust_pretty_printers.py
set print elements 100
set print max-depth 6
break ash::resolved::ExportSummary::collect_with_providers if resolved.module.value == 0
run elaborate::checked_owner_lifecycle_tests::checked_owner_lifecycle_canonical_source_retains_originals --exact --nocapture
until src/resolved.rs:14850
p resolved.export_candidate.hidden_nominal_order
p referenced_nominals
p candidate.id
p candidate.spelling
quit
