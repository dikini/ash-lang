set pagination off
set confirm off
set breakpoint pending on
set debuginfod enabled off
break src/core/validate.rs:9500
commands
silent
print **parameter
print parameter_range
continue
end
break src/core/validate.rs:9491
run elaborate::checked_owner_lifecycle_tests::checked_scalar_borrow_tests::checked_scalar_borrow_boundary_branch_cannot_transport_current_to_an_ordinary_effect --exact --nocapture --test-threads=1
print **parameter
print parameter_range
