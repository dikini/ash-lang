set pagination off
set confirm off
set breakpoint pending on
break ash::core::source_resource::invalid
run elaborate::checked_owner_lifecycle_tests::checked_scalar_borrow_tests::checked_scalar_borrow_boundary_branch_cannot_transport_current_to_an_ordinary_effect --exact --nocapture --test-threads=1
bt 24
