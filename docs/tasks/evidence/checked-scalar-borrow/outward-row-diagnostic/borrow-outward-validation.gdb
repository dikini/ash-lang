set pagination off
set confirm off
set breakpoint pending on
set debuginfod enabled off
break ash::core::validate::ValidationError::new
break ash::core::validate::ValidationError::with_cause
run elaborate::checked_owner_lifecycle_tests::checked_scalar_borrow_tests::checked_scalar_borrow_boundary_branch_cannot_transport_current_to_an_ordinary_effect --exact --nocapture
bt 18
info args
