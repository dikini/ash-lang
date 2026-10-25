set pagination off
set confirm off
set breakpoint pending on
set debuginfod enabled off
break ash::core::validate::ValidationError::new
break ash::core::validate::ValidationError::with_cause
run elaborate::checked_owner_lifecycle_tests::checked_scalar_borrow_tests::checked_scalar_borrow_source_retains_exact_native_owner_and_assumptions --exact --nocapture
bt 18
info args
