set pagination off
set confirm off
set breakpoint pending on
break ash::core::source_resource::invalid
run elaborate::checked_owner_lifecycle_tests::checked_scalar_borrow_tests::checked_scalar_borrow_source_retains_exact_native_owner_and_assumptions --exact --nocapture
bt 22
