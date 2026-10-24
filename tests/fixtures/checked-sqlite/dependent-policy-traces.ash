pub dependent_policy_traces : Unit -> Bool
dependent_policy_traces () = match (
    prepare_policy (0, true), prepare_policy (0, false),
    prepare_policy (19, false), prepare_policy (7, false),
    prepare_policy (19, true), prepare_policy (7, true),
    prepare_policy (21, false), prepare_policy (100, true), prepare_policy (101, false),
    finalize_policy 0, finalize_policy 19, finalize_policy 7,
    finalize_policy 21, finalize_policy 100, finalize_policy 101,
    valid_tail ("x;", 2), valid_tail ("x; \t\n\r", 2),
    valid_tail ("x; SELECT 2", 2), valid_tail ("x;--comment", 2),
    valid_tail ("x;", 3),
    valid_tail ("", 0), valid_tail ("é;", 3), valid_tail ("é;", 2),
    valid_tail ("x;\0", 2),
    ascii_space 9, ascii_space 10, ascii_space 11, ascii_space 12, ascii_space 13, ascii_space 32,
    ascii_space 8, ascii_space 14
) {
    (
        PreparePublish, PrepareEmpty, PrepareNativeFailure, PrepareNativeFailure,
        PrepareReject, PrepareReject, PrepareReject, PrepareReject, PrepareReject,
        FinalizeOk, FinalizeNativeError, FinalizeNativeError,
        FinalizeReject, FinalizeReject, FinalizeReject,
        true, true, false, false, false, true, true, false, false,
        true, true, true, true, true, true, false, false
    ) => true
    _ => false
}
