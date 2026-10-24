// Pure source controls: no native entry, owner disposition, K, or row-generation proof.
pub policy_traces : Unit -> Bool
policy_traces () = {
    let initial = initial_policy ()
    let failed_bind = after_bind (initial, ReturnedStatus 19)
    let reset_ok = after_reset (failed_bind, ReturnedStatus 0)
    let reset_error = after_reset (failed_bind, ReturnedStatus 5)
    let clear_error = after_clear (reset_ok, ReturnedStatus 7)
    let recovered = after_clear (reset_error, ReturnedStatus 0)
    let row = after_step (recovered, ReturnedStatus 100)
    let done = after_step (row, ReturnedStatus 101)
    let busy = after_step (row, ReturnedStatus 5)
    let lost = after_step (row, BoundaryLost)
    match (
        reset_ok, reset_error, clear_error, recovered,
        can_step reset_ok, can_bind reset_error, can_clear reset_ok,
        can_step recovered, can_bind recovered,
        after_step (row, PreEntryRefused),
        after_reset (row, PreEntryRefused),
        after_bind (initial, PreEntryRefused),
        after_clear (failed_bind, PreEntryRefused),
        row, done, busy, can_step done, can_step busy,
        after_clear (after_reset (lost, ReturnedStatus 0), ReturnedStatus 0),
        open_policy (0, true), open_policy (19, true),
        open_policy (7, false), open_policy (0, false),
        open_policy (19, false), open_policy (21, true),
        open_policy (100, true), open_policy (101, false)
    ) {
        (
            Policy(Prepared, Uncertain, Usable),
            Policy(Prepared, Uncertain, Usable),
            Policy(Prepared, Uncertain, Usable),
            Policy(Prepared, Known, Usable),
            false, false, true, true, true,
            Policy(Row, Known, Usable), Policy(Row, Known, Usable),
            Policy(Prepared, Known, Usable), Policy(Prepared, Uncertain, Usable),
            Policy(Row, Known, Usable), Policy(Done, Known, Usable),
            Policy(ExecutionError, Known, Usable), false, false,
            Policy(Prepared, Known, Unavailable),
            PublishConnection, RefusePartial, RefuseNoOwner, RejectOpen,
            RejectOpen, RejectOpen, RejectOpen, RejectOpen
        ) => true
        _ => false
    }
}
