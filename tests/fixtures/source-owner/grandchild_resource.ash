pub interface GrandProvider<Access> {
    grand_read : Access -> Int ! {GrandOps<Access>}
}
pub effect GrandOps<Access> {
    grand_read : Access -> Int
}
pub resource Grand<P, R, G> {
    owned G
    input (Child<P, R>, Int)
    state GrandState<P, R, G>
    data (Child<P, R>, Int)
    acquisition Acquire<GrandState<P, R, G>, (Child<P, R>, Int), Unit>
    completion Finish<GrandState<P, R, G>, Unit>
    result Scope<Unit, Unit, Answer> for <Answer>
    codec scope
    provider GrandProvider<Grand<P, R, G>>
    effect GrandOps<Grand<P, R, G>>
    interpret GrandAllocate<P, R, G>, GrandHold<P, R, G>
    acquire (child, label) => {
        let dependency = perform ChildOps<Child<P, R>, ChildState<P, R>>.child_borrow child
        match perform GrandAllocate<P, R, G>.call (dependency, label) {
            Foreign.Returned(Foreign.Readable(Foreign.NonNull(state))) => Acquired(state, (child, label))
            Foreign.Returned(Foreign.Readable(Foreign.Null)) => Refused ()
            Foreign.Returned(Foreign.Unreadable) => Refused ()
            Foreign.ConversionFailed(_) => Refused ()
        }
    }
    finish (state, (child, label)) => {
        let dependency = perform ChildOps<Child<P, R>, ChildState<P, R>>.child_borrow child
        match perform GrandHold<P, R, G>.call (state, dependency) {
            Foreign.Returned(Foreign.Consumed(())) => Consumed
            Foreign.Returned(Foreign.Retained(())) => Retained(state, ())
            Foreign.Returned(Foreign.BlockedDependent) => Retained(state, ())
            Foreign.ConversionFailed(_) => Retained(state, ())
        }
    }
    handlers (state, (child, label)) {
        grand_read access => resume label
    }
}
