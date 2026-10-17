import @builtin.foreign as Foreign
import owner as Owner

pub type Error = MissingRow

pub effect H {
    op : Unit -> Unit
}
pub effect Stop {
    stop : Unit -> Unit
}

pub effect ProbeOps<Access> {
    probe : (Access, Unit -> Unit ! {Stop, H}) -> Error
}
pub interface ProbeProvider<Access> {
    probe : (Access, Unit -> Unit ! {Stop, H}) -> Error ! {ProbeOps<Access>}
}
pub resource Probe<R> {
    owned R
    input Int
    state Owner.State<R>
    data Unit
    acquisition Owner.Acquire<Owner.State<R>, Unit, Unit>
    completion Owner.Finish<Owner.State<R>, Unit>
    result Owner.Scope<Unit, Unit, Answer> for <Answer>
    codec scope
    provider ProbeProvider<Probe<R>>
    effect ProbeOps<Probe<R>>
    interpret Owner.Allocate<{}, R, {}>, Owner.Free<{}, R, {}>
    acquire size => match perform Owner.Allocate<{}, R, {}>.call size {
        Foreign.Returned(Foreign.Readable(Foreign.NonNull(state))) => Owner.Acquired(state, ())
        Foreign.Returned(Foreign.Readable(Foreign.Null)) => Owner.Refused ()
        Foreign.Returned(Foreign.Unreadable) => Owner.Refused ()
        Foreign.ConversionFailed(_) => Owner.Refused ()
    }
    finish (state, data) => match perform Owner.Free<{}, R, {}>.call state {
        Foreign.Returned(Foreign.Consumed(())) => Owner.Consumed
        Foreign.Returned(Foreign.Retained(())) => Owner.Retained(state, ())
        Foreign.Returned(Foreign.BlockedDependent) => Owner.Retained(state, ())
        Foreign.ConversionFailed(_) => Owner.Retained(state, ())
    }
    handlers (state, data) {
        probe (connection, callback) => {
            let ignored = handle (callback ()) with Stop {
                stop ignored => discard
            }
            resume MissingRow
        }
    }
}

pub with_owner : Unit -> Unit ! {Stop, H}
with_owner () = {
    let abandoned = resource Owner.Probe<{}, I, {}> inner = 8 {
        cleanup fn(ignored) {
            perform H.op ()
        } {
            let ignored = perform Stop.stop ()
            ()
        }
    }
    ()
}

pub without_owner : Unit -> Unit ! {Stop, H}
without_owner () = {
    let ignored = perform H.op ()
    perform Stop.stop ()
}

pub both : Unit -> Owner.Scope<Unit, Unit, (Error, Error)> ! {H}
both () = resource Probe<P> connection = 42 {
    let first = probe (connection, with_owner)
    let second = probe (connection, without_owner)
    (first, second)
}
