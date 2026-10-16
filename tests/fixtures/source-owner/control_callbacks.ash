import @builtin.foreign as Foreign
import owner as Owner

pub type Error = MissingRow

pub effect H {
    op : Unit -> Unit
}
pub effect J {
    op : Unit -> Unit
}

pub effect ConnectionOps<Access, Rows : EffectRow> {
    diagnostic : (Access, Unit -> Unit ! {| Rows}) -> Error
}
pub interface ConnectionProvider<Access, Rows : EffectRow> {
    diagnostic : (Access, Unit -> Unit ! {| Rows}) -> Error ! {ConnectionOps<Access, {| Rows}>}
}
pub resource Connection<R, Rows : EffectRow> {
    owned R
    input Int
    state Owner.State<R>
    data Unit
    acquisition Owner.Acquire<Owner.State<R>, Unit, Unit>
    completion Owner.Finish<Owner.State<R>, Unit>
    result Owner.Scope<Unit, Unit, Answer> for <Answer>
    codec scope
    provider ConnectionProvider<Connection<R, {| Rows}>, {| Rows}>
    effect ConnectionOps<Connection<R, {| Rows}>, {| Rows}>
    interpret Owner.Allocate<{}, R, {| Rows}>, Owner.Free<{}, R, {| Rows}>
    acquire size => match perform Owner.Allocate<{}, R, {| Rows}>.call size {
        Foreign.Returned(Foreign.Readable(Foreign.NonNull(state))) => Owner.Acquired(state, ())
        Foreign.Returned(Foreign.Readable(Foreign.Null)) => Owner.Refused ()
        Foreign.Returned(Foreign.Unreadable) => Owner.Refused ()
        Foreign.ConversionFailed(_) => Owner.Refused ()
    }
    finish (state, data) => match perform Owner.Free<{}, R, {| Rows}>.call state {
        Foreign.Returned(Foreign.Consumed(())) => Owner.Consumed
        Foreign.Returned(Foreign.Retained(())) => Owner.Retained(state, ())
        Foreign.Returned(Foreign.BlockedDependent) => Owner.Retained(state, ())
        Foreign.ConversionFailed(_) => Owner.Retained(state, ())
    }
    handlers (state, data) {
        diagnostic (connection, callback) => {
            let ignored = callback ()
            resume MissingRow
        }
    }
}

pub client<Delta : EffectRow> : (Unit -> Unit ! {| Delta}) -> Owner.Scope<Unit, Unit, Error> ! {H | Delta}
client callback = resource Connection<C, {| Delta}> connection = 42 {
    let ignored = perform H.op ()
    diagnostic (connection, callback)
}
