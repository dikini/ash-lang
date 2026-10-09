import @foreign.sqlite as Native
import provider as Provider

pub type Error = MissingRow

pub effect H {
    op : Unit -> Unit
}
pub effect J {
    op : Unit -> Unit
}

pub effect ConnectionOps<R : Type, Rows : EffectRow> {
    diagnostic : (Connection<R, {| Rows}>, Unit -> Unit ! {| Rows}) -> Error
}

pub interface ConnectionProvider<R : Type, Rows : EffectRow> {
    diagnostic : (Connection<R, {| Rows}>, Unit -> Unit ! {| Rows}) -> Error ! {ConnectionOps<R, {| Rows}>}
}

pub resource Connection<R : Type, Rows : EffectRow> {
    input Native.OpenConfig
    state Native.ConnectionState<R>
    result Provider.Scope<Native.OpenError, Native.CloseError, T> for <T : Type>
    provider ConnectionProvider<R, {| Rows}>
    effect ConnectionOps<R, {| Rows}>
    interpret Native.Connection<R>
    acquire config => perform Native.Connection<R>.open config
    finish state => perform Native.Connection<R>.close state
    handlers state {
        diagnostic (db, callback) => {
            let ignored = callback ()
            resume MissingRow
        }
    }
}

pub client<Delta : EffectRow> : (Unit -> Unit ! {| Delta}) -> Provider.Scope<Native.OpenError, Native.CloseError, Error> ! {H | Delta}
client callback = resource Connection<C, {| Delta}> db = Native.InMemory {
    let ignored = perform H.op ()
    diagnostic (db, callback)
}
