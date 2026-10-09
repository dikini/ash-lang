import @foreign.sqlite as Native
import provider as Provider

pub type Error = MissingRow

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

pub relay<R : Type, Rows : EffectRow> : (Connection<R, {| Rows}>, Unit -> Unit ! {| Rows}) -> Error ! {ConnectionOps<R, {| Rows}>} where ConnectionProvider<R, {| Rows}>
relay operand = diagnostic operand

pub effect Inner {
    inner : Unit -> Unit
}

pub effect Outer<Rows : EffectRow> {
    outer : Unit -> Unit
}

pub interface Witness<Rows : EffectRow> {
    witness : (Unit -> Unit ! {| Rows}) -> Unit ! {| Rows}
}

pub nested : Unit -> Unit where Witness<{Outer<{Inner}>}>
nested () = ()
