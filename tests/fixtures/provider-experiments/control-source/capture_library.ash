import @foreign.sqlite as Native
import provider as Provider

pub type Error = MissingRow
pub effect Stop {
    stop : Unit -> Unit
}
pub effect H {
    op : Unit -> Unit
}

pub effect InnerOps<R> {
    inner_ping : Inner<R> -> Unit
}
pub interface InnerProvider<R> {
    inner_ping : Inner<R> -> Unit ! {InnerOps<R>}
}
pub resource Inner<R> {
    input Native.OpenConfig
    state Native.ConnectionState<R>
    result Provider.Scope<Native.OpenError, Native.CloseError, T> for <T>
    provider InnerProvider<R>
    effect InnerOps<R>
    interpret Native.Connection<R>
    acquire config => perform Native.Connection<R>.open config
    finish state => perform Native.Connection<R>.close state
    handlers state {
        inner_ping inner => resume ()
    }
}

pub effect ProbeOps<R> {
    probe : (Probe<R>, Unit -> Unit ! {Stop, H}) -> Error
}
pub interface ProbeProvider<R> {
    probe : (Probe<R>, Unit -> Unit ! {Stop, H}) -> Error ! {ProbeOps<R>}
}
pub resource Probe<R> {
    input Native.OpenConfig
    state Native.ConnectionState<R>
    result Provider.Scope<Native.OpenError, Native.CloseError, T> for <T>
    provider ProbeProvider<R>
    effect ProbeOps<R>
    interpret Native.Connection<R>
    acquire config => perform Native.Connection<R>.open config
    finish state => perform Native.Connection<R>.close state
    handlers state {
        probe (db, callback) => {
            let ignored = handle (callback ()) with Stop {
                stop ignored => discard
            }
            resume MissingRow
        }
    }
}

pub with_owner : Unit -> Unit ! {Stop, H}
with_owner () = {
    let abandoned = resource Inner<I> inner = Native.InMemory {
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

pub both : Unit -> Provider.Scope<Native.OpenError, Native.CloseError, (Error, Error)> ! {H}
both () = resource Probe<P> db = Native.InMemory {
    let first = probe (db, with_owner)
    let second = probe (db, without_owner)
    (first, second)
}
