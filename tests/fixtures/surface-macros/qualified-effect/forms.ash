import api as Owner

pub syntax send $value:expr => {
    perform Owner.Ask.ask $value
}

pub syntax wrap $value:expr => {
    handle (perform Owner.Ask.ask $value) with Owner.Ask {
        ask value => resume value
    }
}

pub syntax send_owner $eff:ident with $value:expr => {
    perform Owner.$eff.ask $value
}

pub syntax send_caller $path:ident with $value:expr => {
    perform $path.Ask.ask $value
}

pub syntax send_both $eff:ident with $op:ident in $value:expr => {
    perform Owner.$eff.$op $value
}

pub syntax send_typed $eff:ident with $value:expr => {
    perform Owner.$eff<Int>.ask $value
}

pub syntax handle_owner $eff:ident in $body:expr => {
    handle $body with Owner.$eff {
        ask value => resume value
    }
}

pub syntax handle_caller $path:ident in $body:expr => {
    handle $body with $path.Ask {
        ask value => resume value
    }
}

pub syntax row_owner $eff:ident in $body:expr => {
    let action : Unit -> Int ! {Owner.$eff} = fn(ignored) {
        $body
    }
    action ()
}

pub syntax row_caller $path:ident in $body:expr => {
    let action : Unit -> Int ! {$path.Ask} = fn(ignored) {
        $body
    }
    action ()
}
