import helper (syntax keep, syntax twice)

pub syntax declaration: (emit_keep) $name:ident for $T:type => {
    pub $name : Unit -> $T
    $name () = keep ({
        let value : $T = 42
        value
    })
}

pub syntax declaration: (emit_twice) $name:ident for $T:type => {
    pub $name : Unit -> $T
    $name () = twice ({
        let value : $T = 21
        value
    })
}
