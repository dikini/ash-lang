import helper (syntax keep)
import transformer (syntax blocked)

pub syntax declaration: (emit_blocked) $name:ident for $T:type => {
    pub $name : Unit -> $T
    $name () = blocked ({
        let value : $T = 42
        value
    })
}

pub syntax declaration: (emit_nested) $name:ident for $T:type => {
    pub $name : Unit -> $T
    $name () = keep (keep ({
        let value : $T = 42
        value
    }))
}

pub syntax declaration: (emit_outer_blocked) $name:ident for $T:type => {
    pub $name : Unit -> $T
    $name () = blocked (keep ({
        let value : $T = 42
        value
    }))
}
