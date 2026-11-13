import @builtin.compiler.syntax as Syntax

add_hundred : Syntax.ExpressionFragment -> Syntax.ExpressionFragment
add_hundred fragment = syntax { $fragment + 100 }

pub syntax declaration: (make_expr) $name:ident from $value:expr => {
    pub $name : Unit -> Int
    $name () = ${ add_hundred($value) }
}

pub syntax declaration: (local_capture) $name:ident from $value:expr => {
    pub $name : Unit -> Int
    $name () = ${
        let value = syntax { 7 }
        let captured = $value
        syntax { $value + $captured }
    }
}

pub syntax declaration: (make_ident) $name:ident => {
    pub ${ $name } : Unit -> Int
    ${ $name } () = 42
}

pub syntax declaration: (make_type) $name:ident for $T:type => {
    pub $name : ${ $T } -> ${ $T }
    $name value = value
}

pub syntax declaration: (make_pattern) $name:ident when $pattern:pattern => {
    pub $name : Bool -> Int
    $name ${ $pattern } = 42
    $name _ = 0
}

pub syntax declaration: (pass_declaration) $item:declaration => {
    ${ $item }
}
