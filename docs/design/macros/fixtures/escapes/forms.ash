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

pub syntax declaration: (nested_quote) $name:ident => {
    pub $name : Unit -> Int
    $name () = ${
        let base = syntax { 10 }
        syntax {
            ${
                let increment = syntax { 1 }
                syntax { $base + $increment }
            } * 2
        }
    }
}

pub syntax declaration: (zip_values) names $( $name:ident ),+ values $( $value:expr ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = ${
            let input = $value
            syntax { $input + 1 }
        }
    )+
}

next_number : Int -> (Int, Syntax.ExpressionFragment)
next_number state = match state == 0 {
    true => (state + 1, syntax { 0 })
    false => match state == 1 {
        true => (state + 1, syntax { 1 })
        false => match state == 2 {
            true => (state + 1, syntax { 2 })
            false => (state + 1, syntax { 3 })
        }
    }
}

pub syntax declaration: (cached) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = ${
            let first = $number
            let second = $number
            syntax { $first * 10 + $second }
        }
    )+
} with {
    $number from 0 step next_number
}

pub syntax declaration: (nested_values) $( $group:ident { $( $name:ident = $value:expr ),+ } ),+ => {
    $(
        $(
            pub $name : Unit -> Int
            $name () = ${
                let input = $value
                let count = $number
                syntax { $input + $count }
            }
        )+
    )+
} with {
    $number from 0 step next_number
}

never : Unit -> Syntax.ExpressionFragment
never () = never(())

pub syntax declaration: (empty) $( $name:ident ),* => {
    $(
        pub $name : Unit -> Int
        $name () = ${ never(()) }
    )*
}

helper : Unit -> Int
helper () = 1

pub syntax declaration: (hygienic) $name:ident from $value:expr => {
    pub $name : Unit -> Int
    $name () = ${
        let input = $value
        syntax {
            {
                let helper = 100
                $input + helper
            }
        }
    }
}

pub syntax declaration: (definition_helper) $name:ident => {
    pub $name : Unit -> Int
    $name () = ${ syntax { helper(()) } }
}
