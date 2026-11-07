pub syntax declaration: (expression_value) $name:ident from $value:expr => {
    pub $name : Unit -> Int
    $name () = $value
}

pub syntax declaration: (predicate) $name:ident when $pattern:pattern => {
    pub $name : Bool -> Int
    $name $pattern = 42
    $name _ = 0
}

pub syntax declaration: (pass_declaration) $item:declaration => {
    $item
}

pub syntax declaration: (zeroes) $( $name:ident ),* => {
    $(
        pub $name : Unit -> Int
        $name () = 0
    )*
}

pub syntax declaration: (ones) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = 1
    )+
}

pub syntax declaration: (paired) left $( $left:ident ),+ right $( $right:ident ),+ => {
    $(
        pub $left : Unit -> Int
        $left () = 1
        pub $right : Unit -> Int
        $right () = 2
    )+
}
