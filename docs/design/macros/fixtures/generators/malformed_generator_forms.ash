import @builtin.compiler.syntax as Syntax

next_number : Int -> (Int, Syntax.ExpressionFragment)
next_number state = (state + 1, syntax { 0 + })

pub syntax declaration: (unused_generator) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = $number
    )+
} with {
    $number from 0 step next_number
}
