import @builtin.compiler.syntax as Syntax

next_number : Int -> (Int, Syntax.ExpressionFragment)
next_number state = next_number(state)

pub syntax declaration: (bad_duplicate) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = $number
    )+
} with {
    $number from 0 step next_number
    $number from 0 step next_number
}
