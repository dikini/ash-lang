import @builtin.compiler.syntax as Syntax

next_number : Int -> (Int, Syntax.ExpressionFragment)
next_number state = (state + 1, syntax { 42 })

never : Unit -> Syntax.ExpressionFragment
never () = never(())

pub syntax declaration: (diverging) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = $number + ${ never(()) }
    )+
} with {
    $number from 0 step next_number
}
