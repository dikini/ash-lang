import @builtin.compiler.syntax as Syntax

as_subtemplate : Syntax.ExpressionFragment -> Syntax.ExpressionFragment
as_subtemplate fragment = syntax { $fragment }

next_number : Int -> (Int, Syntax.ExpressionFragment)
next_number state = (state + 1, as_subtemplate(syntax { true }))

pub syntax declaration: (wrong_value) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = $number
    )+
} with {
    $number from 0 step next_number
}
