import @builtin.compiler.syntax as Syntax

infinite_seed : Unit -> Int
infinite_seed () = infinite_seed(())

next_number : Int -> (Int, Syntax.ExpressionFragment)
next_number state = (state + 1, syntax { 0 })

pub syntax declaration: (empty_groups) $( $group:ident { $( $name:ident ),+ } ),* => {
    $(
        $(
            pub $name : Unit -> Int
            $name () = $number
        )+
    )* with {
        $number from infinite_seed(()) step next_number
    }
}
