import @builtin.compiler.syntax as Syntax

digit : Int -> Syntax.ExpressionFragment
digit value = match value == 0 {
    true => syntax { 0 }
    false => digit_one(value)
}

digit_one : Int -> Syntax.ExpressionFragment
digit_one value = match value == 1 {
    true => syntax { 1 }
    false => digit_two(value)
}

digit_two : Int -> Syntax.ExpressionFragment
digit_two value = match value == 2 {
    true => syntax { 2 }
    false => digit_three(value)
}

digit_three : Int -> Syntax.ExpressionFragment
digit_three value = match value == 3 {
    true => syntax { 3 }
    false => digit_four(value)
}

digit_four : Int -> Syntax.ExpressionFragment
digit_four value = match value == 4 {
    true => syntax { 4 }
    false => syntax { 5 }
}

as_subtemplate : Syntax.ExpressionFragment -> Syntax.ExpressionFragment
as_subtemplate fragment = syntax { $fragment }

next_number : Int -> (Int, Syntax.ExpressionFragment)
next_number state = (state + 1, as_subtemplate(digit(state)))

is_first : Int -> (Int, Syntax.ExpressionFragment)
is_first state = match state == 0 {
    true => (state + 1, as_subtemplate(syntax { true }))
    false => (state + 1, as_subtemplate(syntax { false }))
}

wrong_syntax : Int -> (Int, Syntax.ExpressionFragment)
wrong_syntax state = (state + 1, as_subtemplate(syntax { 0 }))

pub syntax declaration: (make_constants) starting_at $start:expr names $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = match $first {
            true => $number + 100
            false => $number
        }
    )+
} with {
    $number from $start step next_number
    $first from 0 step is_first
}

pub syntax declaration: (global_groups) $( $group:ident { $( $name:ident ),+ } ),+ => {
    $(
        $(
            pub $name : Unit -> Int
            $name () = $number
        )+
    )+
} with {
    $number from 0 step next_number
}

pub syntax declaration: (reset_groups) $( $group:ident { $( $name:ident ),+ } ),+ => {
    $(
        $(
            pub $name : Unit -> Int
            $name () = $number
        )+
    )+ with {
        $number from 0 step next_number
    }
}

pub syntax declaration: (bad_fragment) $( $name:ident ),+ => {
    $(
        pub $name : $wrong
        $name () = 0
    )+
} with {
    $wrong from 0 step wrong_syntax
}

pub syntax declaration: (mixed_depth) $( $before:ident and $after:ident { $( $name:ident ),+ } ),+ => {
    $(
        pub $before : Unit -> Int
        $before () = $number
        $(
            pub $name : Unit -> Int
            $name () = $number
        )+
        pub $after : Unit -> Int
        $after () = $number
    )+
} with {
    $number from 0 step next_number
}
