import @builtin.compiler.syntax as Syntax
import @builtin.compiler.syntax (fragment_node)

type LiteralNode = LiteralNode(Syntax.TokenResult)

impl Syntax.SyntaxFragment<LiteralNode> {
    fragment_node (LiteralNode(Syntax.MadeToken(token)), origin) = Syntax.TokenNode(token, origin)
    fragment_node (LiteralNode(Syntax.InvalidToken), origin) = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.NoNodes), origin)
}

digit : Int -> String
digit value = match value == 0 {
    true => "0"
    false => digit_one(value)
}

digit_one : Int -> String
digit_one value = match value == 1 {
    true => "1"
    false => digit_two(value)
}

digit_two : Int -> String
digit_two value = match value == 2 {
    true => "2"
    false => digit_three(value)
}

digit_three : Int -> String
digit_three value = match value == 3 {
    true => "3"
    false => digit_four(value)
}

digit_four : Int -> String
digit_four value = match value == 4 {
    true => "4"
    false => "5"
}

next_number : Int -> (Int, LiteralNode) ! {Syntax.Ops}
next_number state = (state + 1, LiteralNode(Syntax.make_token(Syntax.IntegerLiteral, digit(state))))

is_first : Int -> (Int, LiteralNode) ! {Syntax.Ops}
is_first state = match state == 0 {
    true => (state + 1, LiteralNode(Syntax.make_token(Syntax.True, "true")))
    false => (state + 1, LiteralNode(Syntax.make_token(Syntax.False, "false")))
}

wrong_syntax : Int -> (Int, LiteralNode) ! {Syntax.Ops}
wrong_syntax state = (state + 1, LiteralNode(Syntax.make_token(Syntax.IntType, "Int")))

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
        pub $name : Unit -> Int
        $name () = $wrong
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
