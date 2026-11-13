import @builtin.compiler.syntax as Syntax

select_nodes : (Int, Int, Syntax.Nodes) -> Syntax.ExpressionFragment
select_nodes (target, index, nodes) = match nodes {
    Syntax.NoNodes => syntax { 999 }
    Syntax.MoreNodes(node, rest) => match node {
        Syntax.ExpressionNode(fragment, _) => match target == index {
            true => fragment
            false => select_nodes(target, index + 1, rest)
        }
        Syntax.TokenNode(_, _) => select_nodes(target, index, rest)
        _ => syntax { 999 }
    }
}

select_fragment : (Int, Syntax.ExpressionFragment) -> Syntax.ExpressionFragment ! {Syntax.Ops}
select_fragment (target, bank) = match Syntax.expression_syntax(bank) {
    Syntax.Syntax(Syntax.MoreNodes(Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(nodes), _), Syntax.NoNodes)) => select_nodes(target, 0, nodes)
    _ => syntax { 999 }
}

number_bank : Unit -> Syntax.ExpressionFragment
number_bank () = {
    let zero = syntax { 0 }
    let one = syntax { 1 }
    let two = syntax { 2 }
    let three = syntax { 3 }
    let four = syntax { 4 }
    let five = syntax { 5 }
    syntax { ($zero, $one, $two, $three, $four, $five) }
}

boolean_bank : Unit -> Syntax.ExpressionFragment
boolean_bank () = {
    let yes = syntax { true }
    let no = syntax { false }
    syntax { ($yes, $no) }
}

next_number : Int -> (Int, Syntax.ExpressionFragment) ! {Syntax.Ops}
next_number state = (state + 1, select_fragment(state, number_bank(())))

is_first : Int -> (Int, Syntax.ExpressionFragment) ! {Syntax.Ops}
is_first state = match state == 0 {
    true => (state + 1, select_fragment(0, boolean_bank(())))
    false => (state + 1, select_fragment(1, boolean_bank(())))
}

wrong_syntax : Int -> (Int, Syntax.ExpressionFragment) ! {Syntax.Ops}
wrong_syntax state = (state + 1, select_fragment(0, number_bank(())))

wrong_value : Int -> (Int, Syntax.ExpressionFragment) ! {Syntax.Ops}
wrong_value state = (state + 1, select_fragment(0, boolean_bank(())))

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

pub syntax declaration: (type_error) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = $number
    )+
} with {
    $number from 0 step wrong_value
}
