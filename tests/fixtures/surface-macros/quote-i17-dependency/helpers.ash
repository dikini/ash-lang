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



pub test_next : Int -> (Int, Syntax.ExpressionFragment)
test_next state = next_number(state)
pub test_first : Int -> (Int, Syntax.ExpressionFragment)
test_first state = is_first(state)
