import @builtin.compiler.syntax as Syntax

pub syntax square $value:expr => using expand_square
pub syntax constant $value:expr => using expand_constant

expand_square : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_square input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.ExpressionCapture(value)) => reject_mismatch(value, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", origin, Syntax.NoOrigins))
    }
}

reject_mismatch : (Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
reject_mismatch (value, origin) = match Syntax.make_token(Syntax.Star, "+") {
    Syntax.InvalidToken => make_star(value, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("mismatched token accepted", origin, Syntax.NoOrigins))
}

make_star : (Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_star (value, origin) = match Syntax.make_token(Syntax.Star, "*") {
    Syntax.MadeToken(star) => copy_star(value, origin, star)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("star creation failed", origin, Syntax.NoOrigins))
}

copy_star : (Syntax.ExpressionFragment, Syntax.Origin, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
copy_star (value, origin, star) = match Syntax.make_token(Syntax.token_kind(star), Syntax.token_spelling(star)) {
    Syntax.MadeToken(copy) => {
        let tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
        let middle = Syntax.MoreNodes(Syntax.TokenNode(copy, origin), tail)
        let nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), middle)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("token inspection failed", origin, Syntax.NoOrigins))
}

expand_constant : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_constant input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.make_token(Syntax.IntegerLiteral, "42") {
        Syntax.MadeToken(token) => {
            let nodes = Syntax.MoreNodes(Syntax.TokenNode(token, origin), Syntax.NoNodes)
            Syntax.Expanded(Syntax.Syntax(nodes))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("integer creation failed", origin, Syntax.NoOrigins))
    }
}

pub syntax grouped $value:expr => using expand_grouped
pub syntax nested_groups $value:expr => using expand_nested_groups

expand_nested_groups : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_nested_groups input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 0), Syntax.make_token(Syntax.Plus, "+"), Syntax.make_token(Syntax.Star, "*")) {
        (Syntax.Captured(Syntax.ExpressionCapture(value)), Syntax.MadeToken(plus), Syntax.MadeToken(star)) => nested_groups_output(input, value, plus, star, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing nested group input", origin, Syntax.NoOrigins))
    }
}

nested_groups_output : (Syntax.Input, Syntax.ExpressionFragment, Syntax.Token, Syntax.Token, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
nested_groups_output (input, value, plus, star, origin) = {
    let inner_tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
    let inner_middle = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), inner_tail)
    let inner_nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), inner_middle)
    let inner = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(inner_nodes), origin)
    let middle_tail = Syntax.MoreNodes(inner, Syntax.NoNodes)
    let middle_operator = Syntax.MoreNodes(Syntax.TokenNode(star, origin), middle_tail)
    let middle_nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), middle_operator)
    let middle = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(middle_nodes), origin)
    let outer_tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
    let outer_operator = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), outer_tail)
    let output = Syntax.Syntax(Syntax.MoreNodes(middle, outer_operator))
    match Syntax.parse_expression(input, output) {
        Syntax.Parsed(_) => Syntax.Expanded(output)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("nested group parse failed", origin, Syntax.NoOrigins))
    }
}

expand_grouped : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_grouped input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.ExpressionCapture(value)) => group_plus(value, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", origin, Syntax.NoOrigins))
    }
}

group_plus : (Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
group_plus (value, origin) = match Syntax.make_token(Syntax.Plus, "+") {
    Syntax.MadeToken(plus) => group_star(value, origin, plus)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("plus creation failed", origin, Syntax.NoOrigins))
}

group_star : (Syntax.ExpressionFragment, Syntax.Origin, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
group_star (value, origin, plus) = match Syntax.make_token(Syntax.Star, "*") {
    Syntax.MadeToken(star) => {
        let inside_tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
        let inside_middle = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), inside_tail)
        let inside_nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), inside_middle)
        let group = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(inside_nodes), origin)
        let outer_tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
        let outer_middle = Syntax.MoreNodes(Syntax.TokenNode(star, origin), outer_tail)
        let outer_nodes = Syntax.MoreNodes(group, outer_middle)
        Syntax.Expanded(Syntax.Syntax(outer_nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("star creation failed", origin, Syntax.NoOrigins))
}

pub syntax blocked $value:expr => using expand_blocked

expand_blocked : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_blocked input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.ExpressionCapture(value)) => block_line(value, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", origin, Syntax.NoOrigins))
    }
}

block_line : (Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
block_line (value, origin) = match Syntax.make_token(Syntax.LineEnd, "\n") {
    Syntax.MadeToken(line) => {
        let tail = Syntax.MoreNodes(Syntax.TokenNode(line, origin), Syntax.NoNodes)
        let middle = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), tail)
        let inside = Syntax.MoreNodes(Syntax.TokenNode(line, origin), middle)
        let group = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(inside), origin)
        let nodes = Syntax.MoreNodes(group, Syntax.NoNodes)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("line creation failed", origin, Syntax.NoOrigins))
}
