import @builtin.compiler.syntax as Syntax

pub syntax parsed $value:expr => using expand_parsed

expand_parsed : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_parsed input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.make_token(Syntax.Plus, "+") {
        Syntax.MadeToken(plus) => reject_incomplete(input, plus, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing plus", origin, Syntax.NoOrigins))
    }
}

reject_incomplete : (Syntax.Input, Syntax.Token, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
reject_incomplete (input, plus, origin) = {
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), Syntax.NoNodes)
    match Syntax.parse_expression(input, Syntax.Syntax(nodes)) {
        Syntax.ParseRejected(_) => make_unresolved(input, plus, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("incomplete expression accepted", origin, Syntax.NoOrigins))
    }
}

make_unresolved : (Syntax.Input, Syntax.Token, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_unresolved (input, plus, origin) = match Syntax.caller_identifier(input, "not_in_scope", origin) {
    Syntax.MadeIdentifier(name) => parse_unresolved(input, plus, name, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid name", origin, Syntax.NoOrigins))
}

parse_unresolved : (Syntax.Input, Syntax.Token, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_unresolved (input, plus, name, origin) = {
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), Syntax.NoNodes)
    match Syntax.parse_expression(input, Syntax.Syntax(nodes)) {
        Syntax.Parsed(_) => make_two(input, plus, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("parse resolved a name", origin, Syntax.NoOrigins))
    }
}

make_two : (Syntax.Input, Syntax.Token, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_two (input, plus, origin) = match Syntax.make_token(Syntax.IntegerLiteral, "2") {
    Syntax.MadeToken(two) => get_value(input, plus, two, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid integer", origin, Syntax.NoOrigins))
}

get_value : (Syntax.Input, Syntax.Token, Syntax.Token, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
get_value (input, plus, two, origin) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => parse_value(input, plus, two, value, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", origin, Syntax.NoOrigins))
}

parse_value : (Syntax.Input, Syntax.Token, Syntax.Token, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_value (input, plus, two, value, origin) = {
    let tail = Syntax.MoreNodes(Syntax.TokenNode(two, origin), Syntax.NoNodes)
    let middle = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), tail)
    let nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), middle)
    match Syntax.parse_expression(input, Syntax.Syntax(nodes)) {
        Syntax.Parsed(result) => {
            let result_nodes = Syntax.MoreNodes(Syntax.ExpressionNode(result, origin), Syntax.NoNodes)
            Syntax.Expanded(Syntax.Syntax(result_nodes))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("valid expression rejected", origin, Syntax.NoOrigins))
    }
}
