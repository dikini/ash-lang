import @builtin.compiler.syntax as Syntax

pub syntax combined $value:expr => using expand_combined

expand_combined : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_combined input = {
    let invocation = Syntax.invocation_origin(input)
    let definition = Syntax.definition_origin(input)
    match Syntax.combine_origins(input, Syntax.NoOrigins) {
        Syntax.MissingOrigins => combine_pair(input, invocation, definition)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("empty origins accepted", invocation, Syntax.NoOrigins))
    }
}

combine_pair : (Syntax.Input, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
combine_pair (input, invocation, definition) = {
    let tail = Syntax.MoreOrigins(definition, Syntax.NoOrigins)
    let inputs = Syntax.MoreOrigins(invocation, tail)
    match Syntax.combine_origins(input, inputs) {
        Syntax.Combined(origin) => combine_again(input, invocation, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("origins not combined", invocation, Syntax.NoOrigins))
    }
}

combine_again : (Syntax.Input, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
combine_again (input, invocation, previous) = {
    let tail = Syntax.MoreOrigins(invocation, Syntax.NoOrigins)
    let inputs = Syntax.MoreOrigins(previous, tail)
    match Syntax.combine_origins(input, inputs) {
        Syntax.Combined(origin) => make_value(input, invocation, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("nested origins not combined", invocation, Syntax.NoOrigins))
    }
}

make_value : (Syntax.Input, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_value (input, invocation, origin) = match Syntax.make_token(Syntax.IntegerLiteral, "42") {
    Syntax.MadeToken(token) => {
        let nodes = Syntax.MoreNodes(Syntax.TokenNode(token, origin), Syntax.NoNodes)
        match Syntax.parse_expression(input, Syntax.Syntax(nodes)) {
            Syntax.Parsed(expression) => Syntax.Expanded(Syntax.expression_syntax(expression))
            _ => Syntax.Rejected(Syntax.MacroDiagnostic("origin round-trip failed", invocation, Syntax.NoOrigins))
        }
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid token", invocation, Syntax.NoOrigins))
}
