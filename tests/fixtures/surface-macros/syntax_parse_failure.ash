import @builtin.compiler.syntax as Syntax

pub syntax invalid_parse $value:expr => using expand_invalid
pub syntax invalid_output $value:expr => using expand_output
pub syntax trailing_output $value:expr => using expand_trailing

expand_invalid : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_invalid input = {
    let invocation = Syntax.invocation_origin(input)
    let definition = Syntax.definition_origin(input)
    match Syntax.make_token(Syntax.IntegerLiteral, "1") {
        Syntax.MadeToken(one) => make_plus(input, invocation, definition, one)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid integer", invocation, Syntax.NoOrigins))
    }
}

expand_output : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_output input = {
    let invocation = Syntax.invocation_origin(input)
    let definition = Syntax.definition_origin(input)
    match Syntax.make_token(Syntax.IntegerLiteral, "1") {
        Syntax.MadeToken(one) => output_plus(invocation, definition, one)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid integer", invocation, Syntax.NoOrigins))
    }
}

output_plus : (Syntax.Origin, Syntax.Origin, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
output_plus (invocation, definition, one) = match Syntax.make_token(Syntax.Plus, "+") {
    Syntax.MadeToken(plus) => {
        let tail = Syntax.MoreNodes(Syntax.TokenNode(plus, definition), Syntax.NoNodes)
        let nodes = Syntax.MoreNodes(Syntax.TokenNode(one, invocation), tail)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid plus", invocation, Syntax.NoOrigins))
}

expand_trailing : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_trailing input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.make_token(Syntax.IntegerLiteral, "1") {
        Syntax.MadeToken(one) => trailing_line(origin, one)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid integer", origin, Syntax.NoOrigins))
    }
}

trailing_line : (Syntax.Origin, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
trailing_line (origin, one) = match Syntax.make_token(Syntax.LineEnd, "\n") {
    Syntax.MadeToken(line) => {
        let second = Syntax.MoreNodes(Syntax.TokenNode(one, origin), Syntax.NoNodes)
        let separator = Syntax.MoreNodes(Syntax.TokenNode(line, origin), second)
        let nodes = Syntax.MoreNodes(Syntax.TokenNode(one, origin), separator)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid line", origin, Syntax.NoOrigins))
}

make_plus : (Syntax.Input, Syntax.Origin, Syntax.Origin, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
make_plus (input, invocation, definition, one) = match Syntax.make_token(Syntax.Plus, "+") {
    Syntax.MadeToken(plus) => {
        let tail = Syntax.MoreNodes(Syntax.TokenNode(plus, definition), Syntax.NoNodes)
        let nodes = Syntax.MoreNodes(Syntax.TokenNode(one, invocation), tail)
        match Syntax.parse_expression(input, Syntax.Syntax(nodes)) {
            Syntax.ParseRejected(failure) => Syntax.Rejected(Syntax.SyntaxDiagnostic(failure))
            _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid expression parsed", invocation, Syntax.NoOrigins))
        }
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid plus", invocation, Syntax.NoOrigins))
}
