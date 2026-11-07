import @builtin.compiler.syntax as Syntax

pub syntax make_function $name:ident in $body:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)) => get_body(input, name, name_origin, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing parameter", origin, Syntax.NoOrigins))
    }
}

get_body : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
get_body (input, name, name_origin, origin) = match Syntax.capture(input, 1) {
    Syntax.Captured(Syntax.ExpressionCapture(body)) => make_fn(name, name_origin, body, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing body", origin, Syntax.NoOrigins))
}

make_fn : (Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_fn (name, name_origin, body, origin) = match Syntax.make_token(Syntax.Fn, "fn") {
    Syntax.MadeToken(fn_token) => make_line(name, name_origin, body, origin, fn_token)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid fn", origin, Syntax.NoOrigins))
}

make_line : (Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.Origin, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
make_line (name, name_origin, body, origin, fn_token) = match Syntax.make_token(Syntax.LineEnd, "\n") {
    Syntax.MadeToken(line) => {
        let names = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), Syntax.NoNodes)
        let parameter = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(names), origin)
        let end = Syntax.MoreNodes(Syntax.TokenNode(line, origin), Syntax.NoNodes)
        let result = Syntax.MoreNodes(Syntax.ExpressionNode(body, origin), end)
        let body_nodes = Syntax.MoreNodes(Syntax.TokenNode(line, origin), result)
        let function_body = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(body_nodes), origin)
        let tail = Syntax.MoreNodes(function_body, Syntax.NoNodes)
        let after_fn = Syntax.MoreNodes(parameter, tail)
        let nodes = Syntax.MoreNodes(Syntax.TokenNode(fn_token, origin), after_fn)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid line", origin, Syntax.NoOrigins))
}
