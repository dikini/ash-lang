import @builtin.compiler.syntax as Syntax

pub syntax bind_id $name:ident = $initial:expr in $body:expr => using expand_bind

expand_bind : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_bind input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)) => get_initial(input, name, name_origin, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing name", origin, Syntax.NoOrigins))
    }
}

get_initial : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
get_initial (input, name, name_origin, origin) = match Syntax.capture(input, 1) {
    Syntax.Captured(Syntax.ExpressionCapture(initial)) => get_body(input, name, name_origin, initial, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing initializer", origin, Syntax.NoOrigins))
}

get_body : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
get_body (input, name, name_origin, initial, origin) = match Syntax.capture(input, 2) {
    Syntax.Captured(Syntax.ExpressionCapture(body)) => make_let(name, name_origin, initial, body, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing body", origin, Syntax.NoOrigins))
}

make_let : (Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_let (name, name_origin, initial, body, origin) = match Syntax.make_token(Syntax.Let, "let") {
    Syntax.MadeToken(let_token) => make_equal(name, name_origin, initial, body, origin, let_token)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid let", origin, Syntax.NoOrigins))
}

make_equal : (Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.ExpressionFragment, Syntax.Origin, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
make_equal (name, name_origin, initial, body, origin, let_token) = match Syntax.make_token(Syntax.Equal, "=") {
    Syntax.MadeToken(equal) => make_line(name, name_origin, initial, body, origin, let_token, equal)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid equal", origin, Syntax.NoOrigins))
}

make_line : (Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.ExpressionFragment, Syntax.Origin, Syntax.Token, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
make_line (name, name_origin, initial, body, origin, let_token, equal) = match Syntax.make_token(Syntax.LineEnd, "\n") {
    Syntax.MadeToken(line) => {
        let tail = Syntax.MoreNodes(Syntax.TokenNode(line, origin), Syntax.NoNodes)
        let body_nodes = Syntax.MoreNodes(Syntax.ExpressionNode(body, origin), tail)
        let after_initial = Syntax.MoreNodes(Syntax.TokenNode(line, origin), body_nodes)
        let initial_nodes = Syntax.MoreNodes(Syntax.ExpressionNode(initial, origin), after_initial)
        let equal_nodes = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), initial_nodes)
        let name_nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), equal_nodes)
        let let_nodes = Syntax.MoreNodes(Syntax.TokenNode(let_token, origin), name_nodes)
        let block_nodes = Syntax.MoreNodes(Syntax.TokenNode(line, origin), let_nodes)
        let group = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(block_nodes), origin)
        let nodes = Syntax.MoreNodes(group, Syntax.NoNodes)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid line", origin, Syntax.NoOrigins))
}
