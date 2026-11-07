import @builtin.compiler.syntax as Syntax

pub syntax fresh_pair $first:expr then $second:expr => using expand_fresh
pub syntax reuse_pair $first:expr then $second:expr => using expand_reused

expand_fresh : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_fresh input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 0), Syntax.capture(input, 1), Syntax.fresh_identifier(input, "temp", origin), Syntax.fresh_identifier(input, "temp", origin)) {
        (Syntax.Captured(Syntax.ExpressionCapture(first)), Syntax.Captured(Syntax.ExpressionCapture(second)), Syntax.MadeIdentifier(left), Syntax.MadeIdentifier(right)) => make_tokens(first, second, left, right, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing fresh input", origin, Syntax.NoOrigins))
    }
}

expand_reused : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_reused input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 0), Syntax.capture(input, 1), Syntax.fresh_identifier(input, "temp", origin)) {
        (Syntax.Captured(Syntax.ExpressionCapture(first)), Syntax.Captured(Syntax.ExpressionCapture(second)), Syntax.MadeIdentifier(name)) => make_tokens(first, second, name, name, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing reused input", origin, Syntax.NoOrigins))
    }
}

make_tokens : (Syntax.ExpressionFragment, Syntax.ExpressionFragment, Syntax.Identifier, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_tokens (first, second, left, right, origin) = match (Syntax.make_token(Syntax.Let, "let"), Syntax.make_token(Syntax.Equal, "="), Syntax.make_token(Syntax.Plus, "+"), Syntax.make_token(Syntax.LineEnd, "\n")) {
    (Syntax.MadeToken(let_token), Syntax.MadeToken(equal), Syntax.MadeToken(plus), Syntax.MadeToken(line)) => emit(first, second, left, right, origin, let_token, equal, plus, line)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid token", origin, Syntax.NoOrigins))
}

emit : (Syntax.ExpressionFragment, Syntax.ExpressionFragment, Syntax.Identifier, Syntax.Identifier, Syntax.Origin, Syntax.Token, Syntax.Token, Syntax.Token, Syntax.Token) -> Syntax.MacroResult
emit (first, second, left, right, origin, let_token, equal, plus, line) = {
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(line, origin), Syntax.NoNodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(right, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(left, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(line, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.ExpressionNode(second, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(right, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(let_token, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(line, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.ExpressionNode(first, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(left, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(let_token, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(line, origin), nodes)
    let block = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(nodes), origin)
    Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(block, Syntax.NoNodes)))
}
