import @builtin.compiler.syntax as Syntax
pub syntax enclosed $body:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.fresh_identifier(input, "R", origin) {
        Syntax.MadeIdentifier(identity) => name_handle(input, identity, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("identity", origin, Syntax.NoOrigins))
    }
}

name_handle : (Syntax.Input, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
name_handle (input, identity, origin) = match Syntax.fresh_identifier(input, "owner", origin) {
    Syntax.MadeIdentifier(access) => get_body(input, identity, access, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("access", origin, Syntax.NoOrigins))
}

get_body : (Syntax.Input, Syntax.Identifier, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
get_body (input, identity, access, origin) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(body)) => build(identity, access, body, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("body", origin, Syntax.NoOrigins))
}

prepend : (Syntax.TokenKind, String, Syntax.Origin, Syntax.Nodes) -> Syntax.Nodes ! {Syntax.Ops}
prepend (kind, spelling, origin, rest) = match Syntax.make_token(kind, spelling) {
    Syntax.MadeToken(token) => Syntax.MoreNodes(Syntax.TokenNode(token, origin), rest)
    _ => rest
}

build : (Syntax.Identifier, Syntax.Identifier, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
build (identity, access, body, origin) = {
    let inner = Syntax.MoreNodes(Syntax.ExpressionNode(body, origin), Syntax.NoNodes)
    let inner = prepend(Syntax.LineEnd, "\n", origin, inner)
    let group = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(inner), origin)
    let selection = Syntax.MoreNodes(group, Syntax.NoNodes)
    let selection = Syntax.MoreNodes(Syntax.IdentifierNode(access, origin), selection)
    let selection = prepend(Syntax.Using, "using", origin, selection)
    let selection = prepend(Syntax.LineEnd, "\n", origin, selection)
    let body_group = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(selection), origin)
    let nodes = Syntax.MoreNodes(body_group, Syntax.NoNodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(access, origin), nodes)
    let nodes = prepend(Syntax.Greater, ">", origin, nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(identity, origin), nodes)
    let nodes = prepend(Syntax.Less, "<", origin, nodes)
    let nodes = prepend(Syntax.Region, "region", origin, nodes)
    Syntax.Expanded(Syntax.Syntax(nodes))
}
