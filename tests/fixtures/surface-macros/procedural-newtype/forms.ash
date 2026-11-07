import @builtin.compiler.syntax as Syntax
pub syntax local $body:expr => using expand
pub syntax bind $name:ident in $body:expr => using expand_captured

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.fresh_identifier(input, "Token", origin) {
        Syntax.MadeIdentifier(name) => capture(input, name, origin, 0)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("name", origin, Syntax.NoOrigins))
    }
}

expand_captured : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_captured input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, _)) => capture(input, name, origin, 1)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("name", origin, Syntax.NoOrigins))
    }
}

capture : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Int) -> Syntax.MacroResult ! {Syntax.Ops}
capture (input, name, origin, index) = match Syntax.capture(input, index) {
    Syntax.Captured(Syntax.ExpressionCapture(body)) => build(name, body, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("body", origin, Syntax.NoOrigins))
}

prepend : (Syntax.TokenKind, String, Syntax.Origin, Syntax.Nodes) -> Syntax.Nodes ! {Syntax.Ops}
prepend (kind, spelling, origin, rest) = match Syntax.make_token(kind, spelling) {
    Syntax.MadeToken(token) => Syntax.MoreNodes(Syntax.TokenNode(token, origin), rest)
    _ => rest
}

build : (Syntax.Identifier, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
build (name, body, origin) = {
    let representation = prepend(Syntax.IntType, "Int", origin, Syntax.NoNodes)
    let fields = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(representation), origin)
    let arm = prepend(Syntax.LineEnd, "\n", origin, Syntax.NoNodes)
    let arm = Syntax.MoreNodes(Syntax.ExpressionNode(body, origin), arm)
    let arm = prepend(Syntax.FatArrow, "=>", origin, arm)
    let wildcard = prepend(Syntax.Wildcard, "_", origin, Syntax.NoNodes)
    let pattern = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(wildcard), origin)
    let arm = Syntax.MoreNodes(pattern, arm)
    let arm = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), arm)
    let arm = prepend(Syntax.LineEnd, "\n", origin, arm)
    let arms = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(arm), origin)
    let one = prepend(Syntax.IntegerLiteral, "1", origin, Syntax.NoNodes)
    let argument = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(one), origin)
    let nodes = Syntax.MoreNodes(arms, Syntax.NoNodes)
    let nodes = Syntax.MoreNodes(argument, nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), nodes)
    let nodes = prepend(Syntax.Match, "match", origin, nodes)
    let nodes = prepend(Syntax.LineEnd, "\n", origin, nodes)
    let nodes = Syntax.MoreNodes(fields, nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), nodes)
    let nodes = prepend(Syntax.Equal, "=", origin, nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), nodes)
    let nodes = prepend(Syntax.Newtype, "newtype", origin, nodes)
    let nodes = prepend(Syntax.LineEnd, "\n", origin, nodes)
    let group = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(nodes), origin)
    Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(group, Syntax.NoNodes)))
}
