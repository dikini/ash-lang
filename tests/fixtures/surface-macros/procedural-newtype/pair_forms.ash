import @builtin.compiler.syntax as Syntax
pub syntax local $body:expr => using expand
pub syntax same $body:expr => using expand_same
pub syntax repeated $body:expr => using expand_repeated

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.fresh_identifier(input, "Pair", origin) {
        Syntax.MadeIdentifier(name) => first(input, name, origin, "B")
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("name", origin, Syntax.NoOrigins))
    }
}

expand_same : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_same input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.fresh_identifier(input, "Pair", origin) {
        Syntax.MadeIdentifier(name) => first(input, name, origin, "A")
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("name", origin, Syntax.NoOrigins))
    }
}

expand_repeated : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_repeated input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.fresh_identifier(input, "Pair", origin) {
        Syntax.MadeIdentifier(name) => repeated_parameter(input, name, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("name", origin, Syntax.NoOrigins))
    }
}

repeated_parameter : (Syntax.Input, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
repeated_parameter (input, name, origin) = match Syntax.fresh_identifier(input, "A", origin) {
    Syntax.MadeIdentifier(a) => capture(input, name, a, a, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("a", origin, Syntax.NoOrigins))
}

first : (Syntax.Input, Syntax.Identifier, Syntax.Origin, String) -> Syntax.MacroResult ! {Syntax.Ops}
first (input, name, origin, spelling) = match Syntax.fresh_identifier(input, "A", origin) {
    Syntax.MadeIdentifier(a) => second(input, name, a, origin, spelling)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("a", origin, Syntax.NoOrigins))
}

second : (Syntax.Input, Syntax.Identifier, Syntax.Identifier, Syntax.Origin, String) -> Syntax.MacroResult ! {Syntax.Ops}
second (input, name, a, origin, spelling) = match Syntax.fresh_identifier(input, spelling, origin) {
    Syntax.MadeIdentifier(b) => capture(input, name, a, b, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("b", origin, Syntax.NoOrigins))
}

capture : (Syntax.Input, Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
capture (input, name, a, b, origin) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(body)) => build(name, a, b, body, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("body", origin, Syntax.NoOrigins))
}

prepend : (Syntax.TokenKind, String, Syntax.Origin, Syntax.Nodes) -> Syntax.Nodes ! {Syntax.Ops}
prepend (kind, spelling, origin, rest) = match Syntax.make_token(kind, spelling) {
    Syntax.MadeToken(token) => Syntax.MoreNodes(Syntax.TokenNode(token, origin), rest)
    _ => rest
}

build : (Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
build (name, a, b, body, origin) = {
    let tuple = Syntax.MoreNodes(Syntax.IdentifierNode(b, origin), Syntax.NoNodes)
    let tuple = prepend(Syntax.Comma, ",", origin, tuple)
    let tuple = Syntax.MoreNodes(Syntax.IdentifierNode(a, origin), tuple)
    let tuple = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(tuple), origin)
    let fields = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.MoreNodes(tuple, Syntax.NoNodes)), origin)
    let tuple_pattern = prepend(Syntax.Wildcard, "_", origin, Syntax.NoNodes)
    let tuple_pattern = prepend(Syntax.Comma, ",", origin, tuple_pattern)
    let tuple_pattern = prepend(Syntax.Wildcard, "_", origin, tuple_pattern)
    let tuple_pattern = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(tuple_pattern), origin)
    let pattern = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.MoreNodes(tuple_pattern, Syntax.NoNodes)), origin)
    let arm = prepend(Syntax.LineEnd, "\n", origin, Syntax.NoNodes)
    let arm = Syntax.MoreNodes(Syntax.ExpressionNode(body, origin), arm)
    let arm = prepend(Syntax.FatArrow, "=>", origin, arm)
    let arm = Syntax.MoreNodes(pattern, arm)
    let arm = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), arm)
    let arm = prepend(Syntax.LineEnd, "\n", origin, arm)
    let arms = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(arm), origin)
    let pair = prepend(Syntax.True, "true", origin, Syntax.NoNodes)
    let pair = prepend(Syntax.Comma, ",", origin, pair)
    let pair = prepend(Syntax.IntegerLiteral, "40", origin, pair)
    let pair = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(pair), origin)
    let argument = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.MoreNodes(pair, Syntax.NoNodes)), origin)
    let nodes = Syntax.MoreNodes(arms, Syntax.NoNodes)
    let nodes = Syntax.MoreNodes(argument, nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), nodes)
    let nodes = prepend(Syntax.Match, "match", origin, nodes)
    let nodes = prepend(Syntax.LineEnd, "\n", origin, nodes)
    let nodes = Syntax.MoreNodes(fields, nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), nodes)
    let nodes = prepend(Syntax.Equal, "=", origin, nodes)
    let nodes = prepend(Syntax.Greater, ">", origin, nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(b, origin), nodes)
    let nodes = prepend(Syntax.Comma, ",", origin, nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(a, origin), nodes)
    let nodes = prepend(Syntax.Less, "<", origin, nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), nodes)
    let nodes = prepend(Syntax.Newtype, "newtype", origin, nodes)
    let nodes = prepend(Syntax.LineEnd, "\n", origin, nodes)
    let group = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(nodes), origin)
    Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(group, Syntax.NoNodes)))
}
