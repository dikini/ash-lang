import @builtin.compiler.syntax as Syntax

pub syntax make_recursive $name:ident = $initial:expr in $body:expr => using expand
pub syntax make_fresh_recursive $initial:expr in $body:expr => using expand_fresh

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)) => get_initial(input, name, name_origin, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing binder", origin, Syntax.NoOrigins))
    }
}

get_initial : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
get_initial (input, name, name_origin, origin) = match Syntax.capture(input, 1) {
    Syntax.Captured(Syntax.ExpressionCapture(initial)) => get_body(input, name, name_origin, initial, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing initializer", origin, Syntax.NoOrigins))
}

get_body : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
get_body (input, name, name_origin, initial, origin) = match Syntax.capture(input, 2) {
    Syntax.Captured(Syntax.ExpressionCapture(body)) => build(name, name_origin, initial, body, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing body", origin, Syntax.NoOrigins))
}

expand_fresh : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_fresh input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.fresh_identifier(input, "item", origin) {
        Syntax.MadeIdentifier(name) => fresh_initial(input, name, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid identifier", origin, Syntax.NoOrigins))
    }
}

fresh_initial : (Syntax.Input, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
fresh_initial (input, name, origin) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(initial)) => fresh_body(input, name, initial, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing initializer", origin, Syntax.NoOrigins))
}

fresh_body : (Syntax.Input, Syntax.Identifier, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
fresh_body (input, name, initial, origin) = match Syntax.capture(input, 1) {
    Syntax.Captured(Syntax.ExpressionCapture(body)) => build(name, origin, initial, body, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing body", origin, Syntax.NoOrigins))
}

prepend : (Syntax.TokenKind, String, Syntax.Origin, Syntax.Nodes) -> Syntax.Nodes ! {Syntax.Ops}
prepend (kind, spelling, origin, rest) = match Syntax.make_token(kind, spelling) {
    Syntax.MadeToken(token) => Syntax.MoreNodes(Syntax.TokenNode(token, origin), rest)
    Syntax.InvalidToken => rest
}

build : (Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
build (name, name_origin, initial, body, origin) = {
    let result = Syntax.MoreNodes(Syntax.ExpressionNode(body, origin), Syntax.NoNodes)
    let line = prepend(Syntax.LineEnd, "\n", origin, result)
    let initializer = Syntax.MoreNodes(Syntax.ExpressionNode(initial, origin), line)
    let equal = prepend(Syntax.Equal, "=", origin, initializer)
    let result_type = prepend(Syntax.IntType, "Int", origin, equal)
    let arrow = prepend(Syntax.Arrow, "->", origin, result_type)
    let domain = prepend(Syntax.IntType, "Int", origin, arrow)
    let colon = prepend(Syntax.Colon, ":", origin, domain)
    let binder = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), colon)
    let recursive = prepend(Syntax.Rec, "rec", origin, binder)
    let binding = prepend(Syntax.Let, "let", origin, recursive)
    let block = prepend(Syntax.LineEnd, "\n", origin, binding)
    Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(block), origin), Syntax.NoNodes)))
}
