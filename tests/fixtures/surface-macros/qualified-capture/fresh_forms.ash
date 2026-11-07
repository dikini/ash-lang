import @builtin.compiler.syntax as Syntax

pub syntax call $value:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.fresh_identifier(input, "H", origin) {
        Syntax.MadeIdentifier(alias) => member(input, alias, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid alias", origin, Syntax.NoOrigins))
    }
}

member : (Syntax.Input, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
member (input, alias, origin) = match Syntax.caller_identifier(input, "increment", origin) {
    Syntax.MadeIdentifier(name) => dot(input, alias, name, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid member", origin, Syntax.NoOrigins))
}

dot : (Syntax.Input, Syntax.Identifier, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
dot (input, alias, name, origin) = match Syntax.make_token(Syntax.Dot, ".") {
    Syntax.MadeToken(token) => match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.ExpressionCapture(value)) => {
            let tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
            let tail = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), tail)
            let tail = Syntax.MoreNodes(Syntax.TokenNode(token, origin), tail)
            Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(Syntax.IdentifierNode(alias, origin), tail)))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing value", origin, Syntax.NoOrigins))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid dot", origin, Syntax.NoOrigins))
}
