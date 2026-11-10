import @builtin.compiler.syntax as Syntax

pub syntax declaration: (emit_expression) $name:ident yields $body:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 0), Syntax.capture(input, 1)) {
        (Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)), Syntax.Captured(Syntax.ExpressionCapture(body))) => parse_result(input, name, name_origin, body, origin)
        _ => reject(origin)
    }
}

reject : Syntax.Origin -> Syntax.MacroResult
reject origin = Syntax.Rejected(Syntax.MacroDiagnostic("cannot emit expression", origin, Syntax.NoOrigins))

parse_result : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_result (input, name, name_origin, body, origin) = match Syntax.parse_expression(input, Syntax.expression_syntax(body)) {
    Syntax.Parsed(parsed) => tokens(name, name_origin, parsed, origin)
    _ => reject(origin)
}

tokens : (Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
tokens (name, name_origin, body, origin) = match (Syntax.make_token(Syntax.Pub, "pub"), Syntax.make_token(Syntax.Colon, ":"), Syntax.make_token(Syntax.UnitType, "Unit"), Syntax.make_token(Syntax.IntType, "Int"), Syntax.make_token(Syntax.Arrow, "->"), Syntax.make_token(Syntax.LineEnd, "\n"), Syntax.make_token(Syntax.Equal, "="), Syntax.make_token(Syntax.LeftParen, "("), Syntax.make_token(Syntax.RightParen, ")")) {
    (Syntax.MadeToken(public), Syntax.MadeToken(colon), Syntax.MadeToken(unit), Syntax.MadeToken(int), Syntax.MadeToken(arrow), Syntax.MadeToken(line), Syntax.MadeToken(equal), Syntax.MadeToken(left), Syntax.MadeToken(right)) => {
        let end = Syntax.MoreNodes(Syntax.ExpressionNode(body, origin), Syntax.NoNodes)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), end)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(right, origin), equation)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(left, origin), equation)
        let equation = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), equation)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(line, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(int, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(arrow, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(unit, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(colon, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(public, origin), signature)
        Syntax.Expanded(Syntax.Syntax(signature))
    }
    _ => reject(origin)
}
