import @builtin.compiler.syntax as Syntax

pub syntax declaration: (emit_type) $name:ident as $result:type => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 0), Syntax.capture(input, 1)) {
        (Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)), Syntax.Captured(Syntax.TypeCapture(result))) => parse_result(input, name, name_origin, result, origin)
        _ => reject(origin)
    }
}

reject : Syntax.Origin -> Syntax.MacroResult
reject origin = Syntax.Rejected(Syntax.MacroDiagnostic("cannot emit type", origin, Syntax.NoOrigins))

parse_result : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.TypeFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_result (input, name, name_origin, result, origin) = match Syntax.parse_type(input, Syntax.type_syntax(result)) {
    Syntax.ParsedType(parsed) => tokens(name, name_origin, parsed, origin)
    _ => reject(origin)
}

tokens : (Syntax.Identifier, Syntax.Origin, Syntax.TypeFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
tokens (name, name_origin, result, origin) = match (Syntax.make_token(Syntax.Pub, "pub"), Syntax.make_token(Syntax.Colon, ":"), Syntax.make_token(Syntax.UnitType, "Unit"), Syntax.make_token(Syntax.Arrow, "->"), Syntax.make_token(Syntax.LineEnd, "\n"), Syntax.make_token(Syntax.Equal, "="), Syntax.make_token(Syntax.IntegerLiteral, "42")) {
    (Syntax.MadeToken(public), Syntax.MadeToken(colon), Syntax.MadeToken(unit), Syntax.MadeToken(arrow), Syntax.MadeToken(line), Syntax.MadeToken(equal), Syntax.MadeToken(value)) => {
        let end = Syntax.MoreNodes(Syntax.TokenNode(value, origin), Syntax.NoNodes)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), end)
        let argument = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.NoNodes), origin)
        let equation = Syntax.MoreNodes(argument, equation)
        let equation = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), equation)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(line, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TypeNode(result, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(arrow, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(unit, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(colon, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(public, origin), signature)
        Syntax.Expanded(Syntax.Syntax(signature))
    }
    _ => reject(origin)
}
