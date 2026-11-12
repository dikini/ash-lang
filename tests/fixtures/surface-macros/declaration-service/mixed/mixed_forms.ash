import @builtin.compiler.syntax as Syntax

value : Unit -> Int
value () = 1

pub syntax declaration: (emit_repeated) { $( $name:ident matching $pattern:pattern as $T:type yields $body:expr );+ } => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 0), Syntax.capture(input, 1), Syntax.capture(input, 2), Syntax.capture(input, 3)) {
        (Syntax.Captured(Syntax.RepeatedCapture(Syntax.MoreCaptures(Syntax.IdentifierCapture(name, name_origin), Syntax.NoCaptures))), Syntax.Captured(Syntax.RepeatedCapture(Syntax.MoreCaptures(Syntax.PatternCapture(pattern), Syntax.NoCaptures))), Syntax.Captured(Syntax.RepeatedCapture(Syntax.MoreCaptures(Syntax.TypeCapture(ty), Syntax.NoCaptures))), Syntax.Captured(Syntax.RepeatedCapture(Syntax.MoreCaptures(Syntax.ExpressionCapture(body), Syntax.NoCaptures)))) => parse_pattern(input, name, name_origin, pattern, ty, body, origin)
        _ => reject(origin)
    }
}

reject : Syntax.Origin -> Syntax.MacroResult
reject origin = Syntax.Rejected(Syntax.MacroDiagnostic("cannot emit mixed expression", origin, Syntax.NoOrigins))

parse_pattern : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.PatternFragment, Syntax.TypeFragment, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_pattern (input, name, name_origin, pattern, ty, body, origin) = match Syntax.parse_pattern(input, Syntax.pattern_syntax(pattern)) {
    Syntax.ParsedPattern(parsed) => parse_type(input, name, name_origin, parsed, ty, body, origin)
    _ => reject(origin)
}

parse_type : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.PatternFragment, Syntax.TypeFragment, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_type (input, name, name_origin, pattern, ty, body, origin) = match Syntax.parse_type(input, Syntax.type_syntax(ty)) {
    Syntax.ParsedType(parsed) => parse_expression(input, name, name_origin, pattern, parsed, body, origin)
    _ => reject(origin)
}

parse_expression : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.PatternFragment, Syntax.TypeFragment, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_expression (input, name, name_origin, pattern, ty, body, origin) = match Syntax.parse_expression(input, Syntax.expression_syntax(body)) {
    Syntax.Parsed(parsed) => tokens(name, name_origin, pattern, ty, parsed, origin)
    _ => reject(origin)
}

tokens : (Syntax.Identifier, Syntax.Origin, Syntax.PatternFragment, Syntax.TypeFragment, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
tokens (name, name_origin, pattern, ty, body, origin) = match (Syntax.make_token(Syntax.Pub, "pub"), Syntax.make_token(Syntax.Colon, ":"), Syntax.make_token(Syntax.Arrow, "->"), Syntax.make_token(Syntax.LineEnd, "\n"), Syntax.make_token(Syntax.Equal, "=")) {
    (Syntax.MadeToken(public), Syntax.MadeToken(colon), Syntax.MadeToken(arrow), Syntax.MadeToken(line), Syntax.MadeToken(equal)) => {
        let end = Syntax.MoreNodes(Syntax.ExpressionNode(body, origin), Syntax.NoNodes)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), end)
        let equation = Syntax.MoreNodes(Syntax.PatternNode(pattern, origin), equation)
        let equation = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), equation)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(line, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TypeNode(ty, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(arrow, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TypeNode(ty, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(colon, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(public, origin), signature)
        Syntax.Expanded(Syntax.Syntax(signature))
    }
    _ => reject(origin)
}
