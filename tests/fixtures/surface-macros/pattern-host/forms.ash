import @builtin.compiler.syntax as Syntax

pub syntax declaration: (emit_pattern) $name:ident matching $pattern:pattern yields $read:ident => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 0), Syntax.capture(input, 1), Syntax.capture(input, 2)) {
        (Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)), Syntax.Captured(Syntax.PatternCapture(pattern)), Syntax.Captured(Syntax.IdentifierCapture(read, read_origin))) => parse_result(input, name, name_origin, pattern, read, read_origin, origin)
        _ => reject(origin)
    }
}

reject : Syntax.Origin -> Syntax.MacroResult
reject origin = Syntax.Rejected(Syntax.MacroDiagnostic("cannot emit pattern", origin, Syntax.NoOrigins))

parse_result : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.PatternFragment, Syntax.Identifier, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_result (input, name, name_origin, pattern, read, read_origin, origin) = match Syntax.parse_pattern(input, Syntax.pattern_syntax(pattern)) {
    Syntax.ParsedPattern(parsed) => tokens(name, name_origin, parsed, read, read_origin, origin)
    _ => reject(origin)
}

tokens : (Syntax.Identifier, Syntax.Origin, Syntax.PatternFragment, Syntax.Identifier, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
tokens (name, name_origin, pattern, read, read_origin, origin) = match (Syntax.make_token(Syntax.Pub, "pub"), Syntax.make_token(Syntax.Colon, ":"), Syntax.make_token(Syntax.IntType, "Int"), Syntax.make_token(Syntax.Arrow, "->"), Syntax.make_token(Syntax.LineEnd, "\n"), Syntax.make_token(Syntax.Equal, "=")) {
    (Syntax.MadeToken(public), Syntax.MadeToken(colon), Syntax.MadeToken(int), Syntax.MadeToken(arrow), Syntax.MadeToken(line), Syntax.MadeToken(equal)) => {
        let end = Syntax.MoreNodes(Syntax.IdentifierNode(read, read_origin), Syntax.NoNodes)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), end)
        let equation = Syntax.MoreNodes(Syntax.PatternNode(pattern, origin), equation)
        let equation = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), equation)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(line, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(int, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(arrow, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(int, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(colon, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(public, origin), signature)
        Syntax.Expanded(Syntax.Syntax(signature))
    }
    _ => reject(origin)
}
