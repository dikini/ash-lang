import @builtin.compiler.syntax as Syntax

pub syntax declaration: (check_pattern_parse) $name:ident matching $pattern:pattern yields $read:ident as $T:type => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 0), Syntax.capture(input, 1), Syntax.capture(input, 2), Syntax.capture(input, 3)) {
        (Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)), Syntax.Captured(Syntax.PatternCapture(pattern)), Syntax.Captured(Syntax.IdentifierCapture(read, read_origin)), Syntax.Captured(Syntax.TypeCapture(result))) => parse_result(input, name, name_origin, pattern, read, read_origin, result, origin)
        _ => reject(origin)
    }
}

reject : Syntax.Origin -> Syntax.MacroResult
reject origin = Syntax.Rejected(Syntax.MacroDiagnostic("cannot emit pattern", origin, Syntax.NoOrigins))

parse_result : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.PatternFragment, Syntax.Identifier, Syntax.Origin, Syntax.TypeFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_result (input, name, name_origin, pattern, read, read_origin, result, origin) = {
    let wrong_type = Syntax.Syntax(Syntax.MoreNodes(Syntax.PatternNode(pattern, origin), Syntax.NoNodes))
    let wrong_pattern = Syntax.Syntax(Syntax.MoreNodes(Syntax.TypeNode(result, origin), Syntax.NoNodes))
    let extra_pattern = Syntax.Syntax(Syntax.MoreNodes(Syntax.IdentifierNode(read, read_origin), Syntax.MoreNodes(Syntax.IdentifierNode(read, read_origin), Syntax.NoNodes)))
    let extra_type = Syntax.Syntax(Syntax.MoreNodes(Syntax.TypeNode(result, origin), Syntax.MoreNodes(Syntax.TypeNode(result, origin), Syntax.NoNodes)))
    match (Syntax.parse_type(input, wrong_type), Syntax.parse_pattern(input, wrong_pattern), Syntax.parse_pattern(input, extra_pattern), Syntax.parse_type(input, extra_type)) {
        (Syntax.ParseRejected(_), Syntax.ParseRejected(_), Syntax.ParseRejected(_), Syntax.ParseRejected(_)) => match Syntax.parse_pattern(input, Syntax.pattern_syntax(pattern)) {
            Syntax.ParsedPattern(parsed) => tokens(name, name_origin, parsed, read, read_origin, result, origin)
            _ => reject(origin)
        }
        _ => reject(origin)
    }
}

tokens : (Syntax.Identifier, Syntax.Origin, Syntax.PatternFragment, Syntax.Identifier, Syntax.Origin, Syntax.TypeFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
tokens (name, name_origin, pattern, read, read_origin, result, origin) = match (Syntax.make_token(Syntax.Pub, "pub"), Syntax.make_token(Syntax.Colon, ":"), Syntax.make_token(Syntax.Arrow, "->"), Syntax.make_token(Syntax.LineEnd, "\n"), Syntax.make_token(Syntax.Equal, "=")) {
    (Syntax.MadeToken(public), Syntax.MadeToken(colon), Syntax.MadeToken(arrow), Syntax.MadeToken(line), Syntax.MadeToken(equal)) => {
        let end = Syntax.MoreNodes(Syntax.IdentifierNode(read, read_origin), Syntax.NoNodes)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), end)
        let equation = Syntax.MoreNodes(Syntax.PatternNode(pattern, origin), equation)
        let equation = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), equation)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(line, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TypeNode(result, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(arrow, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TypeNode(result, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(colon, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(public, origin), signature)
        Syntax.Expanded(Syntax.Syntax(signature))
    }
    _ => reject(origin)
}
