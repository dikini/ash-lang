import @builtin.compiler.syntax as Syntax

pub syntax declaration: (repeat_forever) $name:ident => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.caller_identifier(input, "repeat_forever", origin), Syntax.capture(input, 0), Syntax.make_token(Syntax.LineEnd, "\n")) {
        (Syntax.MadeIdentifier(macro_name), Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)), Syntax.MadeToken(line)) => {
            let tail = Syntax.MoreNodes(Syntax.TokenNode(line, origin), Syntax.NoNodes)
            let tail = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), tail)
            let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(macro_name, origin), tail)
            Syntax.Expanded(Syntax.Syntax(nodes))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("cannot construct recursive invocation", origin, Syntax.NoOrigins))
    }
}
