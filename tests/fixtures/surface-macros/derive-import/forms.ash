import @builtin.compiler.syntax as Syntax

pub syntax derive: (invalid) => using return_import
pub syntax derive: (later) => using reject_later

return_import : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
return_import input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.make_token(Syntax.Import, "import"), Syntax.caller_identifier(input, "missing", origin)) {
        (Syntax.MadeToken(token), Syntax.MadeIdentifier(name)) => {
            let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), Syntax.NoNodes)
            let nodes = Syntax.MoreNodes(Syntax.TokenNode(token, origin), nodes)
            Syntax.Expanded(Syntax.Syntax(nodes))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("cannot construct import", origin, Syntax.NoOrigins))
    }
}

reject_later : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject_later input = Syntax.Rejected(Syntax.MacroDiagnostic("later rejected", Syntax.invocation_origin(input), Syntax.NoOrigins))
