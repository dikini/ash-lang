import @builtin.compiler.syntax as Syntax

pub syntax declaration: (bad_category) $name:ident => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.make_token(Syntax.IntType, "Int") {
        Syntax.MadeToken(token) => {
            let nodes = Syntax.MoreNodes(Syntax.TokenNode(token, origin), Syntax.NoNodes)
            match Syntax.parse_type(input, Syntax.Syntax(nodes)) {
                Syntax.ParsedType(fragment) => {
                    let output = Syntax.MoreNodes(Syntax.TypeNode(fragment, origin), Syntax.NoNodes)
                    Syntax.Expanded(Syntax.Syntax(output))
                }
                _ => Syntax.Rejected(Syntax.MacroDiagnostic("cannot parse Int type", origin, Syntax.NoOrigins))
            }
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("cannot construct Int token", origin, Syntax.NoOrigins))
    }
}
