import @builtin.compiler.syntax as Syntax
pub syntax combined_bad $value:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let invocation = Syntax.invocation_origin(input)
    let definition = Syntax.definition_origin(input)
    let causes = Syntax.MoreOrigins(invocation, Syntax.MoreOrigins(definition, Syntax.NoOrigins))
    match Syntax.combine_origins(input, causes) {
        Syntax.Combined(origin) => again(input, origin, invocation)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing origins", invocation, Syntax.NoOrigins))
    }
}

again : (Syntax.Input, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
again (input, origin, invocation) = {
    let causes = Syntax.MoreOrigins(origin, Syntax.MoreOrigins(invocation, Syntax.NoOrigins))
    match (Syntax.combine_origins(input, causes), Syntax.make_token(Syntax.True, "true")) {
        (Syntax.Combined(combined), Syntax.MadeToken(token)) => {
            let nodes = Syntax.MoreNodes(Syntax.TokenNode(token, combined), Syntax.NoNodes)
            Syntax.Expanded(Syntax.Syntax(nodes))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("origin or token", invocation, Syntax.NoOrigins))
    }
}
