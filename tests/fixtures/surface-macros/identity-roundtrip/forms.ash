import @builtin.compiler.syntax as Syntax
import identity (syntax identity)

pub syntax outer $value:expr => using expand

same : Int -> Int
same value = value + 1

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let invocation = Syntax.invocation_origin(input)
    let definition = Syntax.definition_origin(input)
    let causes = Syntax.MoreOrigins(invocation, Syntax.MoreOrigins(definition, Syntax.NoOrigins))
    match Syntax.combine_origins(input, causes) {
        Syntax.Combined(origin) => make_output(input, invocation, definition, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("combine failed", invocation, Syntax.NoOrigins))
    }
}

make_output : (Syntax.Input, Syntax.Origin, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_output (input, invocation, definition, origin) = match (Syntax.definition_identifier(input, "identity", definition), Syntax.definition_identifier(input, "same", origin), Syntax.make_token(Syntax.IntegerLiteral, "1"), Syntax.make_token(Syntax.Plus, "+"), Syntax.capture(input, 0)) {
    (Syntax.MadeIdentifier(head), Syntax.MadeIdentifier(name), Syntax.MadeToken(one), Syntax.MadeToken(plus), Syntax.Captured(Syntax.ExpressionCapture(value))) => {
        let tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, invocation), Syntax.NoNodes)
        let add = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), tail)
        let argument = Syntax.MoreNodes(Syntax.TokenNode(one, origin), add)
        let group = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), argument)), origin)
        let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(head, definition), Syntax.MoreNodes(group, Syntax.NoNodes))
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("construction failed", invocation, Syntax.NoOrigins))
}
