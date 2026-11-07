import @builtin.compiler.syntax as Syntax
import actual (increment as adjust)

pub syntax call_procedural $value:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.definition_identifier(input, "adjust", origin) {
        Syntax.MadeIdentifier(name) => argument(input, name, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid name", origin, Syntax.NoOrigins))
    }
}

argument : (Syntax.Input, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
argument (input, name, origin) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => {
        let tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
        let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), tail)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing value", origin, Syntax.NoOrigins))
}
