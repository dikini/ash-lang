import @builtin.compiler.syntax as Syntax

pub syntax marked $value:expr => using mark

mark : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
mark input = {
    let origin = Syntax.definition_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.ExpressionCapture(value)) => {
            let nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
            Syntax.Expanded(Syntax.Syntax(nodes))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing expression", origin, Syntax.NoOrigins))
    }
}
