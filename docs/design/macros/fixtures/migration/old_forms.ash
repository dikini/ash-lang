import @builtin.compiler.syntax as Syntax

pub syntax identity $value:expr => using expand

classify : Syntax.Capture -> Int
classify (Syntax.ExpressionCapture(_)) = 1
classify (Syntax.IdentifierCapture(_, _)) = 2

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(captured) => match captured {
            Syntax.ExpressionCapture(value) => match classify(captured) == 1 {
                true => Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)))
                false => Syntax.Rejected(Syntax.MacroDiagnostic("unexpected expression classification", origin, Syntax.NoOrigins))
            }
            _ => Syntax.Rejected(Syntax.MacroDiagnostic("expected expression", origin, Syntax.NoOrigins))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", origin, Syntax.NoOrigins))
    }
}
