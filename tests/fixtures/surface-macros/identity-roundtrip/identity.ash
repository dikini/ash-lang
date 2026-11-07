import @builtin.compiler.syntax as Syntax

pub syntax identity $value:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => Syntax.Expanded(Syntax.expression_syntax(value))
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", Syntax.invocation_origin(input), Syntax.NoOrigins))
}
