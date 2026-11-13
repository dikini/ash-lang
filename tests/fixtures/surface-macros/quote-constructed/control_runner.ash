import @builtin.compiler.syntax as Syntax
import control (first, second)

pub syntax checked $value:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => Syntax.Expanded(Syntax.expression_syntax(second(first(value))))
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("expected expression", Syntax.invocation_origin(input), Syntax.NoOrigins))
}
