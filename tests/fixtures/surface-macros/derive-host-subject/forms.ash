import @builtin.compiler.syntax as Syntax

pub syntax derive: (check) => using inspect

inspect : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
inspect input = match (Syntax.capture(input, 0), Syntax.capture(input, 1)) {
    (Syntax.Captured(Syntax.DeclarationCapture(_)), Syntax.MissingCapture) => Syntax.Expanded(Syntax.Syntax(Syntax.NoNodes))
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("unexpected captures", Syntax.invocation_origin(input), Syntax.NoOrigins))
}
