import @builtin.compiler.syntax as Syntax

pub syntax derive: (repeat) => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.DeclarationCapture(subject)) => Syntax.Expanded(Syntax.declaration_syntax(subject))
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("expected declaration", Syntax.invocation_origin(input), Syntax.NoOrigins))
}
