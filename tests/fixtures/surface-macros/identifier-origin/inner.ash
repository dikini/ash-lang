import @builtin.compiler.syntax as Syntax
pub syntax observe $name:ident = $value:expr => using reject
reject : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, origin)) => Syntax.Rejected(Syntax.MacroDiagnostic("identifier origin", origin, Syntax.NoOrigins))
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("capture failed", invocation, Syntax.NoOrigins))
    }
}
