import @builtin.compiler.syntax as Syntax

pub syntax bomb $value:expr => using explode

explode : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
explode input = {
    let origin = Syntax.invocation_origin(input)
    Syntax.Rejected(Syntax.MacroDiagnostic("should not run", origin, Syntax.NoOrigins))
}
