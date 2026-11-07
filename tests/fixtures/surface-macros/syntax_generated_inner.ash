import @builtin.compiler.syntax as Syntax

pub syntax bump $value:expr => {
    $value + 1
}

pub syntax bomb $value:expr => using reject

reject : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject input = {
    let origin = Syntax.invocation_origin(input)
    Syntax.Rejected(Syntax.MacroDiagnostic("the discarded syntax ran", origin, Syntax.NoOrigins))
}
