import @builtin.compiler.syntax as Syntax

pub syntax refuse $value:expr => using expand_refuse

expand_refuse : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_refuse input = {
    let invocation = Syntax.invocation_origin(input)
    let definition = Syntax.definition_origin(input)
    let tail = Syntax.MoreOrigins(definition, Syntax.NoOrigins)
    let inputs = Syntax.MoreOrigins(invocation, tail)
    match Syntax.combine_origins(input, inputs) {
        Syntax.Combined(primary) => Syntax.Rejected(Syntax.MacroDiagnostic("expected a positive value", primary, tail))
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("origin combination failed", invocation, Syntax.NoOrigins))
    }
}
