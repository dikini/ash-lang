import @builtin.compiler.syntax as Syntax

pub syntax derive: (first_failure) => using reject_first
pub syntax derive: (second_failure) => using reject_second

reject_first : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject_first input = Syntax.Rejected(Syntax.MacroDiagnostic("first derive rejected", Syntax.invocation_origin(input), Syntax.NoOrigins))

reject_second : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject_second input = Syntax.Rejected(Syntax.MacroDiagnostic("second derive rejected", Syntax.invocation_origin(input), Syntax.NoOrigins))
