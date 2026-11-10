import @builtin.compiler.syntax as Syntax

pub syntax blocked $body:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = Syntax.Rejected(Syntax.MacroDiagnostic("transformer executed", Syntax.invocation_origin(input), Syntax.NoOrigins))
