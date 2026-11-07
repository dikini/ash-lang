import @builtin.compiler.syntax as Syntax

pub syntax derive: (fail_derive) => using reject_derive
pub syntax declaration: (fail_declaration) => using reject_declaration

reject_derive : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject_derive input = Syntax.Rejected(Syntax.MacroDiagnostic("derive rejected", Syntax.invocation_origin(input), Syntax.NoOrigins))

reject_declaration : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject_declaration input = Syntax.Rejected(Syntax.MacroDiagnostic("declaration rejected", Syntax.invocation_origin(input), Syntax.NoOrigins))
