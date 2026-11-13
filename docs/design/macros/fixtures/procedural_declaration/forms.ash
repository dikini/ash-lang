import @builtin.compiler.syntax as Syntax

pub syntax declaration: (identity_declaration) $item:declaration => using expand
pub syntax declaration: (reject_declaration) $item:declaration => using reject

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.DeclarationCapture(item)) => Syntax.Expanded(Syntax.declaration_syntax(item))
    _ => reject(input)
}

reject : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject input = Syntax.Rejected(Syntax.MacroDiagnostic("declaration rejected", Syntax.invocation_origin(input), Syntax.NoOrigins))
