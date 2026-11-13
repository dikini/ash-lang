import @builtin.compiler.syntax as Syntax

pub syntax declaration: (round_trip) $item:declaration => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.DeclarationCapture(item)) => match Syntax.parse_declaration(input, Syntax.declaration_syntax(item)) {
            Syntax.ParsedDeclaration(parsed) => {
                let origin = Syntax.invocation_origin(input)
                Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(Syntax.DeclarationNode(parsed, origin), Syntax.NoNodes)))
            }
            Syntax.ParseRejected(failure) => Syntax.Rejected(Syntax.SyntaxDiagnostic(failure))
            _ => reject(input)
        }
    _ => reject(input)
}

reject : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject input = Syntax.Rejected(Syntax.MacroDiagnostic("unexpected capture or parse result", Syntax.invocation_origin(input), Syntax.NoOrigins))
