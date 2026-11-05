import @builtin.compiler.syntax as Syntax

pub syntax again $value:expr => using expand
pub syntax current $ignored:expr => using current_value
pub syntax wrap $value:expr => {
    $value
}

current_value : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
current_value input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.caller_identifier(input, "item", origin) {
        Syntax.MadeIdentifier(name) => {
            let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), Syntax.NoNodes)
            Syntax.Expanded(Syntax.Syntax(nodes))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("identifier", origin, Syntax.NoOrigins))
    }
}

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.caller_identifier(input, "again", origin) {
        Syntax.MadeIdentifier(name) => emit(input, name, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("identifier", origin, Syntax.NoOrigins))
    }
}

emit : (Syntax.Input, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
emit (input, name, origin) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => {
        let tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
        let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), tail)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("capture", origin, Syntax.NoOrigins))
}
