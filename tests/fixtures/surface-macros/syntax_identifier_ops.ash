import @builtin.compiler.syntax as Syntax
import @builtin.string as Text

pub syntax pick $name:ident in $ignored:expr => using expand_pick

expand_pick : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_pick input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, origin)) => inspect_name(name, origin, invocation)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing identifier", invocation, Syntax.NoOrigins))
    }
}

inspect_name : (Syntax.Identifier, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
inspect_name (name, origin, invocation) = match Text.equal(Syntax.identifier_spelling(name), "temp") {
    true => {
        let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), Syntax.NoNodes)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    false => Syntax.Rejected(Syntax.MacroDiagnostic("unexpected spelling", invocation, Syntax.NoOrigins))
}
