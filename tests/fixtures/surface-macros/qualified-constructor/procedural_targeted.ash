import @builtin.compiler.syntax as Syntax
import actual (Boxed as Wrap, unwrap)

pub syntax procedural $value:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.definition_identifier(input, "unwrap", origin) {
        Syntax.MadeIdentifier(function) => constructor(input, function, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid function", origin, Syntax.NoOrigins))
    }
}

constructor : (Syntax.Input, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
constructor (input, function, origin) = match Syntax.definition_identifier(input, "Wrap", origin) {
    Syntax.MadeIdentifier(name) => argument(input, function, name, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid constructor", origin, Syntax.NoOrigins))
}

argument : (Syntax.Input, Syntax.Identifier, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
argument (input, function, name, origin) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => {
        let payload = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
        let constructed = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), payload)
        let group = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(constructed), origin)
        let call = Syntax.MoreNodes(group, Syntax.NoNodes)
        let output = Syntax.MoreNodes(Syntax.IdentifierNode(function, origin), call)
        Syntax.Expanded(Syntax.Syntax(output))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing value", origin, Syntax.NoOrigins))
}
