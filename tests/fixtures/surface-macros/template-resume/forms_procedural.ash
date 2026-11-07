import @builtin.compiler.syntax as Syntax

pub syntax proceed $value:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.make_token(Syntax.Resume, "resume") {
        Syntax.MadeToken(token) => argument(input, token, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid resume", origin, Syntax.NoOrigins))
    }
}

argument : (Syntax.Input, Syntax.Token, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
argument (input, token, origin) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => {
        let tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
        let nodes = Syntax.MoreNodes(Syntax.TokenNode(token, origin), tail)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing value", origin, Syntax.NoOrigins))
}
