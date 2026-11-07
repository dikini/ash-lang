import @builtin.compiler.syntax as Syntax
pub syntax probe $value:expr => using expand
expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 1) {
        Syntax.MissingCapture => huge(input, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture accepted", origin, Syntax.NoOrigins))
    }
}
huge : (Syntax.Input, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
huge (input, origin) = match Syntax.capture(input, 18446744073709551616000000000000000000) {
    Syntax.MissingCapture => identifier(input, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("huge capture accepted", origin, Syntax.NoOrigins))
}
identifier : (Syntax.Input, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
identifier (input, origin) = match Syntax.fresh_identifier(input, "let", origin) {
    Syntax.InvalidIdentifier => token(input, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid identifier accepted", origin, Syntax.NoOrigins))
}
token : (Syntax.Input, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
token (input, origin) = match Syntax.make_token(Syntax.Plus, "*") {
    Syntax.InvalidToken => origins(input, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid token accepted", origin, Syntax.NoOrigins))
}
origins : (Syntax.Input, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
origins (input, origin) = match Syntax.combine_origins(input, Syntax.NoOrigins) {
    Syntax.MissingOrigins => value(input, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("empty origin accepted", origin, Syntax.NoOrigins))
}
value : (Syntax.Input, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
value (input, origin) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)))
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing value", origin, Syntax.NoOrigins))
}
