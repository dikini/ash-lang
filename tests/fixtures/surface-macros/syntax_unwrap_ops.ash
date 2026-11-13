import @builtin.compiler.syntax as Syntax

pub syntax unwrap $value:expr => using expand_unwrap
pub syntax protected $value:expr => using expand_protected
pub syntax reparsed $value:expr => using expand_reparsed

expand_unwrap : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_unwrap input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.ExpressionCapture(value)) => emit(Syntax.expression_syntax(value), origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", origin, Syntax.NoOrigins))
    }
}

expand_protected : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_protected input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.ExpressionCapture(value)) => {
            let nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
            emit(Syntax.Syntax(nodes), origin)
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", origin, Syntax.NoOrigins))
    }
}

expand_reparsed : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_reparsed input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.ExpressionCapture(value)) => {
            let nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
            match Syntax.parse_expression(input, Syntax.Syntax(nodes)) {
                Syntax.Parsed(parsed) => emit(Syntax.expression_syntax(parsed), origin)
                _ => Syntax.Rejected(Syntax.MacroDiagnostic("parse failed", origin, Syntax.NoOrigins))
            }
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", origin, Syntax.NoOrigins))
    }
}

emit : (Syntax.Syntax, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
emit (syntax_value, origin) = match Syntax.make_token(Syntax.Star, "*") {
    Syntax.MadeToken(star) => emit_ten(syntax_value, origin, star)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid star", origin, Syntax.NoOrigins))
}

emit_ten : (Syntax.Syntax, Syntax.Origin, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
emit_ten (syntax_value, origin, star) = match Syntax.make_token(Syntax.IntegerLiteral, "10") {
    Syntax.MadeToken(ten) => match syntax_value {
        Syntax.Syntax(nodes) => {
            let tail = Syntax.MoreNodes(Syntax.TokenNode(ten, origin), Syntax.NoNodes)
            let suffix = Syntax.MoreNodes(Syntax.TokenNode(star, origin), tail)
            Syntax.Expanded(Syntax.Syntax(append(nodes, suffix)))
        }
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid integer", origin, Syntax.NoOrigins))
}

append : (Syntax.Nodes, Syntax.Nodes) -> Syntax.Nodes
append (left, right) = match left {
    Syntax.NoNodes => right
    Syntax.MoreNodes(head, tail) => Syntax.MoreNodes(head, append(tail, right))
}
