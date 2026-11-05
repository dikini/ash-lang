import @builtin.compiler.syntax as Syntax
import syntax_generated_inner (syntax bump, syntax bomb)
import syntax_unwrap_ops (syntax unwrap)

pub syntax generated $value:expr => using expand_generated
pub syntax generated_caller $value:expr => using expand_caller
pub syntax generated_fresh $value:expr => using expand_fresh
pub syntax parsed_discard $value:expr => using expand_discard
pub syntax nested_unwrap $value:expr => using expand_nested_unwrap

expand_generated : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_generated input = {
    let invocation = Syntax.invocation_origin(input)
    let definition = Syntax.definition_origin(input)
    match Syntax.definition_identifier(input, "bump", definition) {
        Syntax.MadeIdentifier(name) => emit_nested(input, name, definition, invocation)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid name", invocation, Syntax.NoOrigins))
    }
}

expand_nested_unwrap : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_nested_unwrap input = {
    let invocation = Syntax.invocation_origin(input)
    let definition = Syntax.definition_origin(input)
    match Syntax.definition_identifier(input, "unwrap", definition) {
        Syntax.MadeIdentifier(name) => emit_nested(input, name, definition, invocation)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid name", invocation, Syntax.NoOrigins))
    }
}

expand_caller : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_caller input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.caller_identifier(input, "bump", invocation) {
        Syntax.MadeIdentifier(name) => emit_nested(input, name, invocation, invocation)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid caller name", invocation, Syntax.NoOrigins))
    }
}

expand_fresh : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_fresh input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.fresh_identifier(input, "bump", invocation) {
        Syntax.MadeIdentifier(name) => emit_nested(input, name, invocation, invocation)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid fresh name", invocation, Syntax.NoOrigins))
    }
}

expand_discard : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_discard input = {
    let invocation = Syntax.invocation_origin(input)
    let definition = Syntax.definition_origin(input)
    match Syntax.definition_identifier(input, "bomb", definition) {
        Syntax.MadeIdentifier(name) => parse_discard(input, name, definition, invocation)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid name", invocation, Syntax.NoOrigins))
    }
}

parse_discard : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_discard (input, name, definition, invocation) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => {
        let tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, invocation), Syntax.NoNodes)
        let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, definition), tail)
        match Syntax.parse_expression(input, Syntax.Syntax(nodes)) {
            Syntax.Parsed(_) => make_result(invocation)
            _ => Syntax.Rejected(Syntax.MacroDiagnostic("nested parse failed", invocation, Syntax.NoOrigins))
        }
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", invocation, Syntax.NoOrigins))
}

make_result : Syntax.Origin -> Syntax.MacroResult ! {Syntax.Ops}
make_result origin = match Syntax.make_token(Syntax.IntegerLiteral, "42") {
    Syntax.MadeToken(token) => {
        let nodes = Syntax.MoreNodes(Syntax.TokenNode(token, origin), Syntax.NoNodes)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid result", origin, Syntax.NoOrigins))
}

emit_nested : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
emit_nested (input, name, definition, invocation) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => {
        let tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, invocation), Syntax.NoNodes)
        let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, definition), tail)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing capture", invocation, Syntax.NoOrigins))
}
