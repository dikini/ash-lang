import @builtin.compiler.syntax as Syntax
pub syntax observe $name:ident = $value:expr => using reject
pub syntax observe_resolve $name:ident = $value:expr => using emit
pub syntax observe_member $name:ident = $value:expr => using emit_member
pub syntax observe_alias $name:ident = $value:expr => using emit_alias
pub syntax observe_plain $name:ident = $value:expr => using emit_plain
pub syntax observe_success $name:ident = $value:expr => using emit_success
reject : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, origin)) => Syntax.Rejected(Syntax.MacroDiagnostic("identifier origin", origin, Syntax.NoOrigins))
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("capture failed", invocation, Syntax.NoOrigins))
    }
}

emit : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
emit input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, origin)) => Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), Syntax.NoNodes)))
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("capture failed", invocation, Syntax.NoOrigins))
    }
}

emit_member : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
emit_member input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, origin)) => make_qualified(input, "H", name, invocation, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("capture failed", invocation, Syntax.NoOrigins))
    }
}

emit_alias : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
emit_alias input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, origin)) => make_qualified(input, "Missing", name, origin, invocation)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("capture failed", invocation, Syntax.NoOrigins))
    }
}

emit_plain : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
emit_plain input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, ignored)) => make_qualified(input, "H", name, invocation, invocation)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("capture failed", invocation, Syntax.NoOrigins))
    }
}

emit_success : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
emit_success input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.IdentifierCapture(name, origin)) => make_qualified(input, "Success", name, invocation, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("capture failed", invocation, Syntax.NoOrigins))
    }
}

make_qualified : (Syntax.Input, String, Syntax.Identifier, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_qualified (input, spelling, name, alias_origin, member_origin) = match (Syntax.caller_identifier(input, spelling, alias_origin), Syntax.make_token(Syntax.Dot, "."), Syntax.make_token(Syntax.True, "true")) {
    (Syntax.MadeIdentifier(alias), Syntax.MadeToken(dot), Syntax.MadeToken(boolean)) => {
        let last = Syntax.MoreNodes(Syntax.IdentifierNode(name, member_origin), Syntax.MoreNodes(Syntax.TokenNode(boolean, alias_origin), Syntax.NoNodes))
        let middle = Syntax.MoreNodes(Syntax.TokenNode(dot, alias_origin), last)
        let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(alias, alias_origin), middle)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("qualified construction failed", alias_origin, Syntax.NoOrigins))
}

pub syntax observe_type $name:ident = $value:expr => {
    let x : $name = $value
    42
}

pub syntax observe_tuple $name:ident = $value:expr => {
    let x : ($name, Bool) = $value
    42
}
