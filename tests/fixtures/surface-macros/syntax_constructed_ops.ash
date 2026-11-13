import @builtin.compiler.syntax as Syntax

pub syntax bind_fresh $initial:expr in $body:expr => using expand_fresh
pub syntax bind_caller $initial:expr in $body:expr => using expand_caller
pub syntax use_private $value:expr => using expand_private

expand_fresh : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_fresh input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.fresh_identifier(input, "let", origin) {
        Syntax.InvalidIdentifier => match Syntax.fresh_identifier(input, "syntax", origin) {
            Syntax.InvalidIdentifier => fresh_name(input, origin)
            _ => Syntax.Rejected(Syntax.MacroDiagnostic("reserved syntax accepted", origin, Syntax.NoOrigins))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid identifier accepted", origin, Syntax.NoOrigins))
    }
}

fresh_name : (Syntax.Input, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
fresh_name (input, origin) = match Syntax.fresh_identifier(input, "temp", origin) {
    Syntax.MadeIdentifier(name) => get_initial(input, name, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("fresh name failed", origin, Syntax.NoOrigins))
}

expand_caller : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_caller input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.caller_identifier(input, "item", origin) {
        Syntax.MadeIdentifier(name) => get_initial(input, name, origin)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("caller name failed", origin, Syntax.NoOrigins))
    }
}

get_initial : (Syntax.Input, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
get_initial (input, name, origin) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(initial)) => get_body(input, name, initial, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing initializer", origin, Syntax.NoOrigins))
}

get_body : (Syntax.Input, Syntax.Identifier, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
get_body (input, name, initial, origin) = match Syntax.capture(input, 1) {
    Syntax.Captured(Syntax.ExpressionCapture(body)) => make_let(name, initial, body, origin)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing body", origin, Syntax.NoOrigins))
}

make_let : (Syntax.Identifier, Syntax.ExpressionFragment, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_let (name, initial, body, origin) = match Syntax.make_token(Syntax.Let, "let") {
    Syntax.MadeToken(let_token) => make_equal(name, initial, body, origin, let_token)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid let", origin, Syntax.NoOrigins))
}

make_equal : (Syntax.Identifier, Syntax.ExpressionFragment, Syntax.ExpressionFragment, Syntax.Origin, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
make_equal (name, initial, body, origin, let_token) = match Syntax.make_token(Syntax.Equal, "=") {
    Syntax.MadeToken(equal) => make_plus(name, initial, body, origin, let_token, equal)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid equal", origin, Syntax.NoOrigins))
}

make_plus : (Syntax.Identifier, Syntax.ExpressionFragment, Syntax.ExpressionFragment, Syntax.Origin, Syntax.Token, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
make_plus (name, initial, body, origin, let_token, equal) = match Syntax.make_token(Syntax.Plus, "+") {
    Syntax.MadeToken(plus) => make_line(name, initial, body, origin, let_token, equal, plus)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid plus", origin, Syntax.NoOrigins))
}

make_line : (Syntax.Identifier, Syntax.ExpressionFragment, Syntax.ExpressionFragment, Syntax.Origin, Syntax.Token, Syntax.Token, Syntax.Token) -> Syntax.MacroResult ! {Syntax.Ops}
make_line (name, initial, body, origin, let_token, equal, plus) = match Syntax.make_token(Syntax.LineEnd, "\n") {
    Syntax.MadeToken(line) => {
        let tail = Syntax.MoreNodes(Syntax.TokenNode(line, origin), Syntax.NoNodes)
        let name_ref = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), tail)
        let add = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), name_ref)
        let body_nodes = Syntax.MoreNodes(Syntax.ExpressionNode(body, origin), add)
        let after_initial = Syntax.MoreNodes(Syntax.TokenNode(line, origin), body_nodes)
        let initial_nodes = Syntax.MoreNodes(Syntax.ExpressionNode(initial, origin), after_initial)
        let equal_nodes = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), initial_nodes)
        let name_nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, origin), equal_nodes)
        let let_nodes = Syntax.MoreNodes(Syntax.TokenNode(let_token, origin), name_nodes)
        let block_nodes = Syntax.MoreNodes(Syntax.TokenNode(line, origin), let_nodes)
        let group = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(block_nodes), origin)
        let nodes = Syntax.MoreNodes(group, Syntax.NoNodes)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("invalid line", origin, Syntax.NoOrigins))
}

private_increment : Int -> Int
private_increment value = value + 1

expand_private : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_private input = {
    let invocation = Syntax.invocation_origin(input)
    match Syntax.definition_identifier(input, "private_increment", invocation) {
        Syntax.MadeIdentifier(name) => private_argument(input, name, invocation, invocation)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("definition name failed", invocation, Syntax.NoOrigins))
    }
}

private_argument : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
private_argument (input, name, definition, invocation) = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => {
        let tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, invocation), Syntax.NoNodes)
        let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(name, definition), tail)
        Syntax.Expanded(Syntax.Syntax(nodes))
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing value", invocation, Syntax.NoOrigins))
}
