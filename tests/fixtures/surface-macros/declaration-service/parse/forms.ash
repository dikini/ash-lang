import @builtin.compiler.syntax as Syntax

pub syntax declaration: (parse_plain) $item:declaration => using plain
pub syntax declaration: (parse_node) $item:declaration => using node
pub syntax declaration: (parse_empty) => using empty
pub syntax declaration: (parse_two) $item:declaration => using two
pub syntax declaration: (parse_handled) $item:declaration => using handled
pub syntax declaration: (parse_discard) $item:declaration => using discard_item
pub syntax declaration: (parse_quote) $item:declaration => using inspect_quote
pub syntax boom $value:expr => using reject

plain : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
plain input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.DeclarationCapture(item)) => finish(input, Syntax.parse_declaration(input, Syntax.declaration_syntax(item)))
    _ => reject(input)
}

node : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
node input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.DeclarationCapture(item)) => {
        let origin = Syntax.invocation_origin(input)
        let syntax_value = Syntax.Syntax(Syntax.MoreNodes(Syntax.DeclarationNode(item, origin), Syntax.NoNodes))
        finish(input, Syntax.parse_declaration(input, syntax_value))
    }
    _ => reject(input)
}

empty : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
empty input = finish(input, Syntax.parse_declaration(input, Syntax.Syntax(Syntax.NoNodes)))

handled : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
handled input = match (Syntax.capture(input, 0), Syntax.parse_declaration(input, Syntax.Syntax(Syntax.NoNodes))) {
    (Syntax.Captured(Syntax.DeclarationCapture(item)), Syntax.ParseRejected(_)) => {
        let origin = Syntax.invocation_origin(input)
        Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(Syntax.DeclarationNode(item, origin), Syntax.NoNodes)))
    }
    _ => reject(input)
}

discard_item : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
discard_item input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.DeclarationCapture(item)) => match Syntax.parse_declaration(input, Syntax.declaration_syntax(item)) {
        Syntax.ParsedDeclaration(_) => Syntax.Expanded(Syntax.Syntax(Syntax.NoNodes))
        _ => reject(input)
    }
    _ => reject(input)
}

inspect_quote : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
inspect_quote input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.DeclarationCapture(item)) => match Syntax.parse_declaration(input, Syntax.declaration_syntax(item)) {
        Syntax.ParsedDeclaration(parsed) => match has_dollar(Syntax.declaration_syntax(parsed)) {
            true => Syntax.Expanded(Syntax.Syntax(Syntax.NoNodes))
            false => reject(input)
        }
        _ => reject(input)
    }
    _ => reject(input)
}

has_dollar : Syntax.Syntax -> Bool ! {Syntax.Ops}
has_dollar (Syntax.Syntax(nodes)) = has_dollar_nodes(nodes)

has_dollar_nodes : Syntax.Nodes -> Bool ! {Syntax.Ops}
has_dollar_nodes (Syntax.NoNodes) = false
has_dollar_nodes (Syntax.MoreNodes(Syntax.TokenNode(token, _), rest)) = match Syntax.token_kind(token) {
    Syntax.Dollar => true
    _ => has_dollar_nodes(rest)
}
has_dollar_nodes (Syntax.MoreNodes(Syntax.GroupNode(_, nested, _), rest)) = match has_dollar(nested) {
    true => true
    false => has_dollar_nodes(rest)
}
has_dollar_nodes (Syntax.MoreNodes(_, rest)) = has_dollar_nodes(rest)

two : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
two input = match (Syntax.capture(input, 0), Syntax.make_token(Syntax.LineEnd, "\n")) {
    (Syntax.Captured(Syntax.DeclarationCapture(item)), Syntax.MadeToken(line)) => {
        let origin = Syntax.invocation_origin(input)
        let end = Syntax.MoreNodes(Syntax.DeclarationNode(item, origin), Syntax.NoNodes)
        let rest = Syntax.MoreNodes(Syntax.TokenNode(line, origin), end)
        let syntax_value = Syntax.Syntax(Syntax.MoreNodes(Syntax.DeclarationNode(item, origin), rest))
        finish(input, Syntax.parse_declaration(input, syntax_value))
    }
    _ => reject(input)
}

finish : (Syntax.Input, Syntax.ParseResult) -> Syntax.MacroResult ! {Syntax.Ops}
finish (input, result) = match result {
    Syntax.ParsedDeclaration(item) => {
        let origin = Syntax.invocation_origin(input)
        Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(Syntax.DeclarationNode(item, origin), Syntax.NoNodes)))
    }
    Syntax.ParseRejected(failure) => Syntax.Rejected(Syntax.SyntaxDiagnostic(failure))
    _ => reject(input)
}

reject : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject input = Syntax.Rejected(Syntax.MacroDiagnostic("unexpected parse result", Syntax.invocation_origin(input), Syntax.NoOrigins))
