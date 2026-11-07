import @builtin.compiler.syntax as Syntax
import api (Indexed, index)

pub syntax derive: (indexed) $target:ident => using expand_indexed

type Constructors = NoConstructors
    | MoreConstructors(Syntax.Identifier, Syntax.Origin, Constructors)

type Scan = Scanned(Constructors)
    | Unsupported(Syntax.Origin)

expand_indexed : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_indexed input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 0), Syntax.capture(input, 1)) {
        (Syntax.Captured(Syntax.DeclarationCapture(subject)), Syntax.Captured(Syntax.IdentifierCapture(target, _))) => inspect(input, subject, target, origin)
        _ => reject(origin)
    }
}

reject : Syntax.Origin -> Syntax.MacroResult
reject origin = Syntax.Rejected(Syntax.MacroDiagnostic("indexed requires a nongeneric type with nullary constructors", origin, Syntax.NoOrigins))

inspect : (Syntax.Input, Syntax.DeclarationFragment, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
inspect (input, subject, target, origin) = match scan_subject(subject, origin) {
    Scanned(constructors) => names(input, target, origin, constructors)
    Unsupported(location) => reject(location)
}

scan_subject : (Syntax.DeclarationFragment, Syntax.Origin) -> Scan ! {Syntax.Ops}
scan_subject (subject, origin) = match Syntax.declaration_syntax(subject) {
    Syntax.Syntax(Syntax.MoreNodes(Syntax.TokenNode(first, _), Syntax.MoreNodes(Syntax.IdentifierNode(_, _), Syntax.MoreNodes(Syntax.TokenNode(equals, _), rest)))) => match (Syntax.token_kind(first), Syntax.token_kind(equals)) {
        (Syntax.Type, Syntax.Equal) => scan_constructor(rest, origin)
        _ => Unsupported(origin)
    }
    _ => Unsupported(origin)
}

scan_constructor : (Syntax.Nodes, Syntax.Origin) -> Scan ! {Syntax.Ops}
scan_constructor (nodes, origin) = match nodes {
    Syntax.MoreNodes(Syntax.IdentifierNode(name, location), rest) => match scan_tail(rest, origin) {
        Scanned(constructors) => Scanned(MoreConstructors(name, location, constructors))
        Unsupported(location) => Unsupported(location)
    }
    _ => Unsupported(origin)
}

scan_tail : (Syntax.Nodes, Syntax.Origin) -> Scan ! {Syntax.Ops}
scan_tail (nodes, origin) = match nodes {
    Syntax.NoNodes => Scanned(NoConstructors)
    Syntax.MoreNodes(Syntax.GroupNode(_, _, location), _) => Unsupported(location)
    Syntax.MoreNodes(Syntax.TokenNode(line, _), rest) => match Syntax.token_kind(line) {
        Syntax.LineEnd => scan_after_line(rest, origin)
        _ => Unsupported(origin)
    }
    _ => Unsupported(origin)
}

scan_after_line : (Syntax.Nodes, Syntax.Origin) -> Scan ! {Syntax.Ops}
scan_after_line (nodes, origin) = match nodes {
    Syntax.NoNodes => Scanned(NoConstructors)
    Syntax.MoreNodes(Syntax.TokenNode(separator, _), rest) => match Syntax.token_kind(separator) {
        Syntax.Pipe => scan_constructor(rest, origin)
        _ => Unsupported(origin)
    }
    Syntax.MoreNodes(Syntax.IdentifierNode(_, _), Syntax.MoreNodes(Syntax.GroupNode(Syntax.Parentheses, _, _), Syntax.NoNodes)) => Scanned(NoConstructors)
    _ => Unsupported(origin)
}

names : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Constructors) -> Syntax.MacroResult ! {Syntax.Ops}
names (input, target, origin, constructors) = match (Syntax.definition_identifier(input, "Indexed", origin), Syntax.definition_identifier(input, "index", origin)) {
    (Syntax.MadeIdentifier(interface_name), Syntax.MadeIdentifier(method_name)) => tokens(target, interface_name, method_name, origin, constructors)
    _ => reject(origin)
}

tokens : (Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.Origin, Constructors) -> Syntax.MacroResult ! {Syntax.Ops}
tokens (target, interface_name, method_name, origin, constructors) = match (Syntax.make_token(Syntax.Impl, "impl"), Syntax.make_token(Syntax.Less, "<"), Syntax.make_token(Syntax.Greater, ">"), Syntax.make_token(Syntax.Equal, "="), Syntax.make_token(Syntax.IntegerLiteral, "1"), Syntax.make_token(Syntax.LineEnd, "\n")) {
    (Syntax.MadeToken(impl_token), Syntax.MadeToken(less), Syntax.MadeToken(greater), Syntax.MadeToken(equals), Syntax.MadeToken(one), Syntax.MadeToken(line)) => build(target, interface_name, method_name, origin, constructors, impl_token, less, greater, equals, one, line)
    _ => reject(origin)
}

build : (Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.Origin, Constructors, Syntax.Token, Syntax.Token, Syntax.Token, Syntax.Token, Syntax.Token, Syntax.Token) -> Syntax.MacroResult
build (target, interface_name, method_name, origin, constructors, impl_token, less, greater, equals, one, line) = {
    let body = clauses(method_name, origin, constructors, equals, one, line)
    let group = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(body), origin)
    let nodes = Syntax.MoreNodes(group, Syntax.NoNodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(greater, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(target, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(less, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(interface_name, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(impl_token, origin), nodes)
    Syntax.Expanded(Syntax.Syntax(nodes))
}

clauses : (Syntax.Identifier, Syntax.Origin, Constructors, Syntax.Token, Syntax.Token, Syntax.Token) -> Syntax.Nodes
clauses (_, origin, NoConstructors, _, _, line) = Syntax.MoreNodes(Syntax.TokenNode(line, origin), Syntax.NoNodes)
clauses (method_name, origin, MoreConstructors(name, location, rest), equals, one, line) = {
    let tail = clauses(method_name, origin, rest, equals, one, line)
    let tail = Syntax.MoreNodes(Syntax.TokenNode(one, origin), tail)
    let tail = Syntax.MoreNodes(Syntax.TokenNode(equals, origin), tail)
    let tail = Syntax.MoreNodes(Syntax.IdentifierNode(name, location), tail)
    let tail = Syntax.MoreNodes(Syntax.IdentifierNode(method_name, origin), tail)
    Syntax.MoreNodes(Syntax.TokenNode(line, origin), tail)
}
