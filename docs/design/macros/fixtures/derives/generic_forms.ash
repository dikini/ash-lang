import @builtin.compiler.syntax as Syntax
import api (Marker, mark)

pub syntax derive: (generic_marker) $target:ident => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 1), Syntax.fresh_identifier(input, "A", origin), Syntax.definition_identifier(input, "Marker", origin), Syntax.definition_identifier(input, "mark", origin)) {
        (Syntax.Captured(Syntax.IdentifierCapture(target, _)), Syntax.MadeIdentifier(parameter), Syntax.MadeIdentifier(interface_name), Syntax.MadeIdentifier(method_name)) => tokens(target, parameter, interface_name, method_name, origin)
        _ => reject(origin)
    }
}

reject : Syntax.Origin -> Syntax.MacroResult
reject origin = Syntax.Rejected(Syntax.MacroDiagnostic("cannot construct generic marker implementation", origin, Syntax.NoOrigins))

tokens : (Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
tokens (target, parameter, interface_name, method_name, origin) = match (Syntax.make_token(Syntax.Impl, "impl"), Syntax.make_token(Syntax.Less, "<"), Syntax.make_token(Syntax.Greater, ">"), Syntax.make_token(Syntax.Wildcard, "_"), Syntax.make_token(Syntax.Equal, "="), Syntax.make_token(Syntax.True, "true"), Syntax.make_token(Syntax.LineEnd, "\n")) {
    (Syntax.MadeToken(impl_token), Syntax.MadeToken(less), Syntax.MadeToken(greater), Syntax.MadeToken(wildcard), Syntax.MadeToken(equals), Syntax.MadeToken(true_token), Syntax.MadeToken(line)) => build(target, parameter, interface_name, method_name, origin, impl_token, less, greater, wildcard, equals, true_token, line)
    _ => reject(origin)
}

build : (Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.Origin, Syntax.Token, Syntax.Token, Syntax.Token, Syntax.Token, Syntax.Token, Syntax.Token, Syntax.Token) -> Syntax.MacroResult
build (target, parameter, interface_name, method_name, origin, impl_token, less, greater, wildcard, equals, true_token, line) = {
    let body = Syntax.MoreNodes(Syntax.TokenNode(line, origin), Syntax.NoNodes)
    let body = Syntax.MoreNodes(Syntax.TokenNode(true_token, origin), body)
    let body = Syntax.MoreNodes(Syntax.TokenNode(equals, origin), body)
    let body = Syntax.MoreNodes(Syntax.TokenNode(wildcard, origin), body)
    let body = Syntax.MoreNodes(Syntax.IdentifierNode(method_name, origin), body)
    let body = Syntax.MoreNodes(Syntax.TokenNode(line, origin), body)
    let group = Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(body), origin)
    let nodes = Syntax.MoreNodes(group, Syntax.NoNodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(greater, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(greater, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(parameter, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(less, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(target, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(less, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(interface_name, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(greater, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(parameter, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(less, origin), nodes)
    let nodes = Syntax.MoreNodes(Syntax.TokenNode(impl_token, origin), nodes)
    Syntax.Expanded(Syntax.Syntax(nodes))
}
