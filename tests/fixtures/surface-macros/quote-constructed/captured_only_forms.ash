import @builtin.compiler.syntax as Syntax
import identity (syntax identity)

pub syntax declaration: (make_quote) $name:ident => using build

build : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
build input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)) => names(input, name, name_origin)
    _ => reject(Syntax.invocation_origin(input))
}

names : (Syntax.Input, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
names (input, name, name_origin) = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.definition_identifier(input, "Syntax", origin), Syntax.definition_identifier(input, "ExpressionFragment", origin), Syntax.definition_identifier(input, "Ops", origin), Syntax.fresh_identifier(input, "fragment", origin), Syntax.definition_identifier(input, "identity", origin)) {
        (Syntax.MadeIdentifier(qualifier), Syntax.MadeIdentifier(fragment_type), Syntax.MadeIdentifier(ops), Syntax.MadeIdentifier(binder), Syntax.MadeIdentifier(wrapper)) => tokens(name, name_origin, qualifier, fragment_type, ops, binder, wrapper, origin)
        _ => reject(origin)
    }
}

tokens : (Syntax.Identifier, Syntax.Origin, Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.Identifier, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
tokens (name, name_origin, qualifier, fragment_type, ops, binder, wrapper, origin) = match (Syntax.make_token(Syntax.Pub, "pub"), Syntax.make_token(Syntax.Colon, ":"), Syntax.make_token(Syntax.Dot, "."), Syntax.make_token(Syntax.Arrow, "->"), Syntax.make_token(Syntax.Bang, "!"), Syntax.make_token(Syntax.LineEnd, "\n"), Syntax.make_token(Syntax.Equal, "="), Syntax.make_token(Syntax.SyntaxKeyword, "syntax"), Syntax.make_token(Syntax.Dollar, "$")) {
    (Syntax.MadeToken(public), Syntax.MadeToken(colon), Syntax.MadeToken(dot), Syntax.MadeToken(arrow), Syntax.MadeToken(bang), Syntax.MadeToken(line), Syntax.MadeToken(equal), Syntax.MadeToken(keyword), Syntax.MadeToken(dollar)) => {
        let hole = Syntax.MoreNodes(Syntax.IdentifierNode(binder, origin), Syntax.NoNodes)
        let hole = Syntax.MoreNodes(Syntax.TokenNode(dollar, origin), hole)
        let body = Syntax.MoreNodes(Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(hole), origin), Syntax.NoNodes)
        let body = Syntax.MoreNodes(Syntax.TokenNode(keyword, origin), body)
        let body = Syntax.MoreNodes(Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(body), origin), Syntax.NoNodes)
        let body = Syntax.MoreNodes(Syntax.IdentifierNode(wrapper, origin), body)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), body)
        let equation = Syntax.MoreNodes(Syntax.IdentifierNode(binder, origin), equation)
        let equation = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), equation)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(line, origin), equation)
        let effects = Syntax.MoreNodes(Syntax.IdentifierNode(ops, origin), Syntax.NoNodes)
        let effects = Syntax.MoreNodes(Syntax.TokenNode(dot, origin), effects)
        let effects = Syntax.MoreNodes(Syntax.IdentifierNode(qualifier, origin), effects)
        let signature = Syntax.MoreNodes(Syntax.GroupNode(Syntax.Braces, Syntax.Syntax(effects), origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(bang, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(fragment_type, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(dot, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(qualifier, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(arrow, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(fragment_type, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(dot, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(qualifier, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(colon, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(public, origin), signature)
        Syntax.Expanded(Syntax.Syntax(signature))
    }
    _ => reject(origin)
}

reject : Syntax.Origin -> Syntax.MacroResult
reject origin = Syntax.Rejected(Syntax.MacroDiagnostic("could not construct quoted declaration", origin, Syntax.NoOrigins))
