import @builtin.compiler.syntax as Syntax

select_nodes : (Int, Int, Syntax.Nodes) -> Syntax.ExpressionFragment
select_nodes (target, index, nodes) = match nodes {
    Syntax.NoNodes => no_fragment(())
    Syntax.MoreNodes(node, rest) => match node {
        Syntax.ExpressionNode(fragment, _) => match target == index {
            true => fragment
            false => select_nodes(target, index + 1, rest)
        }
        Syntax.TokenNode(_, _) => select_nodes(target, index, rest)
        _ => no_fragment(())
    }
}

select_fragment : (Int, Syntax.ExpressionFragment) -> Syntax.ExpressionFragment ! {Syntax.Ops}
select_fragment (target, bank) = match Syntax.expression_syntax(bank) {
    Syntax.Syntax(Syntax.MoreNodes(Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(nodes), _), Syntax.NoNodes)) => select_nodes(target, 0, nodes)
    _ => no_fragment(())
}


no_fragment : Unit -> Syntax.ExpressionFragment
no_fragment () = no_fragment(())

pub syntax test_selection $first:expr and $second:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.ExpressionCapture(first)) => match Syntax.capture(input, 1) {
            Syntax.Captured(Syntax.ExpressionCapture(second)) => build(input, origin, first, second)
            _ => fail(origin)
        }
        _ => fail(origin)
    }
}

build : (Syntax.Input, Syntax.Origin, Syntax.ExpressionFragment, Syntax.ExpressionFragment) -> Syntax.MacroResult ! {Syntax.Ops}
build (input, origin, first, second) = match Syntax.make_token(Syntax.Comma, ",") {
    Syntax.MadeToken(comma) => {
        let end = Syntax.MoreNodes(Syntax.ExpressionNode(second, origin), Syntax.NoNodes)
        let middle = Syntax.MoreNodes(Syntax.TokenNode(comma, origin), end)
        let children = Syntax.Syntax(Syntax.MoreNodes(Syntax.ExpressionNode(first, origin), middle))
        let group = Syntax.GroupNode(Syntax.Parentheses, children, origin)
        let tree = Syntax.Syntax(Syntax.MoreNodes(group, Syntax.NoNodes))
        match Syntax.parse_expression(input, tree) {
            Syntax.Parsed(bank) => Syntax.Expanded(Syntax.expression_syntax(select_fragment(1, bank)))
            _ => fail(origin)
        }
    }
    _ => fail(origin)
}

fail : Syntax.Origin -> Syntax.MacroResult
fail origin = Syntax.Rejected(Syntax.MacroDiagnostic("service shape mismatch", origin, Syntax.NoOrigins))
