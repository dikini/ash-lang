import @builtin.compiler.syntax as Syntax

pub syntax too_deep $value:expr => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = {
    let origin = Syntax.invocation_origin(input)
    let earlier = group (3, origin)
    let node = group (0, origin)
    let tail = Syntax.MoreNodes(node, Syntax.NoNodes)
    Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(earlier, tail)))
}

group : (Int, Syntax.Origin) -> Syntax.Node
group (depth, origin) = match depth == 130 {
    true => Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.NoNodes), origin)
    false => {
        let inner = group (depth + 1, origin)
        Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.MoreNodes(inner, Syntax.NoNodes)), origin)
    }
}
