import @builtin.compiler.syntax as Syntax

pub syntax declaration_output $name:ident from $value:expr => using expand
pub syntax declaration_overflow $name:ident from $value:expr => using expand_overflow
pub syntax parse_overflow $value:expr => using expand_parse_overflow

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = make_output(input, false)

expand_overflow : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_overflow input = make_output(input, true)

make_output : (Syntax.Input, Bool) -> Syntax.MacroResult ! {Syntax.Ops}
make_output (input, overflow) = {
    let origin = Syntax.invocation_origin(input)
    match (Syntax.capture(input, 0), Syntax.capture(input, 1), Syntax.make_token(Syntax.Plus, "+"), Syntax.make_token(Syntax.Colon, ":"), Syntax.make_token(Syntax.UnitType, "Unit"), Syntax.make_token(Syntax.Arrow, "->"), Syntax.make_token(Syntax.IntType, "Int"), Syntax.make_token(Syntax.LineEnd, "\n"), Syntax.make_token(Syntax.Equal, "=")) {
        (Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)), Syntax.Captured(Syntax.ExpressionCapture(value)), Syntax.MadeToken(plus), Syntax.MadeToken(colon), Syntax.MadeToken(unit), Syntax.MadeToken(arrow), Syntax.MadeToken(integer), Syntax.MadeToken(line), Syntax.MadeToken(equal)) => {
            let inner_tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
            let inner_operator = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), inner_tail)
            let inner_nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), inner_operator)
            let inner = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(inner_nodes), origin)
            let middle_tail = Syntax.MoreNodes(inner, Syntax.NoNodes)
            let middle_operator = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), middle_tail)
            let middle_nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), middle_operator)
            let middle = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(middle_nodes), origin)
            let expression_tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
            let expression_operator = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), expression_tail)
            let expression = Syntax.Syntax(Syntax.MoreNodes(middle, expression_operator))
            match Syntax.parse_expression(input, expression) {
                Syntax.Parsed(parsed) => match Syntax.expression_syntax(parsed) {
                    Syntax.Syntax(body) => {
                        let tail = match overflow {
                            true => Syntax.MoreNodes(Syntax.TokenNode(line, origin), Syntax.MoreNodes(group(0, origin), Syntax.NoNodes))
                            false => Syntax.NoNodes
                        }
                        let body = append(body, tail)
                        let equation_body = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), body)
                        let parameter = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.NoNodes), origin)
                        let equation_parameter = Syntax.MoreNodes(parameter, equation_body)
                        let equation = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), equation_parameter)
                        let separator = Syntax.MoreNodes(Syntax.TokenNode(line, origin), equation)
                        let result = Syntax.MoreNodes(Syntax.TokenNode(integer, origin), separator)
                        let function_arrow = Syntax.MoreNodes(Syntax.TokenNode(arrow, origin), result)
                        let domain = Syntax.MoreNodes(Syntax.TokenNode(unit, origin), function_arrow)
                        let annotation = Syntax.MoreNodes(Syntax.TokenNode(colon, origin), domain)
                        let output = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), annotation)
                        Syntax.Expanded(Syntax.Syntax(output))
                    }
                }
                _ => Syntax.Rejected(Syntax.MacroDiagnostic("expression parse failed", origin, Syntax.NoOrigins))
            }
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing output input", origin, Syntax.NoOrigins))
    }
}

append : (Syntax.Nodes, Syntax.Nodes) -> Syntax.Nodes
append (left, right) = match left {
    Syntax.NoNodes => right
    Syntax.MoreNodes(node, rest) => Syntax.MoreNodes(node, append(rest, right))
}

expand_parse_overflow : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_parse_overflow input = {
    let origin = Syntax.invocation_origin(input)
    let earlier = group(127, origin)
    let too_deep = group(0, origin)
    let nodes = Syntax.MoreNodes(earlier, Syntax.MoreNodes(too_deep, Syntax.NoNodes))
    match Syntax.parse_expression(input, Syntax.Syntax(nodes)) {
        Syntax.Parsed(_) => Syntax.Rejected(Syntax.MacroDiagnostic("over-depth parse succeeded", origin, Syntax.NoOrigins))
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("over-depth parse rejected", origin, Syntax.NoOrigins))
    }
}

group : (Int, Syntax.Origin) -> Syntax.Node
group (depth, origin) = match depth == 130 {
    true => Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.NoNodes), origin)
    false => {
        let inner = group(depth + 1, origin)
        Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.MoreNodes(inner, Syntax.NoNodes)), origin)
    }
}
