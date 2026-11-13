import @builtin.compiler.syntax as Syntax
import helpers (test_next, test_first)

pub syntax declaration: (i17_0) $name:ident => using expand0
pub syntax declaration: (i17_1) $name:ident => using expand1
pub syntax declaration: (i17_2) $name:ident => using expand2
pub syntax declaration: (i17_3) $name:ident => using expand3
pub syntax declaration: (i17_4) $name:ident => using expand4
pub syntax declaration: (i17_5) $name:ident => using expand5

expand0 : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand0 input = evaluate(input, 0)

expand1 : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand1 input = evaluate(input, 1)

expand2 : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand2 input = evaluate(input, 2)

expand3 : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand3 input = evaluate(input, 3)

expand4 : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand4 input = evaluate(input, 4)

expand5 : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand5 input = evaluate(input, 5)

evaluate : (Syntax.Input, Int) -> Syntax.MacroResult ! {Syntax.Ops}
evaluate (input, state) = {
    let (next, digit_value) = test_next(state)
    let (first_next, first_value) = test_first(state)
    let origin = Syntax.invocation_origin(input)
    match (next == state + 1, first_next == state + 1, Syntax.capture(input, 0)) {
        (true, true, Syntax.Captured(Syntax.IdentifierCapture(name, name_origin))) => {
            let body = syntax {
                match $first_value {
                    true => $digit_value + 100
                    false => $digit_value
                }
            }
            parse_result(input, name, name_origin, body, origin)
        }
        _ => reject(origin)
    }
}

reject : Syntax.Origin -> Syntax.MacroResult
reject origin = Syntax.Rejected(Syntax.MacroDiagnostic("cannot emit expression", origin, Syntax.NoOrigins))

parse_result : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
parse_result (input, name, name_origin, body, origin) = match Syntax.parse_expression(input, Syntax.expression_syntax(body)) {
    Syntax.Parsed(parsed) => tokens(name, name_origin, parsed, origin)
    _ => reject(origin)
}

tokens : (Syntax.Identifier, Syntax.Origin, Syntax.ExpressionFragment, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
tokens (name, name_origin, body, origin) = match (Syntax.make_token(Syntax.Pub, "pub"), Syntax.make_token(Syntax.Colon, ":"), Syntax.make_token(Syntax.UnitType, "Unit"), Syntax.make_token(Syntax.IntType, "Int"), Syntax.make_token(Syntax.Arrow, "->"), Syntax.make_token(Syntax.LineEnd, "\n"), Syntax.make_token(Syntax.Equal, "=")) {
    (Syntax.MadeToken(public), Syntax.MadeToken(colon), Syntax.MadeToken(unit), Syntax.MadeToken(int), Syntax.MadeToken(arrow), Syntax.MadeToken(line), Syntax.MadeToken(equal)) => {
        let end = Syntax.MoreNodes(Syntax.ExpressionNode(body, origin), Syntax.NoNodes)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(equal, origin), end)
        let argument = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.NoNodes), origin)
        let equation = Syntax.MoreNodes(argument, equation)
        let equation = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), equation)
        let equation = Syntax.MoreNodes(Syntax.TokenNode(line, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(int, origin), equation)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(arrow, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(unit, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(colon, origin), signature)
        let signature = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), signature)
        let signature = Syntax.MoreNodes(Syntax.TokenNode(public, origin), signature)
        Syntax.Expanded(Syntax.Syntax(signature))
    }
    _ => reject(origin)
}
