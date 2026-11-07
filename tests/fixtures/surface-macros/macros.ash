import helpers as Helpers
import other_dsl (syntax bump, syntax choose)
import @builtin.compiler.syntax as Syntax

pub opaque type Secret = Hidden(Int)

private_increment : Int -> Int
private_increment value = Helpers.increment(value)

pub syntax bind $name:ident = $initial:expr when $condition:expr in $body:expr => {
    let temp = 1
    let $name = $initial
    match Hidden($body + temp) {
        Hidden(value) => choose $condition then private_increment (bump value) else 0
    }
}

pub syntax twice $value:expr => using expand_twice

expand_twice : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_twice input = {
    let origin = Syntax.invocation_origin(input)
    match Syntax.capture(input, 0) {
        Syntax.Captured(Syntax.ExpressionCapture(value)) => match Syntax.make_token(Syntax.Plus, "+") {
            Syntax.MadeToken(plus) => {
                let tail = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), Syntax.NoNodes)
                let middle = Syntax.MoreNodes(Syntax.TokenNode(plus, origin), tail)
                let nodes = Syntax.MoreNodes(Syntax.ExpressionNode(value, origin), middle)
                Syntax.Expanded(Syntax.Syntax(nodes))
            }
            Syntax.InvalidToken => Syntax.Rejected(Syntax.MacroDiagnostic("invalid plus", origin, Syntax.NoOrigins))
        }
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing expression", origin, Syntax.NoOrigins))
    }
}
