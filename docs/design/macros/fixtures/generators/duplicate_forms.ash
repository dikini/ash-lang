import @builtin.compiler.syntax as Syntax
import @builtin.compiler.syntax (fragment_node)

type LiteralNode = LiteralNode(Syntax.TokenResult)

impl Syntax.SyntaxFragment<LiteralNode> {
    fragment_node (LiteralNode(Syntax.MadeToken(token)), origin) = Syntax.TokenNode(token, origin)
    fragment_node (LiteralNode(Syntax.InvalidToken), origin) = Syntax.GroupNode(Syntax.Parentheses, Syntax.Syntax(Syntax.NoNodes), origin)
}

next_number : Int -> (Int, LiteralNode) ! {Syntax.Ops}
next_number state = (state + 1, LiteralNode(Syntax.make_token(Syntax.IntegerLiteral, "0")))

pub syntax declaration: (bad_duplicate) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = $number
    )+
} with {
    $number from 0 step next_number
    $number from 0 step next_number
}
