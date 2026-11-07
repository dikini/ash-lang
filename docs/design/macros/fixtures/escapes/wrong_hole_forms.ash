import @builtin.compiler.syntax as Syntax

wrong : Int -> Syntax.ExpressionFragment
wrong value = syntax { $value }

pub syntax declaration: (wrong_hole) => {
    pub answer : Unit -> Int
    answer () = 42
}
