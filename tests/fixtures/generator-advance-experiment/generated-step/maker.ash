import @builtin.compiler.syntax as Syntax

pub syntax declaration: (make_step) $name:ident => {
    pub $name : Int -> (Int, Syntax.ExpressionFragment)
    $name state = $name(state)
}
