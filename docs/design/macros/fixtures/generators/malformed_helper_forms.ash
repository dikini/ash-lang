import @builtin.compiler.syntax as Syntax

bad_helper : Unit -> Syntax.ExpressionFragment
bad_helper () = syntax { 0 + }

pub syntax declaration: (unused_helper) $name:ident => {
    pub $name : Unit -> Int
    $name () = 42
}
