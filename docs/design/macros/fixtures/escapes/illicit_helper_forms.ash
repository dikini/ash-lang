import @builtin.compiler.syntax as Syntax

helper : Unit -> Syntax.ExpressionFragment
helper () = $value

pub syntax declaration: (illicit_helper) $name:ident from $value:expr => {
    pub $name : Unit -> Int
    $name () = ${ helper(()) }
}
