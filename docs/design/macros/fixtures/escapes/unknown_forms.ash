import @builtin.compiler.syntax as Syntax

quote_missing : Unit -> Syntax.ExpressionFragment
quote_missing () = syntax { missing(()) }

pub syntax declaration: (use_unknown) $name:ident => {
    pub $name : Unit -> Int
    $name () = ${ quote_missing(()) }
}
