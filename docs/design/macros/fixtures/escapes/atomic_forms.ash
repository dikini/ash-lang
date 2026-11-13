import @builtin.compiler.syntax as Syntax

never : Unit -> Syntax.ExpressionFragment
never () = never(())

pub syntax declaration: (abort) $name:ident => {
    pub $name : Unit -> Int
    $name () = 1
    pub after : Unit -> Int
    after () = ${ never(()) }
}
