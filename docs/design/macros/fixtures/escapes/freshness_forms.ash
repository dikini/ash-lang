import @builtin.compiler.syntax as Syntax

make : Unit -> Syntax.ExpressionFragment
make () = syntax {
    {
        let temporary = 10
        temporary
    }
}

pub syntax declaration: (fresh_quotes) $name:ident => {
    pub $name : Unit -> Int
    $name () = ${
        let left = make(())
        let right = make(())
        syntax { $left + $right }
    }
}
