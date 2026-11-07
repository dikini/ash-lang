import @builtin.compiler.syntax as Syntax
import identity_forms (syntax identity)

quote : Syntax.ExpressionFragment -> Syntax.ExpressionFragment
quote fragment = identity (syntax { ${ syntax { $fragment } } })

pub syntax declaration: (quote_roundtrip) $name:ident => {
    pub $name : Unit -> Int
    $name () = ${ quote(syntax { 42 }) }
}
