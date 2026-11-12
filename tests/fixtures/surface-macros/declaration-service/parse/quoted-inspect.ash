import @builtin.compiler.syntax as Syntax
import forms (syntax parse_quote)

parse_quote {
    quote : Syntax.ExpressionFragment -> Syntax.ExpressionFragment ! {Syntax.Ops}
    quote fragment = syntax { $fragment + 100 }
}

main : Unit -> Int
main () = 42
