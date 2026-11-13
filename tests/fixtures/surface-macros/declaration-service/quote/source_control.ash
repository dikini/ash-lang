import @builtin.compiler.syntax as Syntax

quote_identity : Syntax.ExpressionFragment -> Syntax.ExpressionFragment ! {Syntax.Ops}
quote_identity fragment = syntax { $fragment }

main : Unit -> Int
main () = {
    let _ = quote_identity
    42
}
