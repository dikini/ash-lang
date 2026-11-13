import @builtin.compiler.syntax as Syntax
import forms (syntax round_trip)

round_trip {
    quote_identity : Syntax.ExpressionFragment -> Syntax.ExpressionFragment ! {Syntax.Ops}
    quote_identity fragment = syntax { $fragment }
}

main : Unit -> Int
main () = {
    let _ = quote_identity
    42
}
