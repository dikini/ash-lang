import forms (syntax accept)

accept_other<Token> : Token -> Int
accept_other value = accept value

main : Unit -> Int
main () = accept_other true
