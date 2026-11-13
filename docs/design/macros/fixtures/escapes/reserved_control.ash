import @builtin.compiler.syntax as Syntax

syntax_value : Unit -> Int
syntax_value () = 20

declaration : Unit -> Int
declaration () = 22

main : Unit -> Int
main () = syntax_value(()) + declaration(())
