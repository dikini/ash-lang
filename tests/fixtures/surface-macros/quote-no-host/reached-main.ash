import @builtin.compiler.syntax as Syntax

main : Unit -> Syntax.ExpressionFragment
main () = syntax { 1 }
