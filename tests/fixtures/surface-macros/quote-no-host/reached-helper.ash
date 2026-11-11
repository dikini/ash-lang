import @builtin.compiler.syntax as Syntax

make : Unit -> Syntax.ExpressionFragment
make () = syntax { 1 }

main : Unit -> Syntax.ExpressionFragment
main () = make(())
