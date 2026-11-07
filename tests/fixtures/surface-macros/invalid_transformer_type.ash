import @builtin.compiler.syntax as Syntax

pub syntax invalid $value:expr => using wrong

wrong : Int -> Int
wrong value = value

main : Unit -> Int
main () = 42
