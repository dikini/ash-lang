import unknown_forms (syntax use_unknown)

missing : Unit -> Int
missing () = 42

use_unknown answer

main : Unit -> Int
main () = answer(())
