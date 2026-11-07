import early_owner_forms (syntax use_private)

private_calculation : Unit -> Int
private_calculation () = 0

renamed : Unit -> Int
renamed () = 0

use_private owner_result

main : Unit -> Int
main () = owner_result(())
