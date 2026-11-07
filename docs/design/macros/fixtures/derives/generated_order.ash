import generated_failure_forms (syntax spawn_failure)
import ordering_forms (syntax second_failure)

type Source = Source
deriving (spawn_failure, second_failure)

main : Unit -> Int
main () = 42
