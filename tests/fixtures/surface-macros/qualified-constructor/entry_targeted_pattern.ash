import forms_targeted (syntax targeted_pattern)
import actual as Direct

type Fake = Wrap(Int)

main : Unit -> Int
main () = targeted_pattern (Direct.Boxed(41))
