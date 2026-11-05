import forms_pattern (syntax unpack)
import decoy as Helper
import actual as Direct

main : Unit -> Int
main () = {
    let inner = 0
    let result = unpack (Direct.Boxed(inner + 41))
    match Helper.unwrap (Helper.Boxed(1)) == 101 {
        true => match inner == 0 {
            true => result
            false => 0
        }
        false => 0
    }
}
