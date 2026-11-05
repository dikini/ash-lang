import forms (syntax wrap)
import decoy as Helper

main : Unit -> Int
main () = {
    let result = wrap 41
    match Helper.unwrap (Helper.Boxed(1)) == 101 {
        true => result
        false => 0
    }
}
