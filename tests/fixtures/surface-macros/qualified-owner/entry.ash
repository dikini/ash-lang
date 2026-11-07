import forms (syntax call)
import decoy as Helper

main : Unit -> Int
main () = {
    let result = call 41
    match Helper.increment 1 == 101 {
        true => result
        false => 0
    }
}
