import api as Caller
import decoy as Owner
import forms (syntax unpack)

main : Unit -> Int
main () = {
    let inner = 100
    let result = unpack Boxed in Caller.Boxed(42)
    match inner == 100 {
        true => result
        false => 0
    }
}
