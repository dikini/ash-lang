pub import actual (Capsule)
import actual as Direct
import forms (syntax wrap)

main : Unit -> Int
main () = {
    let result = wrap 41
    match Direct.unwrap (Direct.Boxed(0)) == 1 {
        true => result
        false => 0
    }
}
