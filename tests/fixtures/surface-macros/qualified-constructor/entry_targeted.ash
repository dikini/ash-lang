import forms_targeted (syntax targeted)

type Fake = Wrap(Int)

main : Unit -> Int
main () = {
    let result = targeted 41
    let caller = match Wrap(1) {
        Wrap(value) => value
    }
    match caller == 1 {
        true => result
        false => 0
    }
}
