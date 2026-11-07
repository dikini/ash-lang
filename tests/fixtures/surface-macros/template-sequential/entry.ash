import forms (syntax sequence)

main : Unit -> Int
main () = {
    let item = 40
    let result = sequence item = (item + 1) then later = (item + 1) in later
    match item == 40 {
        true => result
        false => 0
    }
}
