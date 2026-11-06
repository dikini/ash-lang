import forms (syntax fresh_pair)

main : Unit -> Int
main () = {
    let temp = 39
    fresh_pair (temp + 1) then 2
}
