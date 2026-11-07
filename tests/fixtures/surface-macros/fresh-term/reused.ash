import forms (syntax reuse_pair)

main : Unit -> Int
main () = {
    let temp = 39
    reuse_pair (temp + 1) then 2
}
