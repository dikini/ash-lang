import opaque_subject (Secret)

main : Unit -> Int
main () = match Secret(0) {
    Secret(value) => value
}
