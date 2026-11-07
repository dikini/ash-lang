import control_opaque_generated (Secret)

main : Unit -> Int
main () = match Secret(42) {
    Secret(value) => value
}
