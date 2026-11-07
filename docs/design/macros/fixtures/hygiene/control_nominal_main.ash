import control_nominal_generated (Boxed, Wrap)

main : Unit -> Int
main () = match Wrap(42) {
    Wrap(value) => value
    _ => 0
}
