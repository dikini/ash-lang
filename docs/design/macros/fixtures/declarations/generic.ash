import extra_forms (syntax make_generic_type, syntax make_generic_box)

make_generic_type Maybe first Present second Absent
make_generic_box Box constructor Box

main : Unit -> Int
main () = match Box(Present(42)) {
    Box(Present(value)) => value
    Box(Absent) => 0
}
