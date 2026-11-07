import extra_forms (syntax make_operations)

make_operations Ask first left second right

main : Unit -> Int
main () = handle (perform Ask.left ()) with Ask {
    left _ => resume 42
    right _ => resume 0
}
