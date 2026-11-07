import extra_forms (syntax make_relation)

make_relation Convert method convert

impl Convert<Int, Bool> {
    convert _ = true
}

main : Unit -> Int
main () = match convert(1) {
    true => 42
    false => 0
}
