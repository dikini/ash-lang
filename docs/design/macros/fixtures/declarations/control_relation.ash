pub interface Convert<A, B> where A -> B {
    convert : A -> B
}

impl Convert<Int, Bool> {
    convert _ = true
}

main : Unit -> Int
main () = match convert(1) {
    true => 42
    false => 0
}
