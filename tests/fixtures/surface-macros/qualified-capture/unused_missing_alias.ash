pub syntax unused $member:ident with $value:expr => {
    Missing.$member(1)
}

main : Unit -> Int
main () = 42
