import helpers as H

pub syntax unused $member:ident with $value:expr => {
    H.$member(missing)
}

main : Unit -> Int
main () = 42
