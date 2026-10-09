effect Number {
    get : Unit -> Int
}

main : Unit -> Int
main () = handle (perform Number.get ()) with Number {
    get ignored => {
        let first = resume 42
        handle (perform Number.get ()) with Number {
            get ignored => resume 17
        }
    }
}
