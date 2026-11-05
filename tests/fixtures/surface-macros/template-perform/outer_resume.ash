import private_forms (syntax local_ask)

effect Outer {
    outer : Unit -> Int
}

main : Unit -> Int
main () = handle (perform Outer.outer ()) with Outer {
    outer ignored => local_ask (resume 42)
}
