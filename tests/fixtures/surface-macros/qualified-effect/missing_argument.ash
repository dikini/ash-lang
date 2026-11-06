pub syntax unused $path:ident with $value:expr => {
    perform $path.Ask<Missing>.ask $value
}

main : Unit -> Int
main () = 42
