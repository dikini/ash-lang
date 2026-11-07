pub syntax unused $path:ident in $value:expr => {
    let item : $path.Box<Missing> = $value
    item
}

main : Unit -> Int
main () = 42
