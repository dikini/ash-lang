import api (Secret as Alias)

pub syntax send $value:expr => {
    perform Alias.ask $value
}

main : Unit -> Int
main () = 42
