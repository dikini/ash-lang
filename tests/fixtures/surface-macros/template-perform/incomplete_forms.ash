effect Ask {
    ask : Int -> Int
    other : Unit -> Int
}

pub syntax incomplete $value:expr => {
    handle (perform Ask.ask $value) with Ask {
        ask value => resume value
    }
}
