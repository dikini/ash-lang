effect Ask {
    ask : Int -> Int
}

pub syntax nested $value:expr => {
    handle (perform Ask.ask $value) with Ask {
        ask value => {
            let saved : Unit -> Int = fn(ignored) {
                resume value
            }
            saved ()
        }
    }
}
