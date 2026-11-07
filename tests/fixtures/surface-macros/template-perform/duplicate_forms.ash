effect Ask {
    ask : Int -> Int
}

pub syntax duplicate $value:expr => {
    handle (perform Ask.ask $value) with Ask {
        ask value => resume value
        ask other => resume other
    }
}
