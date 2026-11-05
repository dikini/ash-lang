effect Ask {
    ask : Int -> Int
}

pub syntax local_ask $value:expr => {
    handle (perform Ask.ask $value) with Ask {
        ask value => resume value
    }
}

pub syntax clause $value:expr => {
    handle (perform Ask.ask 42) with Ask {
        ask value => $value
    }
}
