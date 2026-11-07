pub effect Ask {
    ask : Int -> Int
}

pub syntax send $value:expr => {
    perform Ask.ask $value
}
