pub effect Ask {
    ask : Int -> Int
}

pub syntax bad $value:expr => {
    perform Ask.missing $value
}
