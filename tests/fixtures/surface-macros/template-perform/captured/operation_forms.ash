pub effect Ask {
    ask : Int -> Int
}

pub syntax request $name:ident from $value:expr => {
    perform Ask.$name $value
}
