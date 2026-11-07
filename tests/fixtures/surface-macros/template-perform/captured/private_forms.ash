effect Ask {
    ask : Int -> Int
}

pub syntax request $name:ident from $value:expr => {
    handle (perform Ask.$name $value) with Ask {
        ask value => resume (value + 2)
    }
}
