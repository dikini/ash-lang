pub effect Ask<T> {
    ask : T -> T
}

effect Hidden<T> {
    ask : T -> T
}

pub syntax send $value:expr => {
    perform Ask<Int>.ask $value
}

pub syntax local $value:expr => {
    handle (perform Hidden<Int>.ask $value) with Hidden<Int> {
        ask value => resume value
    }
}
