import actual as Helper

pub syntax hidden_pattern $value:expr => {
    match $value {
        Helper.Hidden(inner) => inner
    }
}
