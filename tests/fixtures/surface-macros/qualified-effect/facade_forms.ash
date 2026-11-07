import facade_api as Owner

pub syntax send $value:expr => {
    perform Owner.Ask.ask $value
}
