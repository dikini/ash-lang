import facade_api (Ask as Alias)

pub syntax send $value:expr => {
    perform Alias.ask $value
}
