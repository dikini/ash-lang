import api (Ask as Alias)

pub syntax wrong $value:expr => {
    perform Alias<Int>.ask $value
}
