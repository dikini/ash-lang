import api (Ask as Alias, Generic as Select)

pub syntax send $value:expr => {
    perform Alias.ask $value
}

pub syntax send_generic $value:expr => {
    perform Select<Int>.ask $value
}
