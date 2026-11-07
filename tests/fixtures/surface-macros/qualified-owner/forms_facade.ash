import facade as Helper

pub syntax call_facade $value:expr => {
    Helper.increment $value
}
