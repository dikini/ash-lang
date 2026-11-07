import actual as Helper

pub syntax destruct $value:expr => {
    Helper.evaluate (fn(Helper.Boxed(inner)) {
        inner + $value
    })
}
