import facade (increment as adjust)

pub syntax call_targeted_facade $value:expr => {
    adjust $value
}
