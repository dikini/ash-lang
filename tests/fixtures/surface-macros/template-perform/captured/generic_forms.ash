pub syntax request $name:ident from $value:expr => {
    perform $name<Int>.ask $value
}
