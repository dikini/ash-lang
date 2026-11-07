pub interface Check<Key> {
    check : Key -> Int
    measure : Key -> Bool
}
