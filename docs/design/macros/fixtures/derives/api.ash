pub interface Marker<A> {
    mark : A -> Bool
}

pub interface Tagged<A> {
    tag : A -> Int
}
