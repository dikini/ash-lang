import forms (syntax marker)

interface Local<A> {
    local : A -> Bool
}
    deriving (marker)

main : Unit -> Int
main () = 42
