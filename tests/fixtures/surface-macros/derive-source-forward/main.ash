import forms (syntax pass)
type First = First
pass {
    type Second = Second
        | Other
}
type Third = Third
main : Unit -> Int
main () = match Other {
    Second => 0
    Other => 42
}
