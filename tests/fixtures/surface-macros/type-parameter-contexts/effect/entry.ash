import forms (syntax emit)
emit Read operation read
main : Unit -> Int
main () = handle (perform Read<Int>.read ()) with Read<Int> {
    read ignored => resume 42
}
