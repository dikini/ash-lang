import forms (syntax wrap)

invoke<T : Type> : (T, Unit -> Int) -> Int
invoke (value, callback) = wrap T in (callback ())

constant : Unit -> Int
constant () = 42

main : Unit -> Int
main () = invoke ((), constant)
