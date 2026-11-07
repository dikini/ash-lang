import outer (syntax introduced)

invoke<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {| R}
invoke callback = introduced (callback ())

constant : Unit -> Int
constant () = 42

main : Unit -> Int
main () = invoke constant
