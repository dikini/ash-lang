effect A {
ask : Unit -> Unit
}
effect B {
ask : Unit -> Unit
}
effect C {
ask : Unit -> Unit
}
effect D {
ask : Unit -> Unit
}
effect E {
ask : Unit -> Unit
}
askB : Unit -> Unit ! {B}
askB () = perform B.ask ()
badD : Unit -> Unit ! {D}
badD () = handle (perform E.ask ()) with E {
ask ignored => {
let _ = perform D.ask ()
resume ()
}
}
runA : Unit -> Unit ! {B, D}
runA () = handle (handle (perform C.ask ()) with C {
ask ignored => {
let _ = askB ()
let _ = resume ()
let _ = perform A.ask ()
let _ = askB ()
badD ()
}
}) with A {
ask ignored => handle ({
let _ = resume ()
perform B.ask ()
}) with B {
ask ignored => handle ({
let _ = resume ()
perform D.ask ()
}) with D {
ask ignored => discard
}
}
}
main : Unit -> Unit
main () = handle (handle (runA ()) with B {
ask ignored => resume ()
}) with D {
ask ignored => resume ()
}
