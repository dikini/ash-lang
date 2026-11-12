effect First {
    first : Unit -> Unit
}
effect Second {
    second : Unit -> Unit
}
pub invoke : Unit -> Unit ! {First, Second}
invoke () = {
    let _ = perform First.first ()
    perform Second.second ()
}
