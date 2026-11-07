import private_type_forms (syntax private_type)

private_type first using HiddenFirst constructor HiddenFirst
private_type second using HiddenSecond constructor HiddenSecond

type Hidden = Hidden

main : Unit -> Int
main () = first(()) + second(())
