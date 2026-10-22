import owner as Owner

main : Unit -> Owner.Scope<Unit, Unit, Int>
main () = resource Owner.Probe<{}, Fresh, {}> owner = 8 {
    Owner.read owner
}
