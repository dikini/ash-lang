import dependency (Option, Some, observe, relay, impl Observe)
main : Unit -> Int
main () = observe(relay(Some(1)))
