import short (Wrap, Relation, relate, relay, reveal, hidden_marker, twin_marker, Opaque, opaque_marker, impl Relation)
import long_two (impl Relation)

main : Unit -> Int
main () = reveal(relay((Wrap(Wrap(42)), ())))
