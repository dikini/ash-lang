import forms (syntax make_identity, syntax make_inline)

make_identity id for Int
make_inline same for Int

main : Unit -> Int
main () = id(same(42))
