import quote_roundtrip_forms (syntax quote_roundtrip)
import identity_forms (syntax token_kinds)

quote_roundtrip answer

main : Unit -> Int
main () = token_kinds answer(())
