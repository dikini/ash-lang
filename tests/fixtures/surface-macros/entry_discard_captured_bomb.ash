import syntax_generated_outer (syntax parsed_discard)
import syntax_generated_inner (syntax bomb)

main : Unit -> Int
main () = parsed_discard (bomb 41)
