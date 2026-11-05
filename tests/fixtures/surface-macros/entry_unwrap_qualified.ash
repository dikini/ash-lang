import syntax_unwrap_ops (syntax unwrap)
import syntax_qualified_helper as Helper

main : Unit -> Int
main () = unwrap (Helper.value ())
