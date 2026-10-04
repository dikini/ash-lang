import library as Library

pub forward<R : Type, Rows : EffectRow> : (Library.Connection<R, {| Rows}>, Unit -> Unit ! {| Rows}) -> Library.Error ! {Library.ConnectionOps<R, {| Rows}>} where Library.ConnectionProvider<R, {| Rows}>
forward operand = Library.relay operand

main : Unit -> Unit
main () = ()
