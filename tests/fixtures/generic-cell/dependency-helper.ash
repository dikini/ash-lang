import @builtin.generic_cell as Cell
pub get<R,T> : Cell.Cell<R,T> -> T ! {Cell.Ops<R,T>} where Cell.Provider<R,T>
get value = Cell.read value
pub put<R,T> : (Cell.Cell<R,T>,T) -> Unit ! {Cell.Ops<R,T>} where Cell.Provider<R,T>
put pair = Cell.write pair
