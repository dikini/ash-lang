import @foreign.retention as Native
import provider as Provider
import library as Library

main : Unit -> Provider.Scope<Native.InitError, Native.FinishError, Provider.Scope<Native.InitError, Native.FinishError, Int>>
main () = resource Library.Parent<P> parent = 20 {
let first = Library.parent_read parent
resource Library.Child<C> child = (parent, 22) {
first + Library.child_read child
}
}
