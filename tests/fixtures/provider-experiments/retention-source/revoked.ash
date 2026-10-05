import @foreign.retention as Native
import provider as Provider
import library as Library

main : Unit -> Provider.Scope<Native.InitError, Native.FinishError, Int>
main () = resource Library.Parent<P> parent = 20 {
let first = Library.parent_read parent
let child_report = resource Library.Child<C> child = (parent, 22) {
Library.child_read child
}
Library.parent_read parent
}
