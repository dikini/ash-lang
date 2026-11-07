import @builtin.regions as Region
import forms (syntax supplied)

allocate<R> : Region.Request -> Region.Storage<R>
allocate request = allocate request
release : Unit -> Unit
release ignored = ()
provider<R> : Int -> ((Region.Request -> Region.Storage<R>), (Unit -> Unit))
provider ignored = (allocate, release)

main : Unit -> Int
main () = {
    let owner = 42
    supplied (provider owner)
}
