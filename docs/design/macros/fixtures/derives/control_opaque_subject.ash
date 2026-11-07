pub import api (Marker)
import api (mark)

pub opaque newtype Secret = Secret(Int)

pub impl Marker<Secret> {
    mark _ = true
}

pub make : Unit -> Secret
make () = Secret(0)
