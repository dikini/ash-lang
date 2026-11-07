pub import api (Marker)
import api (mark)
import forms (syntax public_marker)

pub opaque newtype Secret = Secret(Int)
    deriving (public_marker)

pub make : Unit -> Secret
make () = Secret(0)
