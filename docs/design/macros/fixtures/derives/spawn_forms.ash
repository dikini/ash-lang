import api (Marker, mark)
import forms (syntax marker)

pub syntax derive: (spawn) $target:ident => {
    type Generated = Generated
        deriving (marker)

    probe : Unit -> Bool
    probe () = mark(Generated)
}
