import ordering_forms (syntax first_failure)

pub syntax derive: (spawn_failure) $target:ident => {
    type Generated = Generated
    deriving (first_failure)
}
