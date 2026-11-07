import extra_forms (syntax make_opaque_box, syntax make_opaque_type)

make_opaque_box Secret constructor Secret
make_opaque_type SecretSum constructor HiddenSum

pub build : Int -> Secret
build value = Secret(value)

pub build_sum : Int -> SecretSum
build_sum value = HiddenSum(value)
