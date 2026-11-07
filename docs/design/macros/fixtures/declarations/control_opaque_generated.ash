pub opaque newtype Secret = Secret(Int)
pub opaque type SecretSum = HiddenSum(Int)

pub build : Int -> Secret
build value = Secret(value)

pub build_sum : Int -> SecretSum
build_sum value = HiddenSum(value)
