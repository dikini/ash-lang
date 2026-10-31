pub type Message = Ping
    | Reading(Int)
    | Pair(Int, Int)
pub type ByteValues = End
    | Byte(Int, ByteValues)
pub type Next = EndOfFrame
    | Value(Int)
pub type DecodeResult = Decoded(Message)
    | BadTag
    | Truncated
    | TrailingData
