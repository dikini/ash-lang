import @builtin.foreign as Foreign
import owner as Owner

read_result : Foreign.Call<Int> -> Int
read_result result = match result {
    Foreign.Returned(byte) => byte
    Foreign.ConversionFailed(_) => 999
}
write_result : Foreign.Call<Unit> -> Bool
write_result result = match result {
    Foreign.Returned(()) => true
    Foreign.ConversionFailed(_) => false
}

main : Unit -> Owner.Scope<Unit, Unit, (Int, Int, Bool, Int, Bool, Int, Bool, Int)>
main () = resource Owner.Probe<{}, Fresh, {}> owner = (42, 7) {
    let first = read_result (Owner.read (owner, 0))
    let last = read_result (Owner.read (owner, 1))
    let written = write_result (Owner.write (owner, 0, 255))
    let changed = read_result (Owner.read (owner, 0))
    let rejected_byte = write_result (Owner.write (owner, 0, 256))
    let unchanged = read_result (Owner.read (owner, 0))
    let rejected_index = write_result (Owner.write (owner, 7, 256))
    let still_unchanged = read_result (Owner.read (owner, 0))
    (first, last, written, changed, rejected_byte, unchanged, rejected_index, still_unchanged)
}
