payload_copy<Before : EffectRow, T> : T -> T ! {| Before}
payload_copy value = value

payload_mono : Int -> Int
payload_mono value = value

payload_donor : Int -> Int
payload_donor value = value
