//! Fixed DATA encoding for an Integer inside the prepaid optional result frame.
//! The caller owns scratch capacity; no source/native authority is represented.

pub(super) fn encode(integer: &crate::integer::Integer, output: &mut [u8]) -> Option<usize> {
    let size = usize::try_from(integer.magnitude_byte_length()).ok()?;
    let count = u32::try_from(size).ok()?;
    let end = 6usize.checked_add(size)?;
    if end > output.len() { return None; }
    let negative = integer.write_magnitude_le(&mut output[6..end])?;
    output[0] = 6;
    output[1] = u8::from(negative);
    output[2..6].copy_from_slice(&count.to_le_bytes());
    Some(end)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn actual_integer_result_codec_preserves_sign_magnitude_and_exact_scratch_cut() {
        let positive = crate::integer::Integer::parse_decimal(&"9".repeat(3000)).unwrap();
        let negative = &positive * &crate::integer::Integer::from_i64(-1);
        let zero = crate::integer::Integer::from_i64(0);
        for (integer, sign) in [(&positive,0),(&negative,1),(&zero,0)] {
            let size = usize::try_from(integer.magnitude_byte_length()).unwrap();
            let mut scratch = [0;4096];
            assert_eq!(encode(integer,&mut scratch[..6+size]),Some(6+size));
            assert_eq!(scratch[..2],[6,sign]);
            assert_eq!(u32::from_le_bytes(scratch[2..6].try_into().unwrap()) as usize,size);
            let mut magnitude = vec![0;size];
            assert_eq!(integer.write_magnitude_le(&mut magnitude),Some(sign==1));
            assert_eq!(scratch[6..6+size],magnitude);
            let mut short = [0xa5;4096];
            assert_eq!(encode(integer,&mut short[..5+size]),None);
            assert!(short.iter().all(|byte|*byte==0xa5),"short refusal precedes every write");
        }
    }
}
