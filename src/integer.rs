//! Arbitrary-precision integers accepted at the Ash language boundary.

use std::fmt;
use std::ops::{Add, Mul};

/// An arbitrary-precision Ash integer.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Integer(num_bigint::BigInt);

/// The source text is not a decimal Ash integer literal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidInteger;

impl Integer {
    /// Returns the byte length of the unsigned magnitude encoding.
    /// This is a codec work metric, not a native ABI or memory-layout promise.
    #[must_use]
    pub fn magnitude_byte_length(&self) -> u64 {
        self.0.bits().div_ceil(8)
    }

    /// Copy an exact little-endian unsigned magnitude into already funded
    /// storage. The caller must bound/pay the actual length before invoking.
    /// No allocation or whole-integer clone occurs here; zero has no digits.
    pub(crate) fn write_magnitude_le(&self, destination: &mut [u8]) -> Option<bool> {
        if u64::try_from(destination.len()).ok()? != self.magnitude_byte_length() {
            return None;
        }
        for (word, digit) in self.0.iter_u32_digits().enumerate() {
            let start = word.checked_mul(4)?;
            for (offset, byte) in digit.to_le_bytes().into_iter().enumerate() {
                if let Some(out) = destination.get_mut(start.checked_add(offset)?) { *out = byte; }
                else if byte != 0 { return None; }
            }
        }
        Some(self.0.sign() == num_bigint::Sign::Minus)
    }

    /// Converts to the signed native 64-bit range without narrowing.
    #[must_use]
    pub fn to_i64(&self) -> Option<i64> {
        i64::try_from(&self.0).ok()
    }

    /// Constructs an Ash integer from a native signed 64-bit value.
    #[must_use]
    pub fn from_i64(value: i64) -> Self {
        Self(num_bigint::BigInt::from(value))
    }

    /// Constructs an exact mathematical value from a native unsigned 64-bit reply.
    pub(crate) fn from_u64(value: u64) -> Self {
        Self(num_bigint::BigInt::from(value))
    }

    /// Narrows a nonnegative mathematical value without using the host pointer width.
    pub(crate) fn to_u64(&self) -> Option<u64> {
        u64::try_from(&self.0).ok()
    }

    pub(crate) fn to_usize(&self) -> Option<usize> {
        usize::try_from(&self.0).ok()
    }

    #[cfg(test)]
    fn to_u8(&self) -> Option<u8> {
        u8::try_from(&self.0).ok()
    }

    pub(crate) fn from_usize(value: usize) -> Self {
        Self(num_bigint::BigInt::from(value))
    }

    /// Parses a decimal integer.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidInteger`] unless `source` is `0` or an ASCII nonzero
    /// digit followed by zero or more ASCII digits.
    pub fn parse_decimal(source: &str) -> Result<Self, InvalidInteger> {
        let mut bytes = source.bytes();
        let is_decimal = match bytes.next() {
            Some(b'0') => bytes.next().is_none(),
            Some(b'1'..=b'9') => bytes.all(|byte| byte.is_ascii_digit()),
            _ => false,
        };

        if !is_decimal {
            return Err(InvalidInteger);
        }

        source.parse().map(Self).map_err(|_| InvalidInteger)
    }
}

impl fmt::Display for Integer {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

impl Add for &Integer {
    type Output = Integer;

    fn add(self, rhs: Self) -> Self::Output {
        Integer(&self.0 + &rhs.0)
    }
}

impl Mul for &Integer {
    type Output = Integer;

    fn mul(self, rhs: Self) -> Self::Output {
        Integer(&self.0 * &rhs.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_magnitude_copy_preserves_full_sign_and_refuses_before_short_write() {
        let huge = Integer::parse_decimal(&"9".repeat(3000)).unwrap();
        let negative = &huge * &Integer::from_i64(-1);
        for (integer, sign) in [(&huge, false), (&negative, true)] {
            let count = usize::try_from(integer.magnitude_byte_length()).unwrap();
            let mut short = vec![0x55; count - 1];
            assert_eq!(integer.write_magnitude_le(&mut short), None);
            assert!(short.iter().all(|byte| *byte == 0x55));
            let mut exact = vec![0; count];
            assert_eq!(integer.write_magnitude_le(&mut exact), Some(sign));
            let reconstructed = num_bigint::BigInt::from_bytes_le(
                if sign { num_bigint::Sign::Minus } else { num_bigint::Sign::Plus }, &exact);
            assert_eq!(&integer.0, &reconstructed);
        }
        assert_eq!(Integer::from_i64(0).write_magnitude_le(&mut []), Some(false));
        assert_eq!(Integer::from_i64(i64::MIN).write_magnitude_le(&mut [0; 8]), Some(true));
    }

    #[test]
    fn checked_host_conversions_reject_negative_and_oversized_integers() {
        for number in [-1, -256] {
            let integer = Integer(num_bigint::BigInt::from(number));
            assert_eq!(integer.to_usize(), None);
            assert_eq!(integer.to_u8(), None);
        }
        assert_eq!(Integer::from_usize(0).to_usize(), Some(0));
        assert_eq!(Integer::from_usize(usize::MAX).to_usize(), Some(usize::MAX));
        assert_eq!(Integer::from_usize(255).to_u8(), Some(255));
        assert_eq!(Integer::from_usize(256).to_u8(), None);
        let oversized = Integer(num_bigint::BigInt::from(usize::MAX) + 1u8);
        assert_eq!(oversized.to_usize(), None);
        assert_eq!(oversized.to_u8(), None);
    }
}
