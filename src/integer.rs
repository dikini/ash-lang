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
    /// Private immediate eligibility shared by checked Core and the evaluator.
    pub(crate) fn to_i128(&self) -> Option<i128> {
        i128::try_from(&self.0).ok()
    }

    pub(crate) fn from_i128(value: i128) -> Self {
        Self(num_bigint::BigInt::from(value))
    }

    pub(crate) fn sign_magnitude(&self) -> (bool, Vec<u8>) {
        let (sign, bytes) = self.0.to_bytes_le();
        (sign == num_bigint::Sign::Minus, bytes)
    }

    pub(crate) fn from_sign_magnitude(negative: bool, bytes: &[u8]) -> Self {
        Self(num_bigint::BigInt::from_bytes_le(
            if negative {
                num_bigint::Sign::Minus
            } else {
                num_bigint::Sign::Plus
            },
            bytes,
        ))
    }

    /// Exact quotient and remainder for nonnegative integers. The caller pays
    /// for traversal before invoking this operation.
    pub(crate) fn split_base256(&self) -> Option<(Self, u8)> {
        let (negative, bytes) = self.sign_magnitude();
        if negative {
            return None;
        }
        let remainder = bytes.first().copied().unwrap_or(0);
        let quotient = Self::from_sign_magnitude(false, bytes.get(1..).unwrap_or(&[]));
        Some((quotient, remainder))
    }

    /// Returns the byte length of the unsigned magnitude encoding.
    /// This is a codec work metric, not a native ABI or memory-layout promise.
    #[must_use]
    pub fn magnitude_byte_length(&self) -> u64 {
        self.0.bits().div_ceil(8)
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
    fn integer_conversions_reject_negative_and_oversized_values() {
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

#[cfg(test)]
mod split_base256_tests {
    use super::Integer;

    #[test]
    fn exact_sign_and_unbounded_magnitude() {
        assert!(Integer::from_i64(-1).split_base256().is_none());
        for (input, quotient, remainder) in [
            ("0", "0", 0),
            ("1", "0", 1),
            ("255", "0", 255),
            ("256", "1", 0),
            ("257", "1", 1),
            (
                "340282366920938463463374607431768211456",
                "1329227995784915872903807060280344576",
                0,
            ),
        ] {
            let n = Integer::parse_decimal(input).unwrap();
            let (q, r) = n.split_base256().unwrap();
            assert_eq!(q.to_string(), quotient);
            assert_eq!(r, remainder);
        }
    }
}
