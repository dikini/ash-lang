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
    pub(crate) fn to_i64(&self) -> Option<i64> {
        i64::try_from(&self.0).ok()
    }

    pub(crate) fn from_i64(value: i64) -> Self {
        Self(num_bigint::BigInt::from(value))
    }

    pub(crate) fn to_usize(&self) -> Option<usize> {
        usize::try_from(&self.0).ok()
    }

    pub(crate) fn to_u8(&self) -> Option<u8> {
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
