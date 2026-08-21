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
