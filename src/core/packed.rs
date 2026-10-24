//! Packed ordinary values and compiler-owned first-order pure callables.

use crate::{
    module::ModuleId,
    types::{ConstructorId, Type},
};
use std::sync::Arc;

/// Raw UTF-8 payload. Validation independently rejects malformed encoding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StringNode {
    bytes: Arc<[u8]>,
}
impl StringNode {
    pub(super) fn new(bytes: Arc<[u8]>) -> Self {
        Self { bytes }
    }
    /// Returns the stored bytes, including embedded NUL.
    #[must_use]
    pub fn bytes(&self) -> &Arc<[u8]> {
        &self.bytes
    }
}

/// Closed set of compiler-owned pure operations admitted by this experiment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Intrinsic {
    /// Constructs the null C data pointer, without a memory access.
    AddressNull,
    /// Tests a C data pointer for null.
    AddressIsNull,
    /// Compares raw data-pointer values, without interpreting their lifetime.
    AddressEqual,
    /// Checks the GNU64 signed range without invoking a native symbol.

    /// Checks the GNU64 size_t range without invoking a native symbol.

    /// Checks that an ordinary string contains no NUL, without native authority.

    /// Reads the selected source descriptor's ordinary private payload.

    /// Replaces that payload after complete fallible admission.

    /// Reads through an independently admitted initialized live State.

    /// Writes through that State only after complete reply admission.

    /// Copies a checked live view with its opaque exact-view extent.

    /// Copies a checked live NUL view under its bounded scan contract.

    /// Exposes a copied length without adding access permission.

    /// Conservatively denies the exact authenticated Current/Enclosing group.

    /// Denies the exact pending unpublished acquisition group, including null.

    /// Constructs empty bytes.
    BytesEmpty,
    /// Appends a checked byte and returns an ordinary constructor result.
    BytesAppendByte {
        appended: ConstructorId,
        invalid: ConstructorId,
    },
    /// Reads one independently owned byte with an ordinary bounds result.
    BytesAt {
        found: ConstructorId,
        invalid: ConstructorId,
    },
    /// Counts bytes.
    BytesLength,
    /// Compares byte contents.
    BytesEqual,
    /// Encodes a string as UTF-8 bytes.
    StringToUtf8,
    /// Decodes valid UTF-8, with an ordinary failure result.
    StringFromUtf8 {
        decoded: ConstructorId,
        invalid: ConstructorId,
    },
    /// Counts UTF-8 bytes.
    StringByteLength,
    /// Compares string contents.
    StringEqual,
}

/// Inspectable callable data retaining its compiler-owned module authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IntrinsicNode {
    operation: Intrinsic,
    module: ModuleId,
}
impl IntrinsicNode {
    pub(super) const fn new(operation: Intrinsic, module: ModuleId) -> Self {
        Self { operation, module }
    }
    /// Returns the selected operation.
    #[must_use]
    pub const fn operation(self) -> Intrinsic {
        self.operation
    }
    /// Returns its canonical compiler-owned module.
    #[must_use]
    pub const fn module(self) -> ModuleId {
        self.module
    }
    /// Returns the fixed ordinary signature, including nominal result identity.
    #[must_use]
    pub fn expected_type(self) -> Type {
        let (input, output) = match self.operation {
            Intrinsic::AddressNull => (
                Type::Unit,
                Type::Nominal(crate::types::NominalTypeId::new(self.module, 0)),
            ),
            Intrinsic::AddressIsNull => (
                Type::Nominal(crate::types::NominalTypeId::new(self.module, 0)),
                Type::Bool,
            ),
            Intrinsic::AddressEqual => {
                let address = Type::Nominal(crate::types::NominalTypeId::new(self.module, 0));
                (
                    Type::Tuple(Box::new([address.clone(), address])),
                    Type::Bool,
                )
            }

            Intrinsic::BytesEmpty => (Type::Unit, Type::Bytes),
            Intrinsic::BytesAppendByte { appended, .. } => (
                Type::Tuple(Box::new([Type::Bytes, Type::Int])),
                Type::Nominal(appended.owner()),
            ),
            Intrinsic::BytesAt { found, .. } => (
                Type::Tuple(Box::new([Type::Bytes, Type::Int])),
                Type::Nominal(found.owner()),
            ),
            Intrinsic::BytesLength => (Type::Bytes, Type::Int),
            Intrinsic::BytesEqual => (
                Type::Tuple(Box::new([Type::Bytes, Type::Bytes])),
                Type::Bool,
            ),
            Intrinsic::StringToUtf8 => (Type::String, Type::Bytes),
            Intrinsic::StringFromUtf8 { decoded, .. } => {
                (Type::Bytes, Type::Nominal(decoded.owner()))
            }
            Intrinsic::StringByteLength => (Type::String, Type::Int),
            Intrinsic::StringEqual => (
                Type::Tuple(Box::new([Type::String, Type::String])),
                Type::Bool,
            ),
        };
        Type::Function(Box::new(input), Box::new(output))
    }
    pub(crate) fn authentic_module(self) -> bool {
        match self.operation {
            Intrinsic::AddressNull | Intrinsic::AddressIsNull | Intrinsic::AddressEqual => {
                self.module.is_builtin_foreign()
            }

            Intrinsic::BytesEmpty
            | Intrinsic::BytesAppendByte { .. }
            | Intrinsic::BytesAt { .. }
            | Intrinsic::BytesLength
            | Intrinsic::BytesEqual => self.module.is_builtin_bytes(),
            Intrinsic::StringToUtf8
            | Intrinsic::StringFromUtf8 { .. }
            | Intrinsic::StringByteLength
            | Intrinsic::StringEqual => self.module.is_builtin_string(),
        }
    }
}
