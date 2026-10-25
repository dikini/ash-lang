//! Packed ordinary values and compiler-owned first-order pure callables.

use crate::{
    module::ModuleId,
    types::{ConstructorId, Type, TypeVariableId},
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
    /// Inspect a bound immediate request using ordinary Ash integer values.
    RegionRequestBytes,
    /// Inspect the requested alignment.
    RegionRequestAlignment,
    /// Check and register returned backing for the bound request's owner.
    RegionFromBacking {
        owner: TypeVariableId,
        address_module: ModuleId,
    },
    /// The host leaf of the fixed pair for an explicit prospective owner.
    RegionHostAllocate {
        owner: TypeVariableId,
        configuration: super::region::HostRegionConfiguration,
    },
    /// The paired host release leaf, fixed to that same owner/configuration.
    RegionHostRelease {
        owner: TypeVariableId,
        configuration: super::region::HostRegionConfiguration,
    },
    /// Constructs the null C data pointer, without a memory access.
    AddressNull,
    /// Tests a C data pointer for null.
    AddressIsNull,
    /// Compares raw data-pointer values, without interpreting their lifetime.
    AddressEqual,
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
    pub(crate) const fn new(operation: Intrinsic, module: ModuleId) -> Self {
        Self { operation, module }
    }
    /// Returns the selected operation.
    #[must_use]
    pub const fn operation(self) -> Intrinsic {
        self.operation
    }
    pub(crate) const fn constructs_buffer_or_reply(self) -> bool {
        matches!(
            self.operation,
            Intrinsic::BytesEmpty
                | Intrinsic::BytesAppendByte { .. }
                | Intrinsic::BytesAt { .. }
                | Intrinsic::StringToUtf8
                | Intrinsic::StringFromUtf8 { .. }
        )
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
            Intrinsic::RegionRequestBytes | Intrinsic::RegionRequestAlignment => (
                Type::Nominal(crate::types::NominalTypeId::new(self.module, 0)),
                Type::Int,
            ),
            Intrinsic::RegionFromBacking {
                owner,
                address_module,
            } => (
                Type::Tuple(Box::new([
                    Type::Nominal(crate::types::NominalTypeId::new(self.module, 0)),
                    Type::Nominal(crate::types::NominalTypeId::new(address_module, 0)),
                    Type::Int,
                    Type::Int,
                ])),
                Type::Application(
                    Box::new(Type::Nominal(crate::types::NominalTypeId::new(
                        self.module,
                        1,
                    ))),
                    Box::new(Type::Variable(owner)),
                ),
            ),
            Intrinsic::RegionHostAllocate { owner, .. } => (
                Type::Nominal(crate::types::NominalTypeId::new(self.module, 0)),
                Type::Application(
                    Box::new(Type::Nominal(crate::types::NominalTypeId::new(
                        self.module,
                        1,
                    ))),
                    Box::new(Type::Variable(owner)),
                ),
            ),
            Intrinsic::RegionHostRelease { .. } => (Type::Unit, Type::Unit),
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
        if matches!(
            self.operation,
            Intrinsic::RegionRequestBytes
                | Intrinsic::RegionRequestAlignment
                | Intrinsic::RegionFromBacking { .. }
        ) {
            Type::function_computation(
                input,
                crate::types::ComputationType::new(
                    output,
                    crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                        crate::types::EffectId::new(self.module, 0),
                        Box::new([]),
                    )),
                ),
            )
        } else {
            Type::Function(Box::new(input), Box::new(output))
        }
    }
    pub(crate) fn authentic_module(self) -> bool {
        match self.operation {
            Intrinsic::RegionFromBacking { address_module, .. } => {
                self.module.is_builtin_region() && address_module.is_builtin_foreign()
            }
            Intrinsic::RegionRequestBytes | Intrinsic::RegionRequestAlignment => {
                self.module.is_builtin_region()
            }
            Intrinsic::RegionHostAllocate { .. } | Intrinsic::RegionHostRelease { .. } => {
                self.module.is_builtin_region()
            }
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
