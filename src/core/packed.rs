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
    /// Checks the GNU64 signed range without invoking a native symbol.
    ForeignCheckedI64 {
        /// Claim of the original compiler-owned function identity.
        function: crate::resolved::BinderId,
    },
    /// Checks the GNU64 size_t range without invoking a native symbol.
    ForeignCheckedSizeT {
        /// Claim of the original compiler-owned function identity.
        function: crate::resolved::BinderId,
    },
    /// Checks that an ordinary string contains no NUL, without native authority.
    ForeignCheckedNul {
        /// Original compiler-owned pure preflight declaration.
        function: crate::resolved::BinderId,
    },
    /// Reads the selected source descriptor's ordinary private payload.
    ForeignDataOf {
        /// Original sealed state/data declaration.
        function: crate::resolved::BinderId,
    },
    /// Replaces that payload after complete fallible admission.
    ForeignReplaceData {
        /// Original sealed state/data declaration.
        function: crate::resolved::BinderId,
    },
    /// Reads through an independently admitted initialized live State.
    ForeignByteRead {
        /// Original sealed canonical byte declaration.
        function: crate::resolved::BinderId,
    },
    /// Writes through that State only after complete reply admission.
    ForeignByteWrite {
        /// Original sealed canonical byte declaration.
        function: crate::resolved::BinderId,
    },
    /// Copies a checked live view with its opaque exact-view extent.
    ForeignCopyBytes { function: crate::resolved::BinderId },
    /// Copies a checked live NUL view under its bounded scan contract.
    ForeignCopyNul { function: crate::resolved::BinderId },
    /// Exposes a copied length without adding access permission.
    ForeignExtentValue { function: crate::resolved::BinderId },
    /// Produces an opaque witness from one independently authenticated dictionary.
    ForeignLayoutWitness {
        /// Copied header; canonical dictionary validation is mandatory.
        producer: crate::foreign::ForeignLayoutProducer,
    },
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
            Intrinsic::ForeignCheckedI64 { .. } | Intrinsic::ForeignCheckedSizeT { .. } => (
                Type::Int,
                Type::Application(
                    Box::new(Type::Nominal(crate::types::NominalTypeId::new(
                        self.module,
                        1,
                    ))),
                    Box::new(Type::Int),
                ),
            ),
            Intrinsic::ForeignCheckedNul { .. } => (
                Type::String,
                Type::Application(
                    Box::new(Type::Nominal(crate::types::NominalTypeId::new(
                        self.module,
                        1,
                    ))),
                    Box::new(Type::Unit),
                ),
            ),
            Intrinsic::ForeignDataOf { .. } | Intrinsic::ForeignReplaceData { .. } => {
                let replace = matches!(self.operation, Intrinsic::ForeignReplaceData { .. });
                let state = crate::types::TypeVariableId::resolved(
                    self.module,
                    if replace { 9 } else { 7 },
                );
                let data = crate::types::TypeVariableId::resolved(
                    self.module,
                    if replace { 10 } else { 8 },
                );
                if replace {
                    (
                        Type::Tuple(Box::new([Type::Variable(state), Type::Variable(data)])),
                        Type::Unit,
                    )
                } else {
                    (Type::Variable(state), Type::Variable(data))
                }
            }
            Intrinsic::ForeignCopyBytes { .. }
            | Intrinsic::ForeignCopyNul { .. }
            | Intrinsic::ForeignExtentValue { .. } => {
                let local = match self.operation {
                    Intrinsic::ForeignCopyBytes { .. } => 11,
                    Intrinsic::ForeignCopyNul { .. } => 12,
                    _ => 13,
                };
                let view = crate::types::TypeVariableId::resolved(self.module, local);
                let extent = || {
                    Type::Application(
                        Box::new(Type::Nominal(crate::types::NominalTypeId::new(
                            self.module,
                            5,
                        ))),
                        Box::new(Type::Variable(view)),
                    )
                };
                if matches!(self.operation, Intrinsic::ForeignExtentValue { .. }) {
                    (extent(), Type::Int)
                } else {
                    let second = if matches!(self.operation, Intrinsic::ForeignCopyBytes { .. }) {
                        extent()
                    } else {
                        Type::Int
                    };
                    (
                        Type::Tuple(Box::new([Type::Variable(view), second])),
                        Type::Application(
                            Box::new(Type::Nominal(crate::types::NominalTypeId::new(
                                self.module,
                                1,
                            ))),
                            Box::new(Type::Bytes),
                        ),
                    )
                }
            }
            Intrinsic::ForeignLayoutWitness { producer } => return producer.producer_type(),
            Intrinsic::ForeignByteRead { .. } | Intrinsic::ForeignByteWrite { .. } => {
                let write = matches!(self.operation, Intrinsic::ForeignByteWrite { .. });
                let parameter =
                    crate::types::TypeVariableId::resolved(self.module, if write { 6 } else { 5 });
                let mut fields = vec![Type::Variable(parameter), Type::Int];
                if write {
                    fields.push(Type::Int);
                }
                (
                    Type::Tuple(fields.into_boxed_slice()),
                    Type::Application(
                        Box::new(Type::Nominal(crate::types::NominalTypeId::new(
                            self.module,
                            1,
                        ))),
                        Box::new(if write { Type::Unit } else { Type::Int }),
                    ),
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
            Intrinsic::ForeignCheckedI64 { .. }
            | Intrinsic::ForeignCheckedSizeT { .. }
            | Intrinsic::ForeignCheckedNul { .. }
            | Intrinsic::ForeignDataOf { .. }
            | Intrinsic::ForeignReplaceData { .. }
            | Intrinsic::ForeignByteRead { .. }
            | Intrinsic::ForeignByteWrite { .. }
            | Intrinsic::ForeignCopyBytes { .. }
            | Intrinsic::ForeignCopyNul { .. }
            | Intrinsic::ForeignExtentValue { .. } => self.module.is_builtin_foreign(),
            Intrinsic::ForeignLayoutWitness { .. } => false,
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
