//! Typed Core families and their independent validation boundary.

pub mod binding;
pub mod dialect;
pub mod function;
pub mod literal;
pub mod primitive;
pub mod transform;
pub mod validate;
pub mod variable;

pub use dialect::{
    BuildError, CORE_PAYLOAD_DEPTH_LIMIT, CoreBuilder, MiniAshPureDialect, NodeId, PureComputation,
    PureExprKind, PureProgram, PureValue, TypedExpr, UnvalidatedProgram, ValidatedProgram,
};
pub use primitive::Primitive;
pub use validate::{ValidationError, ValidationReason, validate};
pub use variable::TypedBinder;
