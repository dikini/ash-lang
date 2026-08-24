//! Typed Core families and their independent validation boundary.

pub mod binding;
pub mod data;
pub mod dialect;
pub mod function;
pub mod literal;
pub mod primitive;
pub mod recursion;
pub mod transform;
pub mod type_ops;
pub mod validate;
pub mod variable;

pub use data::{ConstructorNode, CoreMatchArm, CorePattern, CorePatternKind, MatchNode, TupleNode};
pub use dialect::{
    BuildError, CORE_PATTERN_DEPTH_LIMIT, CORE_PAYLOAD_DEPTH_LIMIT, CoreBuilder,
    MiniAshPureDialect, NodeId, PureComputation, PureExprKind, PureProgram, PureValue, TypedExpr,
    UnvalidatedProgram, ValidatedProgram,
};
pub use primitive::Primitive;
pub use recursion::{RecursiveBindingMember, RecursiveBindingNode};
pub use type_ops::{TypeAbstractionNode, TypeApplicationNode};
pub use validate::{ValidationError, ValidationReason, validate, validate_modules};
pub use variable::TypedBinder;
