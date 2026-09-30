//! Typed Core families and their independent validation boundary.

pub mod binding;
pub(crate) mod capture;
pub mod data;
pub mod dialect;
pub mod effect;
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
    AshPureDialect, BuildError, CORE_PATTERN_DEPTH_LIMIT, CORE_PAYLOAD_DEPTH_LIMIT, CoreBuilder,
    NodeId, PureComputation, PureExprKind, PureOperation, PureProgram, PureValue, TypedExpr,
    UnvalidatedProgram, ValidatedProgram,
};
pub use effect::{
    AshEffectDialect, DiscardNode, EffectClause, EffectCoreBuilder, EffectExpr, EffectExprKind,
    EffectOperation, EffectOperationFamily, HandlerId, HandlerNode, RequestNode, ResumeNode,
    ResumeUse, UnvalidatedEffectProgram, ValidatedEffectProgram, validate_effect,
    validate_effect_modules,
};
pub use primitive::Primitive;
pub use recursion::{RecursiveBindingMember, RecursiveBindingNode};
pub use type_ops::{
    LocalNominalScopeNode, NewtypeConversionDirection, NewtypeConversionNode, TypeAbstractionNode,
    TypeApplicationNode,
};
pub use validate::{ValidationError, ValidationReason, validate, validate_modules};
pub use variable::TypedBinder;

#[cfg(test)]
#[path = "alignment_export_tests.rs"]
pub(crate) mod alignment_export;
