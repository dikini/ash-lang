//! Typed Core families and their independent validation boundary.

pub mod binding;
pub(crate) mod capture;
pub mod data;
pub mod dialect;
pub mod effect;
pub mod function;
#[allow(
    dead_code,
    reason = "Conditional ledger rules remain staged until their consumers are complete"
)]
pub(crate) mod ledger_checker;
pub mod literal;
pub mod packed;
pub mod primitive;
pub mod region;

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
    EffectOperation, EffectOperationFamily, HandlerId, HandlerNode, NativeInterpretNode,
    NativeInterpretation, RequestNode, ResumeNode, ResumeUse, UnvalidatedEffectProgram,
    ValidatedEffectProgram, validate_effect, validate_effect_modules,
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
pub(crate) use validate::check_ordinary_effect_modules_with_budget_for_test;

#[cfg(test)]
mod native_interpret_tests;
