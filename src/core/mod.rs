//! Typed Core families and their independent validation boundary.

pub mod binding;
pub(crate) mod capture;
pub mod data;
pub mod dialect;
pub mod effect;
pub mod function;
pub mod literal;
pub mod packed;
pub mod primitive;
pub(crate) mod provider;
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
pub(crate) fn corrupt_provider_core_closure_for_test(
    program: &mut UnvalidatedEffectProgram,
    mutation: usize,
    span: crate::source::Span,
) -> bool {
    std::sync::Arc::make_mut(&mut program.registry)
        .corrupt_provider_core_closure_for_test(mutation, span)
}

#[cfg(test)]
pub(crate) fn erase_provider_certificates_for_test(program: &mut UnvalidatedEffectProgram) {
    std::sync::Arc::make_mut(&mut program.registry).erase_provider_certificates_for_test();
}

#[cfg(test)]
pub(crate) fn erase_registered_foreign_facts_for_test(program: &mut UnvalidatedEffectProgram) {
    std::sync::Arc::make_mut(&mut program.registry).erase_registered_foreign_facts_for_test();
}
