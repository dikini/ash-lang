//! Bounded transformations over independently validated pure Core.

use std::{error::Error, fmt, sync::Arc};

use super::{
    BuildError, CoreBuilder, CoreMatchArm, CorePattern, CorePatternKind, NodeId, Primitive,
    PureComputation, PureExprKind, PureValue, UnvalidatedProgram, ValidatedProgram,
    dialect::{
        CoreOperationFamily, CoreTypedExpr, PureOperationFamily, UnvalidatedCoreProgram,
        ValidatedCoreProgram,
    },
    effect::{EffectClause, EffectExprKind, EffectOperation, EffectOperationFamily},
};
use crate::{
    source::{GeneratedReason, Origin},
    types::{IterativeTypeOwner, Type, discard_type_iteratively},
};

trait RebuildExpression<F: CoreOperationFamily> {
    fn ty(&self) -> &Type;
    fn effects(&self) -> &crate::types::EffectRow;
    fn origin(&self) -> Result<&Origin, TransformError>;
    fn kind(&self) -> &F::Kind;
    fn realized_effects(&self) -> Option<&crate::types::EffectRow> {
        None
    }
}
impl<F: CoreOperationFamily> RebuildExpression<F> for CoreTypedExpr<F> {
    fn ty(&self) -> &Type {
        &self.ty
    }
    fn effects(&self) -> &crate::types::EffectRow {
        self.effects()
    }
    fn origin(&self) -> Result<&Origin, TransformError> {
        Ok(&self.origin)
    }
    fn kind(&self) -> &F::Kind {
        &self.kind
    }
}
impl<F: CoreOperationFamily> RebuildExpression<F> for super::dialect::StoredNode<F> {
    fn ty(&self) -> &Type {
        &self.ty
    }
    fn effects(&self) -> &crate::types::EffectRow {
        F::effect_row(&self.effects)
    }
    fn origin(&self) -> Result<&Origin, TransformError> {
        self.origin
            .as_ref()
            .ok_or(TransformError::InvalidValidatedInput)
    }
    fn kind(&self) -> &F::Kind {
        &self.kind
    }
}

/// Borrowed equation realization for a single original node. No substituted
/// Type, callable metadata or source origin is replaced by this row claim.
struct ProviderRealizedExpression<'a> {
    original: &'a super::dialect::StoredNode<EffectOperationFamily>,
    row: Option<&'a crate::types::EffectRow>,
}
impl RebuildExpression<EffectOperationFamily> for ProviderRealizedExpression<'_> {
    fn ty(&self) -> &Type {
        self.original.ty()
    }
    fn effects(&self) -> &crate::types::EffectRow {
        self.original.effects()
    }
    fn origin(&self) -> Result<&Origin, TransformError> {
        self.original.origin()
    }
    fn kind(&self) -> &EffectExprKind {
        self.original.kind()
    }
    fn realized_effects(&self) -> Option<&crate::types::EffectRow> {
        self.row
    }
}

trait TransformFamily: CoreOperationFamily {
    #[cfg(test)]
    fn rebuild_operation(
        builder: &mut CoreBuilder<Self>,
        remapped: &[Option<NodeId>],
        expression: &impl RebuildExpression<Self>,
    ) -> Result<NodeId, TransformError> {
        Self::rebuild_operation_with_context(builder, remapped, expression, None)
    }
    fn collect_operation_binders(
        kind: &Self::Kind,
        binders: &mut Vec<crate::resolved::BinderId>,
        builder: &mut CoreBuilder<Self>,
    ) -> Result<(), TransformError>;
    fn rebuild_operation_with_context(
        builder: &mut CoreBuilder<Self>,
        remapped: &[Option<NodeId>],
        expression: &impl RebuildExpression<Self>,
        context: Option<&super::provider::ProviderCopyContext<'_>>,
    ) -> Result<NodeId, TransformError>;
}

impl TransformFamily for PureOperationFamily {
    fn collect_operation_binders(
        _: &Self::Kind,
        _: &mut Vec<crate::resolved::BinderId>,
        _: &mut CoreBuilder<Self>,
    ) -> Result<(), TransformError> {
        Ok(())
    }
    fn rebuild_operation_with_context(
        _: &mut CoreBuilder<Self>,
        _: &[Option<NodeId>],
        _: &impl RebuildExpression<Self>,
        _: Option<&super::provider::ProviderCopyContext<'_>>,
    ) -> Result<NodeId, TransformError> {
        Err(TransformError::InvalidValidatedInput)
    }
}

impl TransformFamily for EffectOperationFamily {
    fn collect_operation_binders(
        kind: &Self::Kind,
        binders: &mut Vec<crate::resolved::BinderId>,
        builder: &mut CoreBuilder<Self>,
    ) -> Result<(), TransformError> {
        if let EffectExprKind::Operation(EffectOperation::Resource(resource)) = kind {
            binders.push(resource.handle.id());
        }
        let handler = match kind {
            EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) => {
                builder.charge_effect_metadata(4)?;
                binders
                    .try_reserve(4)
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                binders.extend([
                    scope.acquire.parameter.id(),
                    scope.finish.parameter.id(),
                    scope.handler_state.id(),
                    scope.handle.id(),
                ]);
                for clause in scope.handler.clauses() {
                    retain_provider_pattern_binders(
                        clause.pattern(),
                        binders,
                        &mut builder.type_work,
                    )?;
                }
                return Ok(());
            }
            EffectExprKind::Operation(EffectOperation::Handler(handler)) => handler,
            _ => return Ok(()),
        };
        for clause in handler.clauses() {
            binders.extend(clause.pattern().binder_iter().map(|binder| binder.id()));
        }
        Ok(())
    }

    fn rebuild_operation_with_context(
        builder: &mut CoreBuilder<Self>,
        remapped: &[Option<NodeId>],
        expression: &impl RebuildExpression<Self>,
        context: Option<&super::provider::ProviderCopyContext<'_>>,
    ) -> Result<NodeId, TransformError> {
        let EffectExprKind::Operation(operation) = expression.kind() else {
            return Err(TransformError::InvalidValidatedInput);
        };
        let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
        let effects = copy_expression_row(builder, expression, context)?;
        let origin = copy_origin(builder, expression.origin()?, context)?;
        match operation {
            EffectOperation::ProviderStateAccess(access) => {
                builder.charge_effect_metadata(access.arguments().len())?;
                let mut arguments = IterativeArgumentBuffer(Vec::new());
                arguments
                    .try_reserve(access.arguments().len())
                    .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
                for argument in access.arguments() {
                    arguments.push(copy_argument(builder, argument, context)?);
                }
                // Resolve the single child before moving the guarded clones.
                let operand = remap(remapped, access.operand())?;
                builder.provider_state_access(
                    super::effect::ProviderStateAccessNode::new_kinded(
                        access.method(),
                        access.definition(),
                        arguments.into_vec().into_boxed_slice(),
                        operand,
                    ),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Cleanup(scope) => {
                let callback = copy_binder_id(builder, scope.callback, context)?;
                builder.cleanup_scope(
                    super::effect::CleanupScopeNode {
                        callback,
                        body: remap(remapped, scope.body)?,
                        action: remap(remapped, scope.action)?,
                        ..*scope
                    },
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Registration(scope) => {
                let callback = copy_binder_id(builder, scope.callback, context)?;
                let handler = copy_handler_id(builder, scope.handler, context)?;
                builder.registration_scope(
                    super::effect::RegistrationScopeNode {
                        callback,
                        handler,
                        body: remap(remapped, scope.body)?,
                        ..*scope
                    },
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Resource(resource) => {
                let handle_type =
                    IterativeTypeOwner::new(copy_type(builder, resource.handle.ty(), context)?);
                let handle_id = copy_binder_id(builder, resource.handle.id(), context)?;
                let handle_origin = copy_origin(builder, resource.handle.origin(), context)?;
                let handle =
                    builder.resolved_binder(handle_id, handle_type.into_inner(), handle_origin)?;
                let mut acquisition = resource.acquisition;
                acquisition.identity = copy_variable_id(builder, acquisition.identity, context)?;
                acquisition.handle = copy_binder_id(builder, acquisition.handle, context)?;
                acquisition.provider = copy_lexical_id(builder, acquisition.provider, context)?;
                builder.resource_scope(
                    Box::new(super::effect::ResourceScopeNode {
                        acquisition,
                        handle,
                        initializer: remap(remapped, resource.initializer)?,
                        body: remap(remapped, resource.body)?,
                    }),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::ProviderScope(scope) => {
                if context.is_some() {
                    return Err(TransformError::InvalidValidatedInput);
                }
                let clone_binder = |builder: &mut CoreBuilder<Self>,
                                    binder: &super::TypedBinder|
                 -> Result<super::TypedBinder, TransformError> {
                    let ty = IterativeTypeOwner::new(copy_type(builder, binder.ty(), context)?);
                    let id = copy_binder_id(builder, binder.id(), context)?;
                    let origin = copy_origin(builder, binder.origin(), context)?;
                    Ok(builder.resolved_binder(id, ty.into_inner(), origin)?)
                };
                let acquire = super::provider::ProviderLifecycleEntry {
                    parameter: clone_binder(builder, &scope.acquire.parameter)?,
                    body: remap(remapped, scope.acquire.body)?,
                };
                let finish = super::provider::ProviderLifecycleEntry {
                    parameter: clone_binder(builder, &scope.finish.parameter)?,
                    body: remap(remapped, scope.finish.body)?,
                };
                let handler_state = clone_binder(builder, &scope.handler_state)?;
                let handle = clone_binder(builder, &scope.handle)?;
                let output_value = IterativeTypeOwner::new(copy_type(
                    builder,
                    scope.handler_output.value(),
                    context,
                )?);
                let output_effects = copy_row(builder, scope.handler_output.effects(), context)?;
                let effect = copy_effect_instance(builder, scope.handler.effect(), context)?;
                builder.charge_effect_metadata(
                    scope
                        .handler
                        .clauses()
                        .len()
                        .checked_add(scope.forwardings.len())
                        .ok_or(BuildError::TypeWorkExceeded)?,
                )?;
                let mut clauses = Vec::new();
                clauses
                    .try_reserve_exact(scope.handler.clauses().len())
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                for clause in scope.handler.clauses() {
                    let body = remap(remapped, clause.body())?;
                    clauses.push(EffectClause::new(
                        clause.operation(),
                        clause.resume(),
                        CoreMatchArm::new(
                            rebuild_pattern_with_origin_work(
                                builder,
                                clause.pattern(),
                                context.is_some(),
                                context,
                            )?,
                            body,
                            clause.origin().clone(),
                        ),
                    ));
                }
                let mut forwardings = Vec::new();
                forwardings
                    .try_reserve_exact(scope.forwardings.len())
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                forwardings.extend_from_slice(&scope.forwardings);
                let descriptor = scope
                    .descriptor
                    .relocate(remapped, &mut builder.type_work)?;
                let initializer = remap(remapped, scope.initializer)?;
                let body = remap(remapped, scope.handler.body())?;
                builder.provider_scope(
                    Box::new(super::provider::ProviderScopeNode {
                        initializer,
                        acquire,
                        finish,
                        handler_state,
                        handle,
                        handler: super::effect::HandlerNode::new(
                            scope.handler.id(),
                            body,
                            effect,
                            clauses,
                        ),
                        handler_output: crate::types::ComputationType::new(
                            output_value.into_inner(),
                            output_effects,
                        ),
                        descriptor,
                        lexical: scope.lexical,
                        forwardings: forwardings.into_boxed_slice(),
                    }),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Request(node) => {
                let effect = copy_effect_instance(builder, node.effect(), context)?;
                builder.request(
                    effect,
                    node.operation(),
                    remap(remapped, node.operand())?,
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Resume(node) => {
                let handler = copy_handler_id(builder, node.handler(), context)?;
                let owner = copy_resume_id(builder, node.owner(), context)?;
                builder.resume(
                    handler,
                    owner,
                    node.use_state(),
                    remap(remapped, node.value())?,
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Discard(node) => {
                let handler = copy_handler_id(builder, node.handler(), context)?;
                let owner = copy_resume_id(builder, node.owner(), context)?;
                builder.discard(
                    handler,
                    owner,
                    node.use_state(),
                    ty.into_inner(),
                    effects,
                    origin,
                )
            }
            EffectOperation::Handler(node) => {
                let registration = node
                    .hook_registration
                    .as_ref()
                    .map(|registration| {
                        builder.charge_effect_metadata(1)?;
                        let mut copied = registration.with_target(copy_effect_instance(
                            builder,
                            &registration.target,
                            context,
                        )?);
                        if context.is_some() {
                            copied.callback = copy_binder_id(builder, copied.callback, context)?;
                            copied.input = copy_binder_id(builder, copied.input, context)?;
                            copied.previous = copy_binder_id(builder, copied.previous, context)?;
                            copied.next = copy_binder_id(builder, copied.next, context)?;
                            copied.resume = copy_resume_id(builder, copied.resume, context)?;
                        }
                        Ok::<_, TransformError>(Box::new(copied))
                    })
                    .transpose()?;
                let effect = copy_effect_instance(builder, node.effect(), context)?;
                let root = node
                    .hook_root()
                    .map(|root| {
                        builder.charge_effect_metadata(1)?;
                        let mut copied =
                            root.with_target(copy_effect_instance(builder, &root.target, context)?);
                        if context.is_some() {
                            copied.input = copy_binder_id(builder, copied.input, context)?;
                            copied.resume = copy_resume_id(builder, copied.resume, context)?;
                        }
                        Ok::<_, TransformError>(copied)
                    })
                    .transpose()?;
                let body = remap(remapped, node.body())?;
                let mut clauses = Vec::new();
                builder.charge_effect_metadata(node.clauses().len())?;
                clauses
                    .try_reserve_exact(node.clauses().len())
                    .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
                for clause in node.clauses() {
                    let clause_body = remap(remapped, clause.body())?;
                    let resume = copy_resume_id(builder, clause.resume(), context)?;
                    let clause_origin = copy_origin(builder, clause.origin(), context)?;
                    clauses.push(EffectClause::new(
                        clause.operation(),
                        resume,
                        CoreMatchArm::new(
                            rebuild_pattern_with_origin_work(
                                builder,
                                clause.pattern(),
                                context.is_some(),
                                context,
                            )?,
                            clause_body,
                            clause_origin,
                        ),
                    ));
                }
                let handler_id = copy_handler_id(builder, node.id(), context)?;
                builder.handler_with_contracts(
                    handler_id,
                    body,
                    effect,
                    clauses,
                    ty.into_inner(),
                    effects,
                    origin,
                    root,
                    registration,
                )
            }
        }
        .map_err(TransformError::from)
    }
}

fn clone_effect_instance<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    instance: &crate::types::EffectInstance,
) -> Result<crate::types::EffectInstance, TransformError> {
    super::effect::clone_effect_instance_with_budget(instance, &mut builder.type_work)
        .map_err(TransformError::from)
}

fn copy_type<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    ty: &Type,
    context: Option<&super::provider::ProviderCopyContext<'_>>,
) -> Result<Type, BuildError> {
    match context {
        Some(context) => context.ty(ty, &mut builder.type_work),
        None => builder.clone_type_for_rebuild(ty),
    }
}
fn copy_row<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    row: &crate::types::EffectRow,
    context: Option<&super::provider::ProviderCopyContext<'_>>,
) -> Result<crate::types::EffectRow, BuildError> {
    match context {
        Some(context) => context.row(row, &mut builder.type_work),
        None => builder.clone_effect_row_for_rebuild(row),
    }
}
fn copy_expression_row<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    expression: &impl RebuildExpression<F>,
    context: Option<&super::provider::ProviderCopyContext<'_>>,
) -> Result<crate::types::EffectRow, BuildError> {
    match (expression.realized_effects(), context) {
        (Some(row), Some(context)) => context.realized_row(row, &mut builder.type_work),
        (Some(_), None) => Err(BuildError::InvalidPayload),
        (None, _) => copy_row(builder, expression.effects(), context),
    }
}
fn copy_argument<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    argument: &crate::types::KindedArgument,
    context: Option<&super::provider::ProviderCopyContext<'_>>,
) -> Result<crate::types::KindedArgument, BuildError> {
    match context {
        Some(context) => context.argument(argument, &mut builder.type_work),
        None => builder.clone_owner_argument_for_rebuild(argument),
    }
}
fn copy_effect_instance<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    instance: &crate::types::EffectInstance,
    context: Option<&super::provider::ProviderCopyContext<'_>>,
) -> Result<crate::types::EffectInstance, TransformError> {
    let Some(context) = context else {
        return clone_effect_instance(builder, instance);
    };
    builder.charge_rebuild_work(instance.arguments().len())?;
    let mut arguments = IterativeArgumentBuffer(Vec::new());
    arguments
        .try_reserve(instance.arguments().len())
        .map_err(|_| BuildError::TypeWorkExceeded)?;
    for argument in instance.arguments() {
        arguments.push(context.argument(argument, &mut builder.type_work)?);
    }
    Ok(crate::types::EffectInstance::new_kinded(
        instance.effect(),
        arguments.into_vec().into_boxed_slice(),
    ))
}
fn copy_origin<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    origin: &Origin,
    context: Option<&super::provider::ProviderCopyContext<'_>>,
) -> Result<Origin, TransformError> {
    if context.is_some() {
        clone_provider_origin_for_rebuild(builder, origin)
    } else {
        Ok(origin.clone())
    }
}
macro_rules! copy_identity {
    ($function:ident,$method:ident,$identity:ty) => {
        fn $function<F: CoreOperationFamily>(
            builder: &mut CoreBuilder<F>,
            identity: $identity,
            context: Option<&super::provider::ProviderCopyContext<'_>>,
        ) -> Result<$identity, BuildError> {
            match context {
                Some(context) => context.$method(identity, &mut builder.type_work),
                None => Ok(identity),
            }
        }
    };
}
copy_identity!(copy_binder_id, binder, crate::resolved::BinderId);
copy_identity!(copy_variable_id, variable, crate::types::TypeVariableId);
copy_identity!(copy_handler_id, handler, super::HandlerId);
copy_identity!(copy_resume_id, resume, crate::resolved::ResumeId);
copy_identity!(copy_nominal_id, nominal, crate::types::NominalTypeId);
copy_identity!(
    copy_constructor_id,
    constructor,
    crate::types::ConstructorId
);
copy_identity!(
    copy_lexical_id,
    lexical,
    crate::interface::LexicalEvidenceId
);

struct ProviderKindParameters(Vec<(crate::types::TypeVariableId, crate::types::Kind)>);
impl ProviderKindParameters {
    fn into_vec(mut self) -> Vec<(crate::types::TypeVariableId, crate::types::Kind)> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for ProviderKindParameters {
    fn drop(&mut self) {
        for (_, kind) in self.0.drain(..) {
            drop(kind);
        }
    }
}

struct IterativeTypeBuffer(Vec<Type>);

impl IterativeTypeBuffer {
    fn push(&mut self, ty: Type) {
        self.0.push(ty);
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn into_vec(mut self) -> Vec<Type> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for IterativeTypeBuffer {
    fn drop(&mut self) {
        for ty in self.0.drain(..) {
            discard_type_iteratively(ty);
        }
    }
}

struct CorePatternOwner(Option<CorePattern>);

impl CorePatternOwner {
    const fn new(pattern: CorePattern) -> Self {
        Self(Some(pattern))
    }

    fn into_inner(mut self) -> CorePattern {
        self.0.take().expect("a Core pattern transfers once")
    }
}

impl Drop for CorePatternOwner {
    fn drop(&mut self) {
        if let Some(pattern) = self.0.take() {
            pattern.discard_iteratively();
        }
    }
}

struct CorePatternBuffer(Vec<CorePattern>);

impl CorePatternBuffer {
    fn push(&mut self, pattern: CorePattern) {
        self.0.push(pattern);
    }

    fn pop(&mut self) -> Option<CorePatternOwner> {
        self.0.pop().map(CorePatternOwner::new)
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn append_suffix_to(&mut self, start: usize, destination: &mut Self) {
        let destination_start = destination.len();
        while self.len() > start {
            if let Some(pattern) = self.pop() {
                destination.push(pattern.into_inner());
            }
        }
        destination.0[destination_start..].reverse();
    }

    fn into_boxed_slice(mut self) -> Box<[CorePattern]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for CorePatternBuffer {
    fn drop(&mut self) {
        for pattern in self.0.drain(..) {
            pattern.discard_iteratively();
        }
    }
}

/// Why a validated Core traversal could not construct unchecked output.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TransformError {
    /// The output builder could not represent a transformed payload.
    Build(BuildError),
    /// A supposedly validated graph did not satisfy a traversal invariant.
    InvalidValidatedInput,
}

impl fmt::Display for TransformError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Build(error) => write!(formatter, "Core transformation failed: {error}"),
            Self::InvalidValidatedInput => {
                formatter.write_str("validated Core transformation state is inconsistent")
            }
        }
    }
}

impl Error for TransformError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Build(error) => Some(error),
            Self::InvalidValidatedInput => None,
        }
    }
}

impl From<BuildError> for TransformError {
    fn from(error: BuildError) -> Self {
        Self::Build(error)
    }
}

/// Rebuilds a validated program without changing its typed structure or origins.
///
/// The result deliberately returns to the unchecked boundary and must pass
/// independent validation before another validated-only consumer may use it.
///
/// # Errors
///
/// Returns a typed failure when output construction cannot represent the
/// input or when a validated-input invariant is unexpectedly absent.
pub fn identity_traversal(
    program: &ValidatedProgram,
) -> Result<UnvalidatedProgram, TransformError> {
    rebuild(program, false)
}

/// Folds primitive addition and multiplication whose operands are literals.
///
/// Every folded literal keeps the operation's exact result type and records a
/// generated origin whose cause is the replaced operation. The result returns
/// to the unchecked boundary for independent validation.
///
/// # Errors
///
/// Returns a typed failure when output construction cannot represent the
/// transform or when a validated-input invariant is unexpectedly absent.
pub fn fold_literal_primitives(
    program: &ValidatedProgram,
) -> Result<UnvalidatedProgram, TransformError> {
    rebuild(program, true)
}

/// Rebuilds every family in validated effect Core.
pub fn identity_effect_traversal(
    program: &super::ValidatedEffectProgram,
) -> Result<super::UnvalidatedEffectProgram, TransformError> {
    rebuild(program, false)
}

/// Folds pure literal primitives inside validated effect Core.
pub fn fold_effect_literal_primitives(
    program: &super::ValidatedEffectProgram,
) -> Result<super::UnvalidatedEffectProgram, TransformError> {
    rebuild(program, true)
}

fn rebuild<F: TransformFamily>(
    program: &ValidatedCoreProgram<F>,
    fold_literal_primitives: bool,
) -> Result<UnvalidatedCoreProgram<F>, TransformError> {
    rebuild_with_initial_type_work(program, fold_literal_primitives, 0)
}

fn rebuild_with_initial_type_work<F: TransformFamily>(
    program: &ValidatedCoreProgram<F>,
    fold_literal_primitives: bool,
    initial_type_work: usize,
) -> Result<UnvalidatedCoreProgram<F>, TransformError> {
    let mut builder = CoreBuilder::<F>::with_registry_and_method_evidence(
        Arc::clone(program.registry()),
        Arc::clone(program.method_evidence()),
    )?;
    #[cfg(test)]
    builder.charge_type_work_for_test(initial_type_work)?;
    #[cfg(not(test))]
    debug_assert_eq!(initial_type_work, 0);
    let order = postorder(program, fold_literal_primitives, &mut builder)?;
    let mut binders = Vec::new();
    for id in &order {
        let expression = program
            .node(*id)
            .ok_or(TransformError::InvalidValidatedInput)?;
        builder.charge_effect_metadata(F::operation_extra_edge_count(&expression.kind))?;
        match F::pure(&expression.kind) {
            Some(PureExprKind::Value(PureValue::Function(function))) => {
                binders.push(function.parameter().id());
            }
            Some(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                binders.push(binding.binder().id());
            }
            Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) => {
                binders.extend(group.members().iter().map(|member| member.binder().id()));
            }
            Some(PureExprKind::Computation(PureComputation::Match(match_node))) => {
                for arm in match_node.arms() {
                    let mut pattern_binders = Vec::new();
                    arm.pattern().binders(&mut pattern_binders);
                    binders.extend(pattern_binders.into_iter().map(|binder| binder.id()));
                }
            }
            Some(
                PureExprKind::Value(
                    PureValue::Integer(_)
                    | PureValue::String(_)
                    | PureValue::Intrinsic(_)
                    | PureValue::Boolean(_)
                    | PureValue::Unit(_)
                    | PureValue::Constructor(_),
                )
                | PureExprKind::Variable(_)
                | PureExprKind::Computation(
                    PureComputation::Apply(_)
                    | PureComputation::Primitive(_)
                    | PureComputation::Tuple(_)
                    | PureComputation::NewtypeConversion(_)
                    | PureComputation::LocalNominalScope(_)
                    | PureComputation::TypeAbstraction(_)
                    | PureComputation::TypeApplication(_),
                ),
            ) => {}
            None => F::collect_operation_binders(&expression.kind, &mut binders, &mut builder)?,
        }
    }
    builder.reserve_resolved_binders(binders)?;

    builder.charge_rebuild_work(program.node_count())?;
    let mut remapped = Vec::new();
    remapped
        .try_reserve_exact(program.node_count())
        .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
    remapped.resize(program.node_count(), None);
    for original in order {
        let expression = program
            .node(original)
            .ok_or(TransformError::InvalidValidatedInput)?;
        let transformed = rebuild_node(
            &mut builder,
            program,
            &remapped,
            expression,
            fold_literal_primitives,
        )?;
        let slot = remapped
            .get_mut(node_index(original)?)
            .ok_or(TransformError::InvalidValidatedInput)?;
        *slot = Some(transformed);
    }
    let root = remap(&remapped, program.root())?;
    builder.charge_rebuild_work(program.method_evidence_anchors().len())?;
    for anchor in program.method_evidence_anchors() {
        let node = remap(&remapped, anchor.node)?;
        let role = match anchor.role {
            super::dialect::MethodEvidenceAnchorRole::AdapterEdge {
                adapter,
                adapter_selection_node,
                ordinal,
                producer_node,
                producer_selection_node,
                producer_binder,
                producer,
            } => {
                builder.charge_rebuild_work(1)?;
                super::dialect::MethodEvidenceAnchorRole::AdapterEdge {
                    adapter,
                    adapter_selection_node,
                    ordinal,
                    producer_node: remap(&remapped, producer_node)?,
                    producer_selection_node,
                    producer_binder,
                    producer,
                }
            }
            role => role,
        };
        let application = builder.clone_interface_application_for_rebuild(&anchor.application)?;
        builder.authenticate_method_evidence(
            node,
            anchor.owner,
            anchor.requirement,
            anchor.method,
            application,
            role,
            anchor.occurrence,
        )?;
    }
    builder.finish(root).map_err(TransformError::from)
}

fn rebuild_node<F: TransformFamily>(
    builder: &mut CoreBuilder<F>,
    program: &ValidatedCoreProgram<F>,
    remapped: &[Option<NodeId>],
    expression: &CoreTypedExpr<F>,
    fold_literal_primitives: bool,
) -> Result<NodeId, TransformError> {
    if fold_literal_primitives
        && let Some(PureExprKind::Computation(PureComputation::Primitive(operation))) =
            F::pure(&expression.kind)
        && let Some(value) = folded_literal(program, *operation)
    {
        let ty = builder.clone_type_for_rebuild(&expression.ty)?;
        return builder
            .integer(
                value,
                ty,
                Origin::Generated {
                    cause: Box::new(expression.origin.clone()),
                    reason: GeneratedReason::ConstantFolding,
                },
            )
            .map_err(TransformError::from);
    }

    rebuild_nonfold_node(builder, remapped, expression)
}

fn rebuild_nonfold_node<F: TransformFamily>(
    builder: &mut CoreBuilder<F>,
    remapped: &[Option<NodeId>],
    expression: &impl RebuildExpression<F>,
) -> Result<NodeId, TransformError> {
    rebuild_nonfold_node_with_context(builder, remapped, expression, None)
}

fn rebuild_nonfold_node_with_context<F: TransformFamily>(
    builder: &mut CoreBuilder<F>,
    remapped: &[Option<NodeId>],
    expression: &impl RebuildExpression<F>,
    context: Option<&super::provider::ProviderCopyContext<'_>>,
) -> Result<NodeId, TransformError> {
    let Some(kind) = F::pure(expression.kind()) else {
        return F::rebuild_operation_with_context(builder, remapped, expression, context);
    };
    let origin = copy_origin(builder, expression.origin()?, context)?;
    match kind {
        PureExprKind::Value(PureValue::String(node)) => {
            let ty = copy_type(builder, expression.ty(), context)?;
            builder
                .string(Arc::clone(node.bytes()), ty, origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Intrinsic(node)) => {
            let ty = copy_type(builder, expression.ty(), context)?;
            builder
                .intrinsic(node.operation(), node.module(), ty, origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Integer(node)) => {
            let ty = copy_type(builder, expression.ty(), context)?;
            builder
                .integer(node.value().clone(), ty, origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Boolean(node)) => {
            let ty = copy_type(builder, expression.ty(), context)?;
            builder
                .boolean(node.value(), ty, origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Unit(_)) => {
            let ty = copy_type(builder, expression.ty(), context)?;
            builder.unit(ty, origin).map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Constructor(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let constructor = copy_constructor_id(builder, node.constructor(), context)?;
            builder
                .constructor(constructor, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Function(node)) => {
            let parameter_type =
                IterativeTypeOwner::new(copy_type(builder, node.parameter().ty(), context)?);
            let parameter_id = copy_binder_id(builder, node.parameter().id(), context)?;
            let parameter_origin = copy_origin(builder, node.parameter().origin(), context)?;
            let parameter = builder.resolved_binder(
                parameter_id,
                parameter_type.into_inner(),
                parameter_origin,
            )?;
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let body = remap(remapped, node.body())?;

            builder
                .function(parameter, body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Variable(node) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let binder = copy_binder_id(builder, node.binder(), context)?;
            builder
                .variable(binder, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Bind(node)) => {
            let binder_type =
                IterativeTypeOwner::new(copy_type(builder, node.binder().ty(), context)?);
            let binder_id = copy_binder_id(builder, node.binder().id(), context)?;
            let binder_origin = copy_origin(builder, node.binder().origin(), context)?;
            let binder =
                builder.resolved_binder(binder_id, binder_type.into_inner(), binder_origin)?;
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let initializer = remap(remapped, node.initializer())?;
            let body = remap(remapped, node.body())?;

            builder
                .binding(binder, initializer, body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::RecursiveBind(node)) => {
            let mut members = Vec::new();
            members
                .try_reserve(node.members().len())
                .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
            for member in node.members() {
                let binder_type =
                    IterativeTypeOwner::new(copy_type(builder, member.binder().ty(), context)?);
                let binder_id = copy_binder_id(builder, member.binder().id(), context)?;
                let member_origin = copy_origin(builder, member.binder().origin(), context)?;
                let binder =
                    builder.resolved_binder(binder_id, binder_type.into_inner(), member_origin)?;
                members.push((binder, remap(remapped, member.initializer())?));
            }
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let body = remap(remapped, node.body())?;

            builder
                .recursive_binding(members, body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Apply(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let function = remap(remapped, node.function())?;
            let argument = remap(remapped, node.argument())?;

            if !F::REQUIRES_EMPTY_ROWS {
                let effects = copy_expression_row(builder, expression, context)?;
                return builder
                    .application_with_effects(
                        super::function::ApplicationNode::new(function, argument),
                        ty.into_inner(),
                        effects,
                        origin,
                    )
                    .map_err(TransformError::from);
            }
            builder
                .application(function, argument, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Primitive(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let left = remap(remapped, node.left())?;
            let right = remap(remapped, node.right())?;

            builder
                .primitive(node.primitive(), left, right, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Tuple(node)) => {
            builder.charge_rebuild_work(node.elements().len())?;
            let mut elements = Vec::new();
            elements
                .try_reserve_exact(node.elements().len())
                .map_err(|_| BuildError::TypeWorkExceeded)?;
            for element in node.elements() {
                elements.push(remap(remapped, *element)?);
            }
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);

            builder
                .tuple(elements, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Match(node)) => {
            builder.charge_rebuild_work(node.arms().len())?;
            let mut arms = Vec::new();
            arms.try_reserve_exact(node.arms().len())
                .map_err(|_| BuildError::TypeWorkExceeded)?;
            for arm in node.arms() {
                let pattern = CorePatternOwner::new(rebuild_pattern_with_origin_work(
                    builder,
                    arm.pattern(),
                    context.is_some(),
                    context,
                )?);
                let body = remap(remapped, arm.body())?;
                let origin = copy_origin(builder, arm.origin(), context)?;
                arms.push(CoreMatchArm::new(pattern.into_inner(), body, origin));
            }
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let scrutinee = remap(remapped, node.scrutinee())?;

            builder
                .match_expression(scrutinee, arms, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::NewtypeConversion(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let child = remap(remapped, node.child())?;

            let owner = copy_nominal_id(builder, node.owner(), context)?;
            builder
                .newtype_conversion(owner, node.direction(), child, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::LocalNominalScope(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let body = remap(remapped, node.body())?;
            let owner = copy_nominal_id(builder, node.owner(), context)?;
            builder
                .local_nominal_scope(owner, body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::TypeAbstraction(node)) => {
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let body = remap(remapped, node.body())?;

            if let Some(context) = context {
                let parameters = crate::types::clone_kinded_type_parameters_with_budget(
                    node.parameters(),
                    &mut builder.type_work,
                )
                .map_err(|()| BuildError::TypeWorkExceeded)?;
                let mut parameters = ProviderKindParameters(parameters);
                for (id, _) in &mut parameters.0 {
                    *id = context.variable(*id, &mut builder.type_work)?;
                }
                builder
                    .type_abstraction(parameters.into_vec(), body, ty.into_inner(), origin)
                    .map_err(TransformError::from)
            } else {
                builder
                    .type_abstraction_from_borrowed(
                        node.parameters(),
                        body,
                        ty.into_inner(),
                        origin,
                    )
                    .map_err(TransformError::from)
            }
        }
        PureExprKind::Computation(PureComputation::TypeApplication(node)) => {
            let mut arguments = IterativeTypeBuffer(Vec::new());
            arguments
                .try_reserve(node.arguments().len())
                .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
            for argument in node.arguments() {
                arguments.push(copy_type(builder, argument, context)?);
            }
            builder.charge_effect_metadata(node.row_arguments().len())?;
            let mut row_arguments = Vec::new();
            row_arguments
                .try_reserve_exact(node.row_arguments().len())
                .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
            for row in node.row_arguments() {
                row_arguments.push(copy_row(builder, row, context)?);
            }
            let ty = IterativeTypeOwner::new(copy_type(builder, expression.ty(), context)?);
            let function = remap(remapped, node.function())?;

            builder
                .type_application_with_row_arguments(
                    function,
                    arguments.into_vec(),
                    row_arguments,
                    ty.into_inner(),
                    origin,
                )
                .map_err(TransformError::from)
        }
    }
}

/// Walk an unpublished draft without assigning it validated-program authority.
/// Replacement roots are atomic: their obsolete source ABI children are omitted.
#[cfg(test)]
pub(crate) fn provider_draft_order(
    program: &super::UnvalidatedEffectProgram,
    replacements: &std::collections::HashSet<NodeId>,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<Vec<NodeId>, TransformError> {
    provider_fragment_order(program, &[program.root], replacements, budget)
}

/// Traverse the real entry forest without inventing a Core parent node.
/// This proves graph shape only; the caller separately authenticates roots.
pub(crate) fn provider_fragment_order(
    program: &super::UnvalidatedEffectProgram,
    roots: &[NodeId],
    replacements: &std::collections::HashSet<NodeId>,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<Vec<NodeId>, TransformError> {
    provider_forest_order_inner(program, roots, replacements, budget, true)
}

/// A defining entry can retain authenticated parameter wrappers outside its
/// executable body forest. Traverse exactly the supplied entry roots without
/// treating unrelated wrapper nodes as executable children.
pub(crate) fn provider_entry_forest_order(
    program: &super::UnvalidatedEffectProgram,
    roots: &[NodeId],
    replacements: &std::collections::HashSet<NodeId>,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<Vec<NodeId>, TransformError> {
    provider_forest_order_inner(program, roots, replacements, budget, false)
}

fn provider_forest_order_inner(
    program: &super::UnvalidatedEffectProgram,
    roots: &[NodeId],
    replacements: &std::collections::HashSet<NodeId>,
    budget: &mut crate::types::TypeWorkBudget,
    require_complete: bool,
) -> Result<Vec<NodeId>, TransformError> {
    enum Task {
        Enter(NodeId),
        Exit(NodeId),
    }
    budget
        .charge(
            program
                .nodes
                .len()
                .checked_mul(2)
                .ok_or(BuildError::TypeWorkExceeded)?,
        )
        .map_err(|()| BuildError::TypeWorkExceeded)?;
    let mut colors = Vec::new();
    colors
        .try_reserve_exact(program.nodes.len())
        .map_err(|_| BuildError::TypeWorkExceeded)?;
    colors.resize(program.nodes.len(), 0u8);
    let mut pending = Vec::new();
    budget
        .charge(roots.len())
        .map_err(|()| BuildError::TypeWorkExceeded)?;
    pending
        .try_reserve(roots.len())
        .map_err(|_| BuildError::TypeWorkExceeded)?;
    if roots.is_empty() {
        return Err(TransformError::InvalidValidatedInput);
    }
    pending.extend(roots.iter().rev().copied().map(Task::Enter));
    let mut order = Vec::new();
    order
        .try_reserve_exact(program.nodes.len())
        .map_err(|_| BuildError::TypeWorkExceeded)?;
    while let Some(task) = pending.pop() {
        budget
            .charge(1)
            .map_err(|()| BuildError::TypeWorkExceeded)?;
        let id = match task {
            Task::Enter(id) | Task::Exit(id) => id,
        };
        if id.arena() != program.arena {
            return Err(TransformError::InvalidValidatedInput);
        }
        let ordinal = node_index(id)?;
        let expression = program
            .nodes
            .get(ordinal)
            .ok_or(TransformError::InvalidValidatedInput)?;
        match task {
            Task::Enter(_) => {
                match colors[ordinal] {
                    1 => return Err(TransformError::InvalidValidatedInput),
                    2 => continue,
                    _ => colors[ordinal] = 1,
                }
                if expression.origin.is_none() {
                    return Err(TransformError::InvalidValidatedInput);
                }
                let children = if replacements.contains(&id) {
                    0
                } else {
                    EffectOperationFamily::child_count(&expression.kind)
                };
                budget
                    .charge(children + 1)
                    .map_err(|()| BuildError::TypeWorkExceeded)?;
                pending
                    .try_reserve(children + 1)
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                pending.push(Task::Exit(id));
                for child in (0..children).rev() {
                    pending.push(Task::Enter(
                        EffectOperationFamily::child_at(&expression.kind, child)
                            .ok_or(TransformError::InvalidValidatedInput)?,
                    ));
                }
            }
            Task::Exit(_) => {
                colors[ordinal] = 2;
                order.push(id);
            }
        }
    }
    if require_complete && replacements.is_empty() && order.len() != program.nodes.len() {
        return Err(TransformError::InvalidValidatedInput);
    }
    for replacement in replacements {
        budget
            .charge(1)
            .map_err(|()| BuildError::TypeWorkExceeded)?;
        if replacement.arena() != program.arena
            || colors.get(node_index(*replacement)?).copied() != Some(2)
        {
            return Err(TransformError::InvalidValidatedInput);
        }
    }
    Ok(order)
}

fn retain_provider_pattern_binders(
    root: &CorePattern,
    binders: &mut Vec<crate::resolved::BinderId>,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<(), TransformError> {
    budget
        .charge(1)
        .map_err(|()| BuildError::TypeWorkExceeded)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| BuildError::TypeWorkExceeded)?;
    pending.push(root);
    while let Some(pattern) = pending.pop() {
        budget
            .charge(1)
            .map_err(|()| BuildError::TypeWorkExceeded)?;
        match &pattern.kind {
            CorePatternKind::Binder(binder) => {
                budget
                    .charge(1)
                    .map_err(|()| BuildError::TypeWorkExceeded)?;
                binders
                    .try_reserve(1)
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                binders.push(binder.id());
            }
            CorePatternKind::Tuple(elements) => {
                budget
                    .charge(elements.len())
                    .map_err(|()| BuildError::TypeWorkExceeded)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                pending.extend(elements.iter());
            }
            CorePatternKind::Constructor {
                payload: Some(payload),
                ..
            } => {
                budget
                    .charge(1)
                    .map_err(|()| BuildError::TypeWorkExceeded)?;
                pending
                    .try_reserve(1)
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                pending.push(payload);
            }
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
pub(crate) fn prepare_provider_draft_builder(
    program: &super::UnvalidatedEffectProgram,
    order: &[NodeId],
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<CoreBuilder<EffectOperationFamily>, TransformError> {
    prepare_provider_draft_builder_with_catalog(
        program,
        order,
        Arc::new(super::dialect::MethodEvidenceCatalog::default()),
        budget,
    )
}

#[cfg(test)]
pub(crate) fn prepare_provider_draft_builder_with_catalog(
    program: &super::UnvalidatedEffectProgram,
    order: &[NodeId],
    catalog: Arc<super::dialect::MethodEvidenceCatalog>,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<CoreBuilder<EffectOperationFamily>, TransformError> {
    prepare_provider_fragment_builder_with_catalog(program, order, catalog, &[], &[], budget)
}

pub(crate) fn prepare_provider_fragment_builder_with_catalog(
    program: &super::UnvalidatedEffectProgram,
    order: &[NodeId],
    catalog: Arc<super::dialect::MethodEvidenceCatalog>,
    state: &[&super::TypedBinder],
    patterns: &[&CorePattern],
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<CoreBuilder<EffectOperationFamily>, TransformError> {
    let mut builder = CoreBuilder::<EffectOperationFamily>::with_registry_and_method_evidence(
        Arc::clone(&program.registry),
        catalog,
    )?;
    // Catalog admission is part of this new rebuild, before its per-node ledger resets.
    budget
        .charge(builder.type_work.used())
        .map_err(|()| BuildError::TypeWorkExceeded)?;
    let mut binders = Vec::new();
    budget
        .charge(state.len())
        .map_err(|()| BuildError::TypeWorkExceeded)?;
    binders
        .try_reserve(state.len())
        .map_err(|_| BuildError::TypeWorkExceeded)?;
    binders.extend(state.iter().map(|binder| binder.id()));
    for pattern in patterns {
        retain_provider_pattern_binders(pattern, &mut binders, budget)?;
    }
    for id in order {
        let expression = program
            .nodes
            .get(node_index(*id)?)
            .ok_or(TransformError::InvalidValidatedInput)?;
        let count = EffectOperationFamily::operation_extra_edge_count(&expression.kind);
        budget
            .charge(count + 1)
            .map_err(|()| BuildError::TypeWorkExceeded)?;
        binders
            .try_reserve(count + 1)
            .map_err(|_| BuildError::TypeWorkExceeded)?;
        match EffectOperationFamily::pure(&expression.kind) {
            Some(PureExprKind::Value(PureValue::Function(function))) => {
                binders.push(function.parameter().id())
            }
            Some(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                binders.push(binding.binder().id())
            }
            Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) => {
                budget
                    .charge(group.members().len())
                    .map_err(|()| BuildError::TypeWorkExceeded)?;
                binders
                    .try_reserve(group.members().len())
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                binders.extend(group.members().iter().map(|member| member.binder().id()));
            }
            Some(PureExprKind::Computation(PureComputation::Match(matching))) => {
                for arm in matching.arms() {
                    retain_provider_pattern_binders(arm.pattern(), &mut binders, budget)?;
                }
            }
            _ => {
                if let EffectExprKind::Operation(operation) = &expression.kind {
                    match operation {
                        EffectOperation::Resource(resource) => binders.push(resource.handle.id()),
                        EffectOperation::ProviderScope(scope) => {
                            budget
                                .charge(4)
                                .map_err(|()| BuildError::TypeWorkExceeded)?;
                            binders
                                .try_reserve(4)
                                .map_err(|_| BuildError::TypeWorkExceeded)?;
                            binders.extend([
                                scope.acquire.parameter.id(),
                                scope.finish.parameter.id(),
                                scope.handler_state.id(),
                                scope.handle.id(),
                            ]);
                            for clause in scope.handler.clauses() {
                                retain_provider_pattern_binders(
                                    clause.pattern(),
                                    &mut binders,
                                    budget,
                                )?;
                            }
                        }
                        EffectOperation::Handler(handler) => {
                            for clause in handler.clauses() {
                                retain_provider_pattern_binders(
                                    clause.pattern(),
                                    &mut binders,
                                    budget,
                                )?;
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    builder.reserve_provider_draft_binders(&binders, budget)?;
    Ok(builder)
}

pub(crate) fn rebuild_provider_fragment_binder(
    builder: &mut CoreBuilder<EffectOperationFamily>,
    binder: &super::TypedBinder,
) -> Result<super::TypedBinder, TransformError> {
    let origin = clone_origin_for_rebuild(builder, binder.origin())?;
    let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(binder.ty())?);
    Ok(builder.resolved_binder(binder.id(), ty.into_inner(), origin)?)
}

pub(crate) fn rebuild_provider_fragment_pattern(
    builder: &mut CoreBuilder<EffectOperationFamily>,
    pattern: &CorePattern,
) -> Result<CorePattern, TransformError> {
    rebuild_pattern_with_origin_work(builder, pattern, true, None)
}

fn clone_origin_for_rebuild<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    origin: &Origin,
) -> Result<Origin, TransformError> {
    let mut current = origin;
    for _ in 0..=super::dialect::CORE_PAYLOAD_DEPTH_LIMIT {
        builder.charge_rebuild_work(1)?;
        match current {
            Origin::Source(_) => return Ok(origin.clone()),
            Origin::Generated { cause, .. } => current = cause,
            Origin::Related { primary, related } => {
                builder.charge_rebuild_work(related.len())?;
                current = primary;
            }
        }
    }
    Err(BuildError::InvalidPayload.into())
}

/// Fallible provenance copying for a new checked-template occurrence. Original
/// spans and generated reasons are retained without granting new authority.
fn clone_provider_origin_for_rebuild<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    original: &Origin,
) -> Result<Origin, TransformError> {
    enum Frame<'a> {
        Generated(GeneratedReason),
        Related(&'a [crate::source::Span]),
    }
    struct Guard(Option<Origin>);
    impl Guard {
        fn take(&mut self) -> Result<Origin, BuildError> {
            self.0.take().ok_or(BuildError::InvalidPayload)
        }

        fn replace(&mut self, origin: Origin) {
            if let Some(displaced) = self.0.replace(origin) {
                crate::source::discard_origin_iteratively(displaced);
            }
        }

        fn into_root(mut self) -> Result<Origin, BuildError> {
            self.take()
        }
    }
    impl Drop for Guard {
        fn drop(&mut self) {
            if let Some(origin) = self.0.take() {
                crate::source::discard_origin_iteratively(origin);
            }
        }
    }
    let mut frames = Vec::new();
    let mut current = original;
    let span = loop {
        builder.charge_rebuild_work(1)?;
        if frames.len() > super::dialect::CORE_PAYLOAD_DEPTH_LIMIT {
            return Err(BuildError::InvalidPayload.into());
        }
        match current {
            Origin::Source(span) => break *span,
            Origin::Generated { cause, reason } => {
                frames
                    .try_reserve(1)
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                frames.push(Frame::Generated(*reason));
                current = cause;
            }
            Origin::Related { primary, related } => {
                frames
                    .try_reserve(1)
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                frames.push(Frame::Related(related));
                current = primary;
            }
        }
    };
    let mut copied = Guard(Some(Origin::Source(span)));
    while let Some(frame) = frames.pop() {
        let next = match frame {
            Frame::Generated(reason) => Origin::Generated {
                cause: Box::new(copied.take()?),
                reason,
            },
            Frame::Related(related) => {
                builder.charge_rebuild_work(related.len())?;
                let mut spans = Vec::new();
                spans
                    .try_reserve_exact(related.len())
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                spans.extend_from_slice(related);
                Origin::Related {
                    primary: Box::new(copied.take()?),
                    related: spans,
                }
            }
        };
        copied.replace(next);
    }
    copied.into_root().map_err(TransformError::from)
}

pub(crate) fn begin_provider_draft_work(
    builder: &mut CoreBuilder<EffectOperationFamily>,
    remaining: usize,
) {
    builder.type_work = crate::types::TypeWorkBudget::with_limit(remaining);
}

pub(crate) fn discharge_provider_draft_work(
    builder: &CoreBuilder<EffectOperationFamily>,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<(), BuildError> {
    budget
        .charge(builder.type_work.used())
        .map_err(|()| BuildError::TypeWorkExceeded)
}

pub(crate) fn rebuild_provider_draft_node(
    builder: &mut CoreBuilder<EffectOperationFamily>,
    program: &super::UnvalidatedEffectProgram,
    remapped: &[Option<NodeId>],
    id: NodeId,
) -> Result<NodeId, TransformError> {
    if id.arena() != program.arena {
        return Err(TransformError::InvalidValidatedInput);
    }
    let expression = program
        .nodes
        .get(node_index(id)?)
        .ok_or(TransformError::InvalidValidatedInput)?;
    rebuild_nonfold_node(builder, remapped, expression)
}

/// Copies one stored node through the ordinary shared opcode rebuild engine.
/// Complete sigma/freshening remain compiler claims until final admission.
pub(crate) fn rebuild_provider_draft_node_with_context(
    builder: &mut CoreBuilder<EffectOperationFamily>,
    program: &super::UnvalidatedEffectProgram,
    remapped: &[Option<NodeId>],
    id: NodeId,
    context: &super::provider::ProviderCopyContext<'_>,
) -> Result<NodeId, TransformError> {
    if id.arena() != program.arena {
        return Err(TransformError::InvalidValidatedInput);
    }
    let expression = program
        .nodes
        .get(node_index(id)?)
        .ok_or(TransformError::InvalidValidatedInput)?;
    let row = if context.node_rows.is_empty() {
        None
    } else {
        builder.charge_rebuild_work(1)?;
        context.node_rows.get(&id)
    };
    let realized = ProviderRealizedExpression {
        original: expression,
        row,
    };
    let copied = rebuild_nonfold_node_with_context(builder, remapped, &realized, Some(context))?;
    // Operation and Apply rebuilds already admit their explicit realized row.
    // Other pure constructors derive rows from children; preserve the equation
    // claim at their top row without replacing latent Type metadata.
    if let Some(row) = row
        && let Some(kind) = EffectOperationFamily::pure(&expression.kind)
        && !matches!(kind, PureExprKind::Computation(PureComputation::Apply(_)))
    {
        let effects = context.realized_row(row, &mut builder.type_work)?;
        builder.set_provider_copy_node_row(copied, effects)?;
    }
    Ok(copied)
}

pub(crate) fn rebuild_provider_fragment_origin(
    builder: &mut CoreBuilder<EffectOperationFamily>,
    origin: &Origin,
) -> Result<Origin, TransformError> {
    clone_provider_origin_for_rebuild(builder, origin)
}

pub(crate) fn rebuild_provider_fragment_binder_with_context(
    builder: &mut CoreBuilder<EffectOperationFamily>,
    binder: &super::TypedBinder,
    context: &super::provider::ProviderCopyContext<'_>,
) -> Result<super::TypedBinder, TransformError> {
    let origin = clone_provider_origin_for_rebuild(builder, binder.origin())?;
    let ty = IterativeTypeOwner::new(context.ty(binder.ty(), &mut builder.type_work)?);
    let id = context.binder(binder.id(), &mut builder.type_work)?;
    Ok(builder.resolved_binder(id, ty.into_inner(), origin)?)
}

pub(crate) fn rebuild_provider_fragment_pattern_with_context(
    builder: &mut CoreBuilder<EffectOperationFamily>,
    pattern: &CorePattern,
    context: &super::provider::ProviderCopyContext<'_>,
) -> Result<CorePattern, TransformError> {
    rebuild_pattern_with_origin_work(builder, pattern, true, Some(context))
}

pub(crate) fn provider_draft_span(
    program: &super::UnvalidatedEffectProgram,
    id: NodeId,
) -> Result<crate::source::Span, TransformError> {
    if id.arena() != program.arena {
        return Err(TransformError::InvalidValidatedInput);
    }
    Ok(program
        .nodes
        .get(node_index(id)?)
        .and_then(|n| n.origin.as_ref())
        .ok_or(TransformError::InvalidValidatedInput)?
        .primary_span())
}

pub(crate) fn provider_draft_type(
    program: &super::UnvalidatedEffectProgram,
    id: NodeId,
) -> Result<&Type, TransformError> {
    if id.arena() != program.arena {
        return Err(TransformError::InvalidValidatedInput);
    }
    Ok(&program
        .nodes
        .get(node_index(id)?)
        .ok_or(TransformError::InvalidValidatedInput)?
        .ty)
}

#[cfg(test)]
fn rebuild_pattern<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    pattern: &CorePattern,
) -> Result<CorePattern, TransformError> {
    rebuild_pattern_with_origin_work(builder, pattern, false, None)
}

fn rebuild_pattern_with_origin_work<F: CoreOperationFamily>(
    builder: &mut CoreBuilder<F>,
    pattern: &CorePattern,
    provider_origins: bool,
    context: Option<&super::provider::ProviderCopyContext<'_>>,
) -> Result<CorePattern, TransformError> {
    let clone_origin = |builder: &mut CoreBuilder<F>, origin: &Origin| {
        if context.is_some() {
            clone_provider_origin_for_rebuild(builder, origin)
        } else if provider_origins {
            clone_origin_for_rebuild(builder, origin)
        } else {
            Ok(origin.clone())
        }
    };
    enum Task<'a> {
        Visit(&'a CorePattern),
        FinishTuple(&'a CorePattern, usize),
        FinishConstructor(&'a CorePattern, crate::types::ConstructorId, bool),
    }

    builder.charge_rebuild_work(1)?;
    let mut work = Vec::new();
    work.try_reserve(1)
        .map_err(|_| BuildError::TypeWorkExceeded)?;
    work.push(Task::Visit(pattern));
    let mut rebuilt = CorePatternBuffer(Vec::new());
    while let Some(task) = work.pop() {
        builder.charge_rebuild_work(1)?;
        rebuilt
            .0
            .try_reserve(1)
            .map_err(|_| BuildError::TypeWorkExceeded)?;
        match task {
            Task::Visit(pattern) => match &pattern.kind {
                CorePatternKind::Binder(binder) => {
                    let origin = clone_origin(builder, &pattern.origin)?;
                    let binder_origin = clone_origin(builder, binder.origin())?;
                    let binder_type =
                        IterativeTypeOwner::new(copy_type(builder, binder.ty(), context)?);
                    let binder_id = copy_binder_id(builder, binder.id(), context)?;
                    let binder = builder.resolved_binder(
                        binder_id,
                        binder_type.into_inner(),
                        binder_origin,
                    )?;
                    let ty = copy_type(builder, &pattern.ty, context)?;
                    rebuilt.push(CorePattern::new(
                        ty,
                        origin,
                        CorePatternKind::Binder(binder),
                    ));
                }
                CorePatternKind::Wildcard => {
                    let origin = clone_origin(builder, &pattern.origin)?;
                    let ty = copy_type(builder, &pattern.ty, context)?;
                    rebuilt.push(CorePattern::new(ty, origin, CorePatternKind::Wildcard));
                }
                CorePatternKind::Boolean(value) => {
                    let origin = clone_origin(builder, &pattern.origin)?;
                    let ty = copy_type(builder, &pattern.ty, context)?;
                    rebuilt.push(CorePattern::new(
                        ty,
                        origin,
                        CorePatternKind::Boolean(*value),
                    ));
                }
                CorePatternKind::Unit => {
                    let origin = clone_origin(builder, &pattern.origin)?;
                    let ty = copy_type(builder, &pattern.ty, context)?;
                    rebuilt.push(CorePattern::new(ty, origin, CorePatternKind::Unit));
                }
                CorePatternKind::Tuple(elements) => {
                    builder.charge_rebuild_work(elements.len() + 1)?;
                    work.try_reserve(elements.len() + 1)
                        .map_err(|_| BuildError::TypeWorkExceeded)?;
                    work.push(Task::FinishTuple(pattern, elements.len()));
                    work.extend(elements.iter().rev().map(Task::Visit));
                }
                CorePatternKind::Constructor {
                    constructor,
                    payload,
                } => {
                    builder.charge_rebuild_work(2)?;
                    work.try_reserve(2)
                        .map_err(|_| BuildError::TypeWorkExceeded)?;
                    work.push(Task::FinishConstructor(
                        pattern,
                        copy_constructor_id(builder, *constructor, context)?,
                        payload.is_some(),
                    ));
                    if let Some(payload) = payload.as_deref() {
                        work.push(Task::Visit(payload));
                    }
                }
            },
            Task::FinishTuple(pattern, count) => {
                let origin = clone_origin(builder, &pattern.origin)?;
                if rebuilt.len() < count {
                    return Err(TransformError::InvalidValidatedInput);
                }
                builder.charge_rebuild_work(count)?;
                let mut elements = CorePatternBuffer(Vec::new());
                elements
                    .0
                    .try_reserve_exact(count)
                    .map_err(|_| BuildError::TypeWorkExceeded)?;
                let start = rebuilt.len() - count;
                rebuilt.append_suffix_to(start, &mut elements);
                let ty = IterativeTypeOwner::new(copy_type(builder, &pattern.ty, context)?);
                rebuilt.push(CorePattern::new(
                    ty.into_inner(),
                    origin,
                    CorePatternKind::Tuple(elements.into_boxed_slice()),
                ));
            }
            Task::FinishConstructor(pattern, constructor, has_payload) => {
                let origin = clone_origin(builder, &pattern.origin)?;
                let payload = if has_payload {
                    Some(rebuilt.pop().ok_or(TransformError::InvalidValidatedInput)?)
                } else {
                    None
                };
                let ty = IterativeTypeOwner::new(copy_type(builder, &pattern.ty, context)?);
                rebuilt.push(CorePattern::new(
                    ty.into_inner(),
                    origin,
                    CorePatternKind::Constructor {
                        constructor,
                        payload: payload.map(|payload| Box::new(payload.into_inner())),
                    },
                ));
            }
        }
    }
    let result = rebuilt.pop().ok_or(TransformError::InvalidValidatedInput)?;
    if rebuilt.is_empty() {
        Ok(result.into_inner())
    } else {
        Err(TransformError::InvalidValidatedInput)
    }
}

fn postorder<F: TransformFamily>(
    program: &ValidatedCoreProgram<F>,
    fold_literal_primitives: bool,
    builder: &mut CoreBuilder<F>,
) -> Result<Vec<NodeId>, TransformError> {
    enum Task {
        Enter(NodeId),
        Exit(NodeId),
    }

    let mut scheduled = vec![false; program.node_count()];
    let mut work = vec![Task::Enter(program.root())];
    let mut order = Vec::with_capacity(program.node_count());
    while let Some(task) = work.pop() {
        match task {
            Task::Enter(id) => {
                let index = node_index(id)?;
                let Some(was_scheduled) = scheduled.get_mut(index) else {
                    return Err(TransformError::InvalidValidatedInput);
                };
                if *was_scheduled {
                    continue;
                }
                *was_scheduled = true;
                let expression = program
                    .node(id)
                    .ok_or(TransformError::InvalidValidatedInput)?;
                let child_count = if fold_literal_primitives
                    && matches!(
                            F::pure(&expression.kind),
                            Some(PureExprKind::Computation(PureComputation::Primitive(operation)))
                                if is_foldable_literal(program, *operation)
                    ) {
                    0
                } else {
                    F::child_count(&expression.kind)
                };
                builder.charge_effect_metadata(F::operation_extra_edge_count(&expression.kind))?;
                work.try_reserve(
                    child_count
                        .checked_add(1)
                        .ok_or(BuildError::TypeWorkExceeded)?,
                )
                .map_err(|_| BuildError::TypeWorkExceeded)?;
                work.push(Task::Exit(id));
                for child_index in (0..child_count).rev() {
                    let child = F::child_at(&expression.kind, child_index)
                        .ok_or(TransformError::InvalidValidatedInput)?;
                    work.push(Task::Enter(child));
                }
            }
            Task::Exit(id) => order.push(id),
        }
    }
    Ok(order)
}

fn folded_literal<F: TransformFamily>(
    program: &ValidatedCoreProgram<F>,
    operation: super::primitive::PrimitiveNode,
) -> Option<crate::integer::Integer> {
    let Some(PureExprKind::Value(PureValue::Integer(left))) =
        F::pure(&program.node(operation.left())?.kind)
    else {
        return None;
    };
    let Some(PureExprKind::Value(PureValue::Integer(right))) =
        F::pure(&program.node(operation.right())?.kind)
    else {
        return None;
    };
    match operation.primitive() {
        Primitive::Add => Some(left.value() + right.value()),
        Primitive::Multiply => Some(left.value() * right.value()),
        Primitive::Equal => None,
    }
}

fn is_foldable_literal<F: TransformFamily>(
    program: &ValidatedCoreProgram<F>,
    operation: super::primitive::PrimitiveNode,
) -> bool {
    matches!(operation.primitive(), Primitive::Add | Primitive::Multiply)
        && matches!(
            program
                .node(operation.left())
                .and_then(|node| F::pure(&node.kind)),
            Some(PureExprKind::Value(PureValue::Integer(_)))
        )
        && matches!(
            program
                .node(operation.right())
                .and_then(|node| F::pure(&node.kind)),
            Some(PureExprKind::Value(PureValue::Integer(_)))
        )
}

fn remap(remapped: &[Option<NodeId>], original: NodeId) -> Result<NodeId, TransformError> {
    remapped
        .get(node_index(original)?)
        .copied()
        .flatten()
        .ok_or(TransformError::InvalidValidatedInput)
}

fn node_index(id: NodeId) -> Result<usize, TransformError> {
    usize::try_from(id.value()).map_err(|_| TransformError::InvalidValidatedInput)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::NewtypeConversionDirection,
        elaborate::{Elaborator, check_module, link_modules},
        module::{ModuleGraph, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::{BinderId, CheckedModule, ResolvedRegistry},
        source::{ByteRange, SourceFile},
        types::{ConstructorId, Kind, NominalTypeId, TYPE_WORK_LIMIT, Type, TypeVariableId},
        validate_linked_facts_for_test,
    };
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    static LINKED_TRANSFORM_TEMP_IDS: AtomicU64 = AtomicU64::new(0);

    #[test]
    fn provider_state_access_rebuild_preserves_metadata_and_remaps_only_operand() {
        use crate::{
            core::effect::ProviderStateAccessNode,
            interface::{InterfaceId, MethodId},
            module::ModuleId,
            resolved::ResourceDefinitionId,
            types::{EffectId, EffectInstance, EffectRow},
        };
        let source = SourceFile::new("state-access-transform", "()").unwrap();
        let origin = Origin::Source(source.span(ByteRange::new(0, 2).unwrap()).unwrap());
        let method = MethodId::new(InterfaceId::new(ModuleId::new(1), 2), 3);
        let definition = ResourceDefinitionId::new(ModuleId::new(2), 4);
        let arguments = [Type::Bool, Type::Tuple(Box::new([Type::Int, Type::Unit]))];
        let original = NodeId::new(super::super::dialect::ArenaId::new(0), 0);
        let expression = CoreTypedExpr {
            ty: Type::Bool,
            effects: EffectRow::singleton(EffectInstance::new(
                EffectId::new(ModuleId::new(3), 5),
                Box::new([Type::Int]),
            )),
            origin: origin.clone(),
            kind: EffectExprKind::Operation(EffectOperation::ProviderStateAccess(
                ProviderStateAccessNode::new(
                    method,
                    definition,
                    Box::new(arguments.clone()),
                    original,
                ),
            )),
        };
        let mut builder = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        builder.unit(Type::Unit, origin.clone()).unwrap();
        let replacement = builder.unit(Type::Unit, origin).unwrap();
        let root = EffectOperationFamily::rebuild_operation(
            &mut builder,
            &[Some(replacement)],
            &expression,
        )
        .unwrap();
        assert_eq!(builder.nodes.len(), 3);
        let rebuilt = &builder.nodes[root.index().unwrap()];
        assert_eq!(rebuilt.ty, expression.ty);
        assert_eq!(rebuilt.effects, expression.effects);
        assert_eq!(rebuilt.origin.as_ref(), Some(&expression.origin));
        assert_eq!(rebuilt.kind.child_count(), 1);
        let EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) = &rebuilt.kind
        else {
            unreachable!()
        };
        assert_eq!(access.method(), method);
        assert_eq!(access.definition(), definition);
        assert_eq!(
            access.arguments(),
            arguments.clone().map(crate::types::KindedArgument::TypeArg)
        );
        assert_eq!(access.operand(), replacement);
        assert_ne!(access.operand(), original);
    }

    #[test]
    fn provider_state_access_rebuild_is_exact_bounded_and_disposes_partial_clones() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                use crate::{
                    core::effect::ProviderStateAccessNode,
                    interface::{InterfaceId, MethodId},
                    module::ModuleId,
                    resolved::ResourceDefinitionId,
                    types::{EffectRow, TypeWorkBudget},
                };
                let source = SourceFile::new("state-access-transform-budget", "()").unwrap();
                let origin = Origin::Source(source.span(ByteRange::new(0, 2).unwrap()).unwrap());
                let prepare = |depth| {
                    let mut builder = CoreBuilder::<EffectOperationFamily>::with_effect_registry(
                        Arc::new(ResolvedRegistry::default()),
                    );
                    let operand = builder.unit(Type::Unit, origin.clone()).unwrap();
                    let expression = CoreTypedExpr {
                        ty: Type::Unit,
                        effects: EffectRow::empty(),
                        origin: origin.clone(),
                        kind: EffectExprKind::Operation(EffectOperation::ProviderStateAccess(
                            ProviderStateAccessNode::new(
                                MethodId::new(InterfaceId::new(ModuleId::new(1), 0), 0),
                                ResourceDefinitionId::new(ModuleId::new(2), 0),
                                Box::new([application_type(depth), application_type(depth)]),
                                operand,
                            ),
                        )),
                    };
                    (builder, [Some(operand)], expression)
                };
                let (mut measured, remapped, expression) = prepare(120);
                let prefix = measured.type_work.used();
                EffectOperationFamily::rebuild_operation(&mut measured, &remapped, &expression)
                    .unwrap();
                let cost = measured.type_work.used() - prefix;
                let (mut short, remapped, expression) = prepare(120);
                short.type_work = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.type_work.charge(prefix).unwrap();
                assert_eq!(
                    EffectOperationFamily::rebuild_operation(&mut short, &remapped, &expression),
                    Err(TransformError::Build(BuildError::TypeWorkExceeded))
                );
                assert_eq!(short.nodes.len(), 1);
                for _ in 0..2 {
                    let (mut retry, remapped, expression) = prepare(120);
                    retry.type_work = TypeWorkBudget::with_limit(prefix + cost);
                    retry.type_work.charge(prefix).unwrap();
                    EffectOperationFamily::rebuild_operation(&mut retry, &remapped, &expression)
                        .unwrap();
                    assert_eq!(retry.type_work.used(), prefix + cost);
                }
                let (mut late, remapped, expression) = prepare(32_000);
                // The first deep argument clone fits; the second clone exhausts
                // the ledger and must dismantle both partial and original types.
                late.type_work = TypeWorkBudget::with_limit(64_010);
                assert_eq!(
                    EffectOperationFamily::rebuild_operation(&mut late, &remapped, &expression),
                    Err(TransformError::Build(BuildError::TypeWorkExceeded))
                );
                assert_eq!(late.nodes.len(), 1);
                let (mut missing, _, expression) = prepare(120);
                assert_eq!(
                    EffectOperationFamily::rebuild_operation(&mut missing, &[None], &expression),
                    Err(TransformError::InvalidValidatedInput)
                );
                assert_eq!(missing.nodes.len(), 1);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    struct LinkedTransformDirectory(PathBuf);

    impl LinkedTransformDirectory {
        fn create() -> Self {
            loop {
                let id = LINKED_TRANSFORM_TEMP_IDS.fetch_add(1, Ordering::Relaxed);
                let directory = std::env::temp_dir().join(format!(
                    "ash-linked-core-transform-{}-{id}",
                    std::process::id(),
                ));
                match fs::create_dir(&directory) {
                    Ok(()) => return Self(directory),
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("linked transform fixture should be creatable: {error}"),
                }
            }
        }

        fn write(&self, name: &str, source: &str) -> PathBuf {
            let path = self.0.join(name);
            fs::write(&path, source).expect("linked transform fixture should be writable");
            path
        }
    }

    impl Drop for LinkedTransformDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct LinkedTransformFixture {
        _directory: LinkedTransformDirectory,
        graph: ModuleGraph,
        program: ValidatedProgram,
        module_sources: Vec<(crate::module::ModuleId, crate::source::SourceId)>,
    }

    impl LinkedTransformFixture {
        fn sources(&self) -> Vec<&SourceFile> {
            self.graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect()
        }
    }

    fn checked_linked_transform_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
        let mut checked = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|checked: &&CheckedModule| checked.module() == edge.target())
                        .expect("dependency order should check the target first");
                    DependencyExports::new(edge, dependency.exports())
                        .expect("linked transform dependency exports should authenticate")
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies)
                .expect("the linked transform module should resolve");
            checked.push(
                check_module(resolved).expect("the linked transform module should type-check"),
            );
        }
        checked
    }

    fn linked_row_bearing_fold_fixture() -> LinkedTransformFixture {
        let directory = LinkedTransformDirectory::create();
        let entry = directory.write(
            "entry.ash",
            concat!(
                "pub fold<F : Type -> Type> : F<Int> -> Int\n",
                "fold value = 1 + 2\n\n",
                "main : Unit -> Int\n",
                "main () = 0\n",
            ),
        );
        let graph = load_module_graph(&entry, &ModuleRoots::empty())
            .expect("the linked transform graph should load");
        let checked = checked_linked_transform_graph(&graph);
        let linked = link_modules(checked, graph.entry())
            .expect("the checked linked transform graph should link");
        let linked = validate_linked_facts_for_test(linked)
            .expect("the linked transform facts should authenticate");
        let mut elaborator = Elaborator::for_module_program(&linked)
            .expect("the linked transform binder namespace should fit");
        let typed = elaborator
            .synthesize_module_program(&linked)
            .expect("the linked transform program should lower to Core");
        let unchecked = elaborator
            .finish(typed.node)
            .expect("the linked transform Core root should finish");
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let module_sources = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        let program =
            super::super::validate::validate_modules(unchecked, &sources, &module_sources)
                .expect("the linked row-bearing transform Core should validate");
        LinkedTransformFixture {
            _directory: directory,
            graph,
            program,
            module_sources,
        }
    }

    fn linked_method_transform_fixture() -> LinkedTransformFixture {
        let directory = LinkedTransformDirectory::create();
        let entry = directory.write(
            "entry.ash",
            concat!(
                "type Wrap<A> = Wrap(A)\n\n",
                "interface Base<A> {\n",
                "base : A -> A\n",
                "}\n\n",
                "interface Convert<A> {\n",
                "convert<X> : (A, X) -> A\n",
                "}\n\n",
                "impl Base<Int> {\n",
                "base value = value\n",
                "}\n\n",
                "impl<A> Convert<Wrap<A>> where Base<A> {\n",
                "convert (Wrap(value), ignored) = Wrap(base(value))\n",
                "}\n\n",
                "main : Unit -> Wrap<Int>\n",
                "main () = convert((Wrap(42), true))\n",
            ),
        );
        let graph = load_module_graph(&entry, &ModuleRoots::empty())
            .expect("the linked method transform graph should load");
        let checked = checked_linked_transform_graph(&graph);
        let linked = link_modules(checked, graph.entry())
            .expect("the checked linked method transform graph should link");
        let linked = validate_linked_facts_for_test(linked)
            .expect("the linked method transform facts should authenticate");
        let mut elaborator = Elaborator::for_module_program(&linked)
            .expect("the linked method transform binder namespace should fit");
        let typed = elaborator
            .synthesize_module_program(&linked)
            .expect("the linked method transform program should lower to Core");
        let unchecked = elaborator
            .finish(typed.node)
            .expect("the linked method transform Core root should finish");
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let module_sources = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        let program =
            super::super::validate::validate_modules(unchecked, &sources, &module_sources)
                .expect("the linked method transform Core should validate");
        LinkedTransformFixture {
            _directory: directory,
            graph,
            program,
            module_sources,
        }
    }

    #[test]
    fn linked_method_transforms_have_exact_anchor_remap_and_arc_lifecycle_boundaries() {
        // This one-edge fixture consumes 673 predecessor node-reconstruction,
        // anchor Type-clone/Builder-replay, and finish units. Its four complete
        // applications add four vector-copy slots, four retained argument
        // slots, three non-edge application envelopes, and five aligned edge
        // authentication units. Admitting all methods adds eight catalog
        // lookup cells across the four replays. Reading the immutable sidecar
        // costs X=4, and remapping the exact prerequisite producer costs G=1
        // before the embedded NodeId lookup.
        // The edge-local concrete-source catalog adds S=1 lookup cell to each
        // of the four method-filtered expectation matches replayed here.
        const CONCRETE_SOURCE_LOOKUP_WORK: usize = 4;
        const COMPLETE_APPLICATION_WORK: usize = 4 + 4 + 3 + 5;
        const ALL_METHOD_CATALOG_LOOKUP_WORK: usize = 8;
        const CORE_WORK: usize = 673
            + COMPLETE_APPLICATION_WORK
            + ALL_METHOD_CATALOG_LOOKUP_WORK
            + CONCRETE_SOURCE_LOOKUP_WORK;
        const ANCHOR_REPLAY_WORK: usize = 4;
        const PRODUCER_REMAP_WORK: usize = 1;
        // Constructor admission reserves both the E=4 consumed bitmap and
        // the E=4 anchor carrier, adding the second E term to prior totals.
        const CONSTRUCTOR_SECOND_CARRIER_WORK: usize = 4;
        // Index construction adds two E-bounded tables plus one original
        // expectation visit and retained position per row. Authentication
        // replaces prior duplicate/whole-table scans with two key lookups,
        // one retained key, and exact shortlisted original-position visits.
        const CONSTRUCTOR_INDEX_WORK: usize = 4 * ANCHOR_REPLAY_WORK;
        const PRIOR_ANCHOR_DUPLICATE_SCAN_WORK: usize = 1 + 2 + 3;
        const PRIOR_EXPECTATION_SCAN_WORK: usize = 4 * ANCHOR_REPLAY_WORK;
        const INDEXED_ANCHOR_KEY_WORK: usize = 3 * ANCHOR_REPLAY_WORK;
        // Complete tags add four anchor-clone visits, four retained tag
        // admissions, and two additional selected-application comparisons.
        const COMPLETE_TAG_REPLAY_WORK: usize = 4 + 4 + 2;
        const IDENTITY_WORK: usize = CORE_WORK
            + COMPLETE_TAG_REPLAY_WORK
            + ANCHOR_REPLAY_WORK
            + PRODUCER_REMAP_WORK
            + CONSTRUCTOR_SECOND_CARRIER_WORK
            + 1; // exact selected producer matcher entry during anchor replay
        const FOLD_WORK: usize = IDENTITY_WORK;
        let fixture = linked_method_transform_fixture();
        assert_eq!(
            fixture.program.method_evidence_anchors().len(),
            ANCHOR_REPLAY_WORK,
        );
        assert_eq!(
            fixture
                .program
                .method_evidence_anchors()
                .iter()
                .filter(|anchor| matches!(
                    anchor.role,
                    super::super::dialect::MethodEvidenceAnchorRole::AdapterEdge { .. }
                ))
                .count(),
            PRODUCER_REMAP_WORK,
        );
        let expectations = fixture.program.method_evidence().expectations();
        assert_eq!(expectations.len(), ANCHOR_REPLAY_WORK);
        // The validated original anchor records its admitted expectation.
        // Replay keeps that immutable catalog and order. Every same-key
        // position through the admitted one is visited, including consumed
        // positions; unrelated keys and the untouched full predicate add no
        // new scan debit. Derive this count from coordinates, not measured
        // transform work or a larger allowance chosen after refusal.
        let mut indexed_candidate_work = 0;
        for anchor in fixture.program.method_evidence_anchors() {
            let expected = &expectations[anchor.expectation];
            assert_eq!(expected.occurrence, anchor.occurrence);
            assert_eq!(expected.method, anchor.method);
            indexed_candidate_work += expectations[..=anchor.expectation]
                .iter()
                .filter(|candidate| {
                    candidate.occurrence == anchor.occurrence && candidate.method == anchor.method
                })
                .count();
        }
        // Fallible tuple/match carriers now charge each copied edge. Pattern
        // rebuilding additionally charges its initial queue, every visited
        // pattern/finish carrier, and tuple/constructor pending storage.
        let mut payload_carrier_work = 0;
        for index in 0..fixture.program.node_count() {
            let kind = &fixture
                .program
                .node(NodeId::new(fixture.program.root().arena(), index as u32))
                .unwrap()
                .kind;
            match kind {
                PureExprKind::Computation(PureComputation::Tuple(tuple)) => {
                    payload_carrier_work += tuple.elements().len()
                }
                PureExprKind::Computation(PureComputation::Match(matching)) => {
                    payload_carrier_work += matching.arms().len();
                    for arm in matching.arms() {
                        let mut patterns = vec![arm.pattern()];
                        let (mut nodes, mut tuples, mut constructors, mut tuple_edges) =
                            (0, 0, 0, 0);
                        while let Some(pattern) = patterns.pop() {
                            nodes += 1;
                            match &pattern.kind {
                                CorePatternKind::Tuple(elements) => {
                                    tuples += 1;
                                    tuple_edges += elements.len();
                                    patterns.extend(elements.iter());
                                }
                                CorePatternKind::Constructor { payload, .. } => {
                                    constructors += 1;
                                    patterns.extend(payload.as_deref());
                                }
                                _ => {}
                            }
                        }
                        payload_carrier_work +=
                            1 + nodes + 2 * tuples + 3 * constructors + 2 * tuple_edges;
                    }
                }
                _ => {}
            }
        }
        let registry = Arc::clone(fixture.program.registry());
        let catalog = Arc::clone(fixture.program.method_evidence());
        let weak_registry = Arc::downgrade(&registry);
        let weak_catalog = Arc::downgrade(&catalog);
        let sources = fixture.sources();
        for (fold, exact_work) in [(false, IDENTITY_WORK), (true, FOLD_WORK)] {
            let exact_work = exact_work
                + payload_carrier_work
                + CONSTRUCTOR_INDEX_WORK
                + INDEXED_ANCHOR_KEY_WORK
                + indexed_candidate_work
                - PRIOR_ANCHOR_DUPLICATE_SCAN_WORK
                - PRIOR_EXPECTATION_SCAN_WORK;
            assert_eq!(
                rebuild_with_initial_type_work(
                    &fixture.program,
                    fold,
                    TYPE_WORK_LIMIT - (exact_work - 1),
                )
                .expect_err("one missing anchor-remap unit must reject the transform"),
                TransformError::Build(BuildError::TypeWorkExceeded),
            );
            let rebuilt = rebuild_with_initial_type_work(
                &fixture.program,
                fold,
                TYPE_WORK_LIMIT - exact_work,
            )
            .expect("the exact anchor-remap allowance should fit");
            assert!(Arc::ptr_eq(&rebuilt.registry, &registry));
            assert!(Arc::ptr_eq(&rebuilt.method_evidence, &catalog));
            super::super::validate::validate_modules(rebuilt, &sources, &fixture.module_sources)
                .expect("the exactly rebuilt anchors should freshly validate");
        }
        drop(sources);
        drop(registry);
        drop(catalog);
        drop(fixture);
        assert!(weak_registry.upgrade().is_none());
        assert!(weak_catalog.upgrade().is_none());
    }

    type GlobalRowShape = (BinderId, Vec<TypeVariableId>);

    fn global_row_shape(registry: &ResolvedRegistry) -> Vec<GlobalRowShape> {
        registry
            .global_parameter_rows()
            .iter()
            .map(|row| (row.owner(), row.parameters().to_vec()))
            .collect()
    }

    fn has_constant_folded_literal(program: &UnvalidatedProgram) -> bool {
        program.nodes.iter().any(|node| {
            matches!(node.kind, PureExprKind::Value(PureValue::Integer(_)))
                && node.origin.as_ref().is_some_and(|origin| {
                    origin.generated_reason() == Some(GeneratedReason::ConstantFolding)
                })
        })
    }

    fn deep_origin(source: &SourceFile, depth: usize) -> Origin {
        let mut origin = Origin::Source(
            source
                .span(ByteRange::new(0, 1).expect("the deep origin range should be ordered"))
                .expect("the deep origin span should fit"),
        );
        for _ in 0..depth {
            origin = Origin::Generated {
                cause: Box::new(origin),
                reason: GeneratedReason::TypeChecking,
            };
        }
        origin
    }

    fn origin_depth(root: &Origin) -> usize {
        let mut depth = 0;
        let mut current = root;
        loop {
            match current {
                Origin::Source(_) => return depth,
                Origin::Generated { cause, .. } => current = cause,
                Origin::Related { primary, .. } => current = primary,
            }
            depth += 1;
        }
    }

    fn row_bearing_fold_program_with_initial_type_work(
        registry: Arc<ResolvedRegistry>,
        owner: BinderId,
        parameter: TypeVariableId,
        origin: Origin,
        initial_type_work: usize,
    ) -> Result<UnvalidatedProgram, BuildError> {
        let parameter_kind = registry
            .type_variable(parameter)
            .ok_or(BuildError::InvalidPayload)?
            .kind
            .clone();
        let mut builder = CoreBuilder::with_registry(registry);
        builder.charge_type_work_for_test(initial_type_work)?;
        builder.reserve_resolved_binders([owner])?;
        let left = builder.integer(
            crate::integer::Integer::parse_decimal("1").expect("the left literal should parse"),
            Type::Int,
            origin.clone(),
        )?;
        let right = builder.integer(
            crate::integer::Integer::parse_decimal("2").expect("the right literal should parse"),
            Type::Int,
            origin.clone(),
        )?;
        let body = builder.primitive(Primitive::Add, left, right, Type::Int, origin.clone())?;
        let parameter_binder = builder.binder(Type::Unit, origin.clone())?;
        let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Int));
        let function = builder.function(
            parameter_binder,
            body,
            function_type.clone(),
            origin.clone(),
        )?;
        let scheme = Type::Forall(
            Box::new([(parameter, parameter_kind.clone())]),
            Box::new(function_type),
        );
        let abstraction = builder.type_abstraction(
            vec![(parameter, parameter_kind)],
            function,
            scheme.clone(),
            origin.clone(),
        )?;
        let global = builder.resolved_binder(owner, scheme, origin.clone())?;
        let group_body = builder.unit(Type::Unit, origin.clone())?;
        let root = builder.recursive_binding(
            vec![(global, abstraction)],
            group_body,
            Type::Unit,
            origin,
        )?;
        builder.finish(root)
    }

    fn application_type(depth: usize) -> Type {
        let mut result = Type::Unit;
        for _ in 0..depth {
            result = Type::Application(Box::new(result), Box::new(Type::Unit));
        }
        result
    }

    fn application_spine_depth(root: &Type) -> usize {
        let mut depth = 0;
        let mut current = root;
        loop {
            match current {
                Type::Application(function, argument) => {
                    assert!(matches!(argument.as_ref(), Type::Unit));
                    depth += 1;
                    current = function;
                }
                Type::Unit => return depth,
                _ => panic!("the deep transform payload must remain a Unit application spine"),
            }
        }
    }

    fn deep_arrow_kind(depth: usize) -> Kind {
        let mut result = Kind::Type;
        for _ in 0..depth {
            result = Kind::Arrow(Box::new(Kind::Type), Box::new(result));
        }
        result
    }

    fn arrow_kind_depth(root: &Kind) -> usize {
        let mut depth = 0;
        let mut current = root;
        loop {
            match current {
                Kind::Arrow(domain, codomain) => {
                    assert!(matches!(domain.as_ref(), Kind::Type));
                    depth += 1;
                    current = codomain;
                }
                Kind::Type | Kind::EffectRow => return depth,
            }
        }
    }

    #[test]
    fn unchecked_transforms_share_the_exact_nonempty_global_row_registry() {
        let fixture = linked_row_bearing_fold_fixture();
        let registry = Arc::clone(fixture.program.registry());
        let rows = global_row_shape(&registry);
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].1.len(), 1);
        assert!(registry.type_variable(rows[0].1[0]).is_some());

        let identity = identity_traversal(&fixture.program)
            .expect("the row-bearing identity traversal should rebuild");
        let folded = fold_literal_primitives(&fixture.program)
            .expect("the row-bearing literal fold should rebuild independently");
        assert!(Arc::ptr_eq(&identity.registry, &registry));
        assert!(Arc::ptr_eq(&folded.registry, &registry));
        assert_eq!(global_row_shape(&identity.registry), rows);
        assert_eq!(global_row_shape(&folded.registry), rows);
        assert!(!has_constant_folded_literal(&identity));
        assert!(has_constant_folded_literal(&folded));

        let sources = fixture.sources();
        let identity =
            super::super::validate::validate_modules(identity, &sources, &fixture.module_sources)
                .expect("the row-bearing identity traversal should independently revalidate");
        let folded =
            super::super::validate::validate_modules(folded, &sources, &fixture.module_sources)
                .expect("the row-bearing literal fold should independently revalidate");
        assert!(Arc::ptr_eq(identity.registry(), &registry));
        assert!(Arc::ptr_eq(folded.registry(), &registry));
        assert_eq!(global_row_shape(identity.registry()), rows);
        assert_eq!(global_row_shape(folded.registry()), rows);
    }

    #[test]
    fn row_bearing_construction_and_identity_have_exact_independent_type_work() {
        std::thread::Builder::new()
            .name("exact-row-bearing-construction-and-identity".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                // Input literals and primitive: three admitted Int cells = 3.
                // Function: Unit binder 1 + three-cell function result = 4.
                // Abstraction: one record + three Arrow Kind nodes + eight-cell scheme = 12.
                // Recursive owner/root: eight-cell scheme binder + Unit result = 9.
                // Recursive body Unit = 1. The shared registry and its row add 0.
                const CONSTRUCTION_WORK: usize = 3 + 4 + 12 + 9 + 1;
                // Identity literals and primitive: three clone/admission pairs = 6.
                // Function: Unit binder clone/admission 2 + result clone/admission 6 = 8.
                // Abstraction: scheme clone/admission 16 + parameter record/Arrow Kind 4 = 20.
                // Recursive owner/root: scheme binder clone/admission 16 + Unit result 2 = 18.
                // Recursive body Unit clone/admission = 2. The shared row again adds 0.
                // Exact old-to-new NodeId remap slots = 7.
                const IDENTITY_WORK: usize = 6 + 8 + 20 + 18 + 2 + 7;

                let fixture = linked_row_bearing_fold_fixture();
                let registry = Arc::clone(fixture.program.registry());
                let rows = global_row_shape(&registry);
                let [(owner, parameters)] = rows.as_slice() else {
                    panic!("the exact construction fixture should retain one global row");
                };
                let [parameter] = parameters.as_slice() else {
                    panic!("the exact construction row should retain one parameter");
                };
                let source = fixture
                    .graph
                    .modules()
                    .first()
                    .expect("the exact construction fixture should retain its entry module")
                    .source();
                let origin = deep_origin(source, super::super::CORE_PAYLOAD_DEPTH_LIMIT - 1);
                let registry_owners_before = Arc::strong_count(&registry);

                let short = row_bearing_fold_program_with_initial_type_work(
                    Arc::clone(&registry),
                    *owner,
                    *parameter,
                    origin.clone(),
                    TYPE_WORK_LIMIT - (CONSTRUCTION_WORK - 1),
                )
                .expect_err("one-short construction must reject without publishing a program");
                assert_eq!(short, BuildError::TypeWorkExceeded);
                assert_eq!(Arc::strong_count(&registry), registry_owners_before);

                let unchecked = row_bearing_fold_program_with_initial_type_work(
                    Arc::clone(&registry),
                    *owner,
                    *parameter,
                    origin,
                    TYPE_WORK_LIMIT - CONSTRUCTION_WORK,
                )
                .expect("the exact construction allowance should succeed on a fresh retry");
                assert!(Arc::ptr_eq(&unchecked.registry, &registry));
                assert_eq!(global_row_shape(&unchecked.registry), rows);
                let sources = fixture.sources();
                let program = super::super::validate::validate_modules(
                    unchecked,
                    &sources,
                    &fixture.module_sources,
                )
                .expect("the exact constructed row-bearing Core should freshly validate");
                assert!(Arc::ptr_eq(program.registry(), &registry));
                assert_eq!(global_row_shape(program.registry()), rows);
                assert_eq!(program.node_count(), 7);

                let registry_owners_before = Arc::strong_count(&registry);
                let short = rebuild_with_initial_type_work(
                    &program,
                    false,
                    TYPE_WORK_LIMIT - (IDENTITY_WORK - 1),
                )
                .expect_err("one-short identity rebuild must publish no transformed program");
                assert_eq!(short, TransformError::Build(BuildError::TypeWorkExceeded));
                assert_eq!(Arc::strong_count(&registry), registry_owners_before);

                let identity = rebuild_with_initial_type_work(
                    &program,
                    false,
                    TYPE_WORK_LIMIT - IDENTITY_WORK,
                )
                .expect("the exact identity allowance should succeed on a fresh retry");
                assert!(Arc::ptr_eq(&identity.registry, &registry));
                assert_eq!(global_row_shape(&identity.registry), rows);
                let identity = super::super::validate::validate_modules(
                    identity,
                    &sources,
                    &fixture.module_sources,
                )
                .expect("the exact identity result should freshly validate");
                assert!(Arc::ptr_eq(identity.registry(), &registry));
                assert_eq!(global_row_shape(identity.registry()), rows);
                assert_eq!(identity.node_count(), 7);

                drop(identity);
                drop(program);
                drop(sources);
                drop(fixture);
                drop(registry);
            })
            .expect("the small-stack construction/identity worker should start")
            .join()
            .expect("accepted and rejected construction/identity states should dismantle");
    }

    #[test]
    fn folded_higher_kinded_transform_has_exact_independent_type_work() {
        std::thread::Builder::new()
            .name("exact-row-bearing-fold-transform".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                // Folded Int result: one clone + one admission = 2.
                // Function: Unit binder clone/admission 2 + result clone/admission 6 = 8.
                // Outer Forall(F : Type -> Type). (Unit -> Int): 8 + 8 = 16.
                // Abstraction parameter: one record + three Arrow Kind nodes = 4.
                // Recursive owner: scheme binder clone/admission 16 + result Unit 2 = 18.
                // Recursive body Unit: one clone + one admission = 2.
                // The shared registry Arc and its nonempty resolved-global row add 0.
                // Exact old-to-new NodeId remap slots = 7.
                const EXACT_WORK: usize = 2 + 8 + 16 + 4 + 18 + 2 + 7;
                let fixture = linked_row_bearing_fold_fixture();
                let registry = Arc::clone(fixture.program.registry());
                let rows = global_row_shape(&registry);
                let [(owner, parameters)] = rows.as_slice() else {
                    panic!("the exact fold fixture should retain one global row");
                };
                let [parameter] = parameters.as_slice() else {
                    panic!("the exact fold row should retain one parameter");
                };
                assert!(owner.module().is_some());
                let canonical = registry
                    .type_variable(*parameter)
                    .expect("the retained row parameter should have one canonical record");
                assert!(matches!(canonical.kind, Kind::Arrow(_, _)));
                let source = fixture
                    .graph
                    .modules()
                    .first()
                    .expect("the exact fold fixture should retain its entry module")
                    .source();
                let origin = deep_origin(source, super::super::CORE_PAYLOAD_DEPTH_LIMIT - 1);
                assert_eq!(
                    origin_depth(&origin),
                    super::super::CORE_PAYLOAD_DEPTH_LIMIT - 1,
                );
                let unchecked = row_bearing_fold_program_with_initial_type_work(
                    Arc::clone(&registry),
                    *owner,
                    *parameter,
                    origin,
                    0,
                )
                .expect("the row-bearing fold fixture should construct");
                assert!(Arc::ptr_eq(&unchecked.registry, &registry));
                assert_eq!(global_row_shape(&unchecked.registry), rows);
                assert_eq!(unchecked.nodes.len(), 7);
                assert!(unchecked.nodes.iter().any(|node| matches!(
                    node.kind,
                    PureExprKind::Computation(PureComputation::Primitive(_)),
                )));
                let sources = fixture.sources();
                let program = super::super::validate::validate_modules(
                    unchecked,
                    &sources,
                    &fixture.module_sources,
                )
                .expect("the row-bearing higher-kinded fold fixture should validate");
                assert!(Arc::ptr_eq(program.registry(), &registry));

                let registry_owners_before = Arc::strong_count(&registry);
                let short = rebuild_with_initial_type_work(
                    &program,
                    true,
                    TYPE_WORK_LIMIT - (EXACT_WORK - 1),
                )
                .expect_err("one-short folding must reject without publishing output");
                assert_eq!(short, TransformError::Build(BuildError::TypeWorkExceeded));
                assert_eq!(Arc::strong_count(&registry), registry_owners_before);

                let transformed =
                    rebuild_with_initial_type_work(&program, true, TYPE_WORK_LIMIT - EXACT_WORK)
                        .expect("the exact independent folding allowance should succeed on retry");
                assert!(Arc::ptr_eq(&transformed.registry, &registry));
                assert_eq!(global_row_shape(&transformed.registry), rows);
                assert_eq!(transformed.nodes.len(), 5);
                assert!(has_constant_folded_literal(&transformed));
                let (folded_value, folded_origin) = transformed
                    .nodes
                    .iter()
                    .find_map(|node| {
                        let PureExprKind::Value(PureValue::Integer(integer)) = &node.kind else {
                            return None;
                        };
                        let origin = node.origin.as_ref()?;
                        (origin.generated_reason() == Some(GeneratedReason::ConstantFolding))
                            .then_some((integer.value(), origin))
                    })
                    .expect("the exact transform should publish its folded literal");
                assert_eq!(folded_value.to_string(), "3");
                assert_eq!(
                    origin_depth(folded_origin),
                    super::super::CORE_PAYLOAD_DEPTH_LIMIT,
                );
                let transformed = super::super::validate::validate_modules(
                    transformed,
                    &sources,
                    &fixture.module_sources,
                )
                .expect("the exact folded result should independently validate");
                assert!(Arc::ptr_eq(transformed.registry(), &registry));
                assert_eq!(global_row_shape(transformed.registry()), rows);
                assert_eq!(
                    crate::eval::evaluate(&transformed)
                        .expect("the exact folded result should evaluate")
                        .value
                        .to_string(),
                    "()",
                );

                drop(transformed);
                drop(program);
                drop(sources);
                drop(fixture);
                drop(registry);
            })
            .expect("the small-stack exact fold worker should start")
            .join()
            .expect("accepted and rejected fold states should dismantle on the small stack");
    }

    #[test]
    fn higher_kinded_transform_copies_have_an_exact_type_budget() {
        // Body: one retained clone + one admission visit = 2.
        // Abstraction scheme: six clone units and six admission units.
        // Abstraction parameters: one binder record + three Kind nodes = 4.
        // Exact old-to-new NodeId remap slots = 2.
        const EXACT_WORK: usize = 20;
        let source =
            SourceFile::new("transform-kinds.ash", "higher").expect("transform fixture source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 6).expect("transform fixture range"))
                .expect("transform fixture span"),
        );
        let parameter = TypeVariableId::new(0);
        let kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let mut builder = CoreBuilder::new();
        let body = builder
            .unit(Type::Unit, origin.clone())
            .expect("fixture body");
        let root = builder
            .type_abstraction(
                vec![(parameter, kind.clone())],
                body,
                Type::Forall(
                    vec![(parameter, kind.clone())].into_boxed_slice(),
                    Box::new(Type::Unit),
                ),
                origin,
            )
            .expect("fixture abstraction");
        let program = super::super::validate::validate(
            builder.finish(root).expect("fixture root"),
            &[&source],
        )
        .expect("fixture validates");

        let short =
            rebuild_with_initial_type_work(&program, false, TYPE_WORK_LIMIT - (EXACT_WORK - 1))
                .expect_err("one-short transform must reject before publishing output");
        assert_eq!(short, TransformError::Build(BuildError::TypeWorkExceeded));

        let transformed =
            rebuild_with_initial_type_work(&program, false, TYPE_WORK_LIMIT - EXACT_WORK)
                .expect("the exact transform allowance fits");
        super::super::validate::validate(transformed, &[&source])
            .expect("the exact transform preserves canonical binder kinds");
    }

    #[test]
    fn discard_rebuild_preserves_owner_usage_and_empty_row_without_children() {
        use crate::{
            core::{DiscardNode, HandlerId, ResumeUse},
            resolved::ResumeId,
            types::EffectRow,
        };
        let source = SourceFile::new("discard-transform.ash", "discard").unwrap();
        let origin = Origin::Source(source.span(ByteRange::new(0, 7).unwrap()).unwrap());
        let expression = CoreTypedExpr {
            ty: Type::Unit,
            effects: EffectRow::empty(),
            origin,
            kind: EffectExprKind::Operation(EffectOperation::Discard(DiscardNode::new(
                HandlerId::new(7),
                ResumeId::new(9),
                ResumeUse::Consumed,
            ))),
        };
        let mut builder = CoreBuilder::<EffectOperationFamily>::with_effect_registry(Arc::new(
            ResolvedRegistry::default(),
        ));
        let root =
            EffectOperationFamily::rebuild_operation(&mut builder, &[], &expression).unwrap();
        let rebuilt = &builder.nodes[root.index().unwrap()];
        assert_eq!(rebuilt.kind, expression.kind);
        assert_eq!(rebuilt.ty, Type::Unit);
        assert!(rebuilt.effects.is_empty());
        assert_eq!(rebuilt.origin.as_ref(), Some(&expression.origin));
        assert_eq!(
            crate::core::validate_effect(builder.finish(root).unwrap(), &[&source])
                .unwrap_err()
                .reason(),
            crate::core::ValidationReason::Resume
        );
    }

    #[test]
    fn effect_handler_rebuild_is_exact_retryable_and_deep_drop_safe() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                use crate::{
                    core::effect::{HandlerId, HandlerNode},
                    resolved::ResumeId,
                    types::{EffectId, EffectInstance, EffectRow, OperationId},
                };
                let source = SourceFile::new("effect-transform.ash", "handler").unwrap();
                let origin = Origin::Source(source.span(ByteRange::new(0, 7).unwrap()).unwrap());
                let effect = EffectId::new(crate::module::ModuleId::new(0), 0);
                let prepare = |deep| {
                    let mut builder = CoreBuilder::<EffectOperationFamily>::with_effect_registry(
                        Arc::new(ResolvedRegistry::default()),
                    );
                    let body = builder.unit(Type::Unit, origin.clone()).unwrap();
                    let clauses = (0..4)
                        .map(|ordinal| {
                            EffectClause::new(
                                OperationId::new(effect, ordinal),
                                ResumeId::new(ordinal),
                                CoreMatchArm::new(
                                    CorePattern::new(
                                        Type::Unit,
                                        origin.clone(),
                                        CorePatternKind::Wildcard,
                                    ),
                                    body,
                                    origin.clone(),
                                ),
                            )
                        })
                        .collect();
                    let expression = CoreTypedExpr {
                        ty: Type::Unit,
                        effects: EffectRow::empty(),
                        origin: origin.clone(),
                        kind: EffectExprKind::Operation(EffectOperation::Handler(
                            HandlerNode::new(
                                HandlerId::new(0),
                                body,
                                EffectInstance::new(
                                    effect,
                                    vec![deep, Type::Unit].into_boxed_slice(),
                                ),
                                clauses,
                            ),
                        )),
                    };
                    (builder, vec![Some(body)], expression)
                };
                let admitted = || application_type(super::super::CORE_PAYLOAD_DEPTH_LIMIT - 2);
                let (mut measured, remapped, expression) = prepare(admitted());
                let before = measured.type_work.used();
                EffectOperationFamily::rebuild_operation(&mut measured, &remapped, &expression)
                    .unwrap();
                let work = measured.type_work.used() - before;

                let (mut short, remapped, expression) = prepare(admitted());
                let retained = short.nodes.len();
                short
                    .charge_type_work_for_test(
                        TYPE_WORK_LIMIT - short.type_work.used() - (work - 1),
                    )
                    .unwrap();
                assert_eq!(
                    EffectOperationFamily::rebuild_operation(&mut short, &remapped, &expression),
                    Err(TransformError::Build(BuildError::TypeWorkExceeded)),
                );
                assert_eq!(short.nodes.len(), retained);
                for _ in 0..2 {
                    let (mut retry, remapped, expression) = prepare(admitted());
                    retry
                        .charge_type_work_for_test(TYPE_WORK_LIMIT - retry.type_work.used() - work)
                        .unwrap();
                    EffectOperationFamily::rebuild_operation(&mut retry, &remapped, &expression)
                        .expect("fresh exact retry");
                }
                let rejected_type = (0..32_768).fold(Type::Unit, |ty, _| {
                    Type::Function(Box::new(Type::Unit), Box::new(ty))
                });
                let (mut rejected, remapped, expression) = prepare(rejected_type);
                assert_eq!(
                    EffectOperationFamily::rebuild_operation(
                        &mut rejected,
                        &remapped,
                        &expression,
                    ),
                    Err(TransformError::Build(BuildError::TypeDepthExceeded)),
                );
                expression.discard_iteratively();
            })
            .unwrap()
            .join()
            .expect("deep effect metadata teardown stays on the small stack");
    }

    #[test]
    fn row_bearing_deep_abstraction_failure_dismantles_integrated_transform_state() {
        std::thread::Builder::new()
            .name("integrated-row-bearing-transform-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const TYPE_DEPTH: usize = 32_768;
                const KIND_DEPTH: usize = 16_384;
                const KIND_NODES: usize = 2 * KIND_DEPTH + 1;
                const TYPE_CELLS: usize = 2 * TYPE_DEPTH + 1;
                // Forall root + binder record + binder Kind + body Type.
                const SCHEME_WORK: usize = 1 + 1 + KIND_NODES + TYPE_CELLS;
                // The abstraction payload independently clones its binder
                // record and Kind after the body remap succeeds.
                const PARAMETER_WORK: usize = 1 + KIND_NODES;
                const REBUILD_WORK: usize = SCHEME_WORK + PARAMETER_WORK + SCHEME_WORK;
                const BODY_WORK: usize = 1;

                let fixture = linked_row_bearing_fold_fixture();
                let registry = Arc::clone(fixture.program.registry());
                let rows = global_row_shape(&registry);
                let [(owner, parameters)] = rows.as_slice() else {
                    panic!("the integrated transform fixture must retain one global row");
                };
                let [resolved_parameter] = parameters.as_slice() else {
                    panic!("the integrated transform row must retain one parameter");
                };
                assert!(owner.module().is_some());
                assert!(matches!(
                    registry
                        .type_variable(*resolved_parameter)
                        .expect("the row parameter must retain its canonical record")
                        .kind,
                    Kind::Arrow(_, _),
                ));

                let source = fixture
                    .graph
                    .modules()
                    .first()
                    .expect("the integrated fixture must retain its source")
                    .source();
                let span = source
                    .span(ByteRange::new(0, 1).expect("the integrated range is ordered"))
                    .expect("the integrated span belongs to its source");
                let generated_parameter = TypeVariableId::generated(90_001);
                let parameter_kind = deep_arrow_kind(KIND_DEPTH);
                let expression = super::super::TypedExpr {
                    effects: (),
                    ty: Type::Forall(
                        Box::new([(generated_parameter, parameter_kind.clone())]),
                        Box::new(application_type(TYPE_DEPTH)),
                    ),
                    origin: deep_origin(source, super::super::CORE_PAYLOAD_DEPTH_LIMIT),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![(generated_parameter, parameter_kind)],
                            fixture.program.root(),
                        ),
                    )),
                };

                let Type::Forall(scheme_parameters, scheme_body) = &expression.ty else {
                    panic!("the integrated input must retain its deep scheme");
                };
                assert_eq!(scheme_parameters[0].0, generated_parameter);
                assert_eq!(arrow_kind_depth(&scheme_parameters[0].1), KIND_DEPTH);
                assert_eq!(application_spine_depth(scheme_body), TYPE_DEPTH);
                let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                    &expression.kind
                else {
                    panic!("the integrated input must remain a type abstraction");
                };
                assert_eq!(abstraction.body(), fixture.program.root());
                assert_eq!(abstraction.parameters()[0].0, generated_parameter);
                assert_eq!(arrow_kind_depth(&abstraction.parameters()[0].1), KIND_DEPTH);
                assert_eq!(
                    origin_depth(&expression.origin),
                    super::super::CORE_PAYLOAD_DEPTH_LIMIT,
                );
                const { assert!(BODY_WORK + REBUILD_WORK < TYPE_WORK_LIMIT) };

                let owners_before = Arc::strong_count(&registry);
                let mut output = CoreBuilder::with_registry(Arc::clone(&registry));
                let body = output
                    .unit(Type::Unit, Origin::Source(span))
                    .expect("the mapped output body must fit");
                let mut remapped = vec![None; fixture.program.node_count()];
                remapped[node_index(fixture.program.root()).expect("the root index must fit")] =
                    Some(body);
                output
                    .charge_type_work_for_test(TYPE_WORK_LIMIT - BODY_WORK - (REBUILD_WORK - 1))
                    .expect("the late one-short allowance must fit");
                let error =
                    rebuild_node(&mut output, &fixture.program, &remapped, &expression, false)
                        .expect_err(
                            "one missing final admission cell must reject the rebuilt abstraction",
                        );
                assert_eq!(error, TransformError::Build(BuildError::TypeWorkExceeded));
                drop(output);
                assert_eq!(Arc::strong_count(&registry), owners_before);
                assert_eq!(global_row_shape(&registry), rows);

                let mut exact_output = CoreBuilder::with_registry(Arc::clone(&registry));
                let exact_body = exact_output
                    .unit(Type::Unit, Origin::Source(span))
                    .expect("the exact mapped output body must fit");
                let mut exact_remapped = vec![None; fixture.program.node_count()];
                exact_remapped
                    [node_index(fixture.program.root()).expect("the exact root index must fit")] =
                    Some(exact_body);
                exact_output
                    .charge_type_work_for_test(TYPE_WORK_LIMIT - BODY_WORK - REBUILD_WORK)
                    .expect("the exact integrated allowance must fit");
                let rebuilt = rebuild_node(
                    &mut exact_output,
                    &fixture.program,
                    &exact_remapped,
                    &expression,
                    false,
                )
                .expect("the exact integrated allowance must rebuild the abstraction");
                let exact = exact_output
                    .finish(rebuilt)
                    .expect("the exact integrated output must finish unchecked");
                assert!(Arc::ptr_eq(&exact.registry, &registry));
                assert_eq!(global_row_shape(&exact.registry), rows);
                exact.discard_iteratively();
                assert_eq!(Arc::strong_count(&registry), owners_before);

                expression.discard_iteratively();
                drop(fixture);
                drop(registry);
            })
            .expect("the integrated transform worker must start")
            .join()
            .expect("integrated rejected and exact transform state must dismantle on 256 KiB");
    }

    #[test]
    fn late_pattern_rebuild_failure_discards_completed_patterns_iteratively() {
        std::thread::Builder::new()
            .name("late-pattern-transform-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_000;
                let source =
                    SourceFile::new("transform-owner.ash", "()").expect("the fixture should fit");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("fixture span"),
                );
                let binder_id = BinderId::new(0);
                let mut builder = CoreBuilder::new();
                builder
                    .reserve_resolved_binders([binder_id])
                    .expect("the test binder is reserved");
                let binder = builder
                    .resolved_binder(binder_id, Type::Unit, origin.clone())
                    .expect("the first materialization succeeds");
                let pattern = CorePattern::new(
                    Type::Tuple(vec![application_type(DEPTH), Type::Unit].into_boxed_slice()),
                    origin.clone(),
                    CorePatternKind::Tuple(
                        vec![
                            CorePattern::new(
                                application_type(DEPTH),
                                origin.clone(),
                                CorePatternKind::Wildcard,
                            ),
                            CorePattern::new(Type::Unit, origin, CorePatternKind::Binder(binder)),
                        ]
                        .into_boxed_slice(),
                    ),
                );

                let error = rebuild_pattern(&mut builder, &pattern)
                    .expect_err("the duplicate binder materialization is rejected");
                assert_eq!(
                    error,
                    TransformError::Build(BuildError::DuplicateResolvedBinder)
                );
                pattern.discard_iteratively();
                drop(builder);
            })
            .expect("small-stack transform thread should start")
            .join()
            .expect("late pattern-transform teardown must fit the small stack");
    }

    #[test]
    fn deep_type_application_arguments_survive_a_late_missing_remap() {
        std::thread::Builder::new()
            .name("transform-type-argument-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_768;
                let source = SourceFile::new("transform-argument.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("test span"),
                );
                let mut input = CoreBuilder::new();
                let input_root = input.unit(Type::Unit, origin.clone()).expect("input root");
                let program = super::super::validate::validate(
                    input.finish(input_root).expect("input program"),
                    &[&source],
                )
                .expect("input validates");
                let expression = super::super::TypedExpr {
                    effects: (),
                    ty: Type::Unit,
                    origin: origin.clone(),
                    kind: PureExprKind::Computation(PureComputation::TypeApplication(
                        super::super::type_ops::TypeApplicationNode::new(
                            program.root(),
                            vec![application_type(DEPTH)],
                        ),
                    )),
                };
                let mut output = CoreBuilder::new();
                let remapped = vec![None; program.node_count()];

                let error = rebuild_node(&mut output, &program, &remapped, &expression, false)
                    .expect_err("the deliberately absent function remap is an invariant failure");
                assert_eq!(error, TransformError::InvalidValidatedInput);

                expression.discard_iteratively();
            })
            .expect("small-stack argument-owner thread should start")
            .join()
            .expect("late missing-remap teardown must fit the small stack");
    }

    #[test]
    fn accumulated_type_arguments_survive_one_short_result_clone() {
        std::thread::Builder::new()
            .name("transform-result-clone-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_768;
                const DEEP_CELLS: usize = 2 * DEPTH + 1;
                const ARGUMENT_CELLS: usize = DEEP_CELLS + 1;
                let source = SourceFile::new("transform-result.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("test span"),
                );
                let mut input = CoreBuilder::new();
                let input_root = input.unit(Type::Unit, origin.clone()).expect("input root");
                let program = super::super::validate::validate(
                    input.finish(input_root).expect("input program"),
                    &[&source],
                )
                .expect("input validates");
                let expression = super::super::TypedExpr {
                    effects: (),
                    ty: Type::Unit,
                    origin,
                    kind: PureExprKind::Computation(PureComputation::TypeApplication(
                        super::super::type_ops::TypeApplicationNode::new(
                            program.root(),
                            vec![application_type(DEPTH), Type::Unit],
                        ),
                    )),
                };
                let mut output = CoreBuilder::new();
                output
                    .charge_type_work_for_test(TYPE_WORK_LIMIT - ARGUMENT_CELLS)
                    .expect("the exact argument-clone allowance remains");

                let error = rebuild_node(&mut output, &program, &[], &expression, false)
                    .expect_err("the one-short result clone must fail after both arguments");
                assert_eq!(error, TransformError::Build(BuildError::TypeWorkExceeded));

                expression.discard_iteratively();
            })
            .expect("small-stack result-owner thread should start")
            .join()
            .expect("late result-clone teardown must fit the small stack");
    }

    #[test]
    fn extracted_tuple_and_constructor_children_survive_parent_clone_failure() {
        std::thread::Builder::new()
            .name("transform-pattern-child-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_768;
                const DEEP_CELLS: usize = 2 * DEPTH + 1;
                let source = SourceFile::new("transform-pattern.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("test span"),
                );

                let tuple = CorePattern::new(
                    Type::Unit,
                    origin.clone(),
                    CorePatternKind::Tuple(
                        vec![
                            CorePattern::new(
                                application_type(DEPTH),
                                origin.clone(),
                                CorePatternKind::Wildcard,
                            ),
                            CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard),
                        ]
                        .into_boxed_slice(),
                    ),
                );
                let mut tuple_builder = CoreBuilder::new();
                tuple_builder
                    .charge_type_work_for_test(TYPE_WORK_LIMIT - (DEEP_CELLS + 1))
                    .expect("the exact tuple-child allowance remains");
                assert_eq!(
                    rebuild_pattern(&mut tuple_builder, &tuple),
                    Err(TransformError::Build(BuildError::TypeWorkExceeded))
                );
                tuple.discard_iteratively();

                let constructor = CorePattern::new(
                    Type::Unit,
                    origin.clone(),
                    CorePatternKind::Constructor {
                        constructor: ConstructorId::new(NominalTypeId::new(source.id(), 0), 0),
                        payload: Some(Box::new(CorePattern::new(
                            application_type(DEPTH),
                            origin,
                            CorePatternKind::Wildcard,
                        ))),
                    },
                );
                let mut constructor_builder = CoreBuilder::new();
                constructor_builder
                    .charge_type_work_for_test(TYPE_WORK_LIMIT - DEEP_CELLS)
                    .expect("the exact constructor-child allowance remains");
                assert_eq!(
                    rebuild_pattern(&mut constructor_builder, &constructor),
                    Err(TransformError::Build(BuildError::TypeWorkExceeded))
                );
                constructor.discard_iteratively();
            })
            .expect("small-stack pattern-child thread should start")
            .join()
            .expect("extracted pattern-child teardown must fit the small stack");
    }

    #[test]
    fn rebuilt_deep_match_pattern_survives_missing_body_remap() {
        std::thread::Builder::new()
            .name("transform-match-pattern-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_768;
                let source = SourceFile::new("transform-match.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("test span"),
                );
                let mut input = CoreBuilder::new();
                let input_root = input.unit(Type::Unit, origin.clone()).expect("input root");
                let program = super::super::validate::validate(
                    input.finish(input_root).expect("input program"),
                    &[&source],
                )
                .expect("input validates");
                let pattern = CorePattern::new(
                    application_type(DEPTH),
                    origin.clone(),
                    CorePatternKind::Wildcard,
                );
                let expression = super::super::TypedExpr {
                    effects: (),
                    ty: Type::Unit,
                    origin: origin.clone(),
                    kind: PureExprKind::Computation(PureComputation::Match(
                        super::super::MatchNode::new(
                            program.root(),
                            vec![CoreMatchArm::new(pattern, program.root(), origin)],
                        ),
                    )),
                };
                let mut output = CoreBuilder::new();
                let remapped = vec![None; program.node_count()];

                let error = rebuild_node(&mut output, &program, &remapped, &expression, false)
                    .expect_err("the deliberately absent arm-body remap is an invariant failure");
                assert_eq!(error, TransformError::InvalidValidatedInput);

                expression.discard_iteratively();
            })
            .expect("small-stack match-pattern thread should start")
            .join()
            .expect("missing-remap pattern teardown must fit the small stack");
    }

    #[test]
    fn transforms_rebuild_validated_newtype_conversions() {
        const REMAP_WORK: usize = 2; // one slot per input node
        const CHILD_COPY_WORK: usize = 2; // clone + admit `Unit`
        const CONVERSION_COPY_WORK: usize = 2; // clone + admit `Unit`
        const EXACT_WORK: usize = REMAP_WORK + CHILD_COPY_WORK + CONVERSION_COPY_WORK;
        let source = SourceFile::new("transform-conversion.ash", "()").expect("test source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 2).expect("ordered range"))
                .expect("source span"),
        );
        let owner = NominalTypeId::new(source.id(), 0);
        let mut builder = CoreBuilder::new();
        let child = builder
            .unit(Type::Unit, origin.clone())
            .expect("the conversion child should fit");
        let root = builder
            .newtype_conversion(
                owner,
                NewtypeConversionDirection::Wrap,
                child,
                Type::Unit,
                origin,
            )
            .expect("the conversion carrier should fit");
        let program = super::super::dialect::forge_validated_for_test(
            builder.finish(root).expect("the conversion should finish"),
        );

        let identity = identity_traversal(&program).expect("identity must rebuild the conversion");
        let folded =
            fold_literal_primitives(&program).expect("folding must rebuild the conversion");
        for rebuilt in [&identity, &folded] {
            assert!(matches!(
                rebuilt.expression_kinds_for_test().nth(1),
                Some(PureExprKind::Computation(PureComputation::NewtypeConversion(
                    conversion,
                ))) if conversion.owner() == owner
                    && conversion.direction() == NewtypeConversionDirection::Wrap
            ));
        }
        for fold_literal_primitives in [false, true] {
            assert_eq!(
                rebuild_with_initial_type_work(
                    &program,
                    fold_literal_primitives,
                    TYPE_WORK_LIMIT - (EXACT_WORK - 1),
                )
                .expect_err("one-short newtype transform must reject"),
                TransformError::Build(BuildError::TypeWorkExceeded),
            );
            for _ in 0..2 {
                let rebuilt = rebuild_with_initial_type_work(
                    &program,
                    fold_literal_primitives,
                    TYPE_WORK_LIMIT - EXACT_WORK,
                )
                .expect("exact newtype transform should retry");
                assert_eq!(rebuilt.expression_kinds_for_test().count(), 2);
                drop(rebuilt);
            }
        }
    }

    #[test]
    fn transform_conversion_rebuild_and_teardown_fit_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("transform-newtype-conversion-rebuild".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    SourceFile::new("transform-conversion-chain.ash", "()").expect("test source");
                let origin = Origin::Source(
                    source
                        .span(ByteRange::new(0, 2).expect("ordered range"))
                        .expect("source span"),
                );
                let owner = NominalTypeId::new(source.id(), 0);
                let mut builder = CoreBuilder::new();
                let mut root = builder
                    .unit(Type::Unit, origin.clone())
                    .expect("the conversion leaf should fit");
                for index in 0..DEPTH {
                    root = builder
                        .newtype_conversion(
                            owner,
                            if index % 2 == 0 {
                                NewtypeConversionDirection::Wrap
                            } else {
                                NewtypeConversionDirection::Unwrap
                            },
                            root,
                            Type::Unit,
                            origin.clone(),
                        )
                        .expect("the conversion chain should fit");
                }
                let program = super::super::dialect::forge_validated_for_test(
                    builder.finish(root).expect("the conversion should finish"),
                );
                let identity = identity_traversal(&program)
                    .expect("identity must rebuild the conversion chain");
                let folded = fold_literal_primitives(&program)
                    .expect("folding must rebuild the conversion chain");
                drop(identity);
                drop(folded);
            })
            .expect("the transform rebuild thread should start")
            .join()
            .expect("transform conversion rebuilding must fit a small stack");
    }
}

#[cfg(test)]
mod provider_draft_tests {
    use super::*;
    use crate::{
        source::{ByteRange, Origin, SourceFile},
        types::{Type, TypeWorkBudget},
    };
    fn draft() -> super::super::UnvalidatedEffectProgram {
        let source = SourceFile::new("provider-draft.ash", "x").unwrap();
        let origin = Origin::Source(source.span(ByteRange::new(0, 1).unwrap()).unwrap());
        let mut builder = CoreBuilder::<EffectOperationFamily>::with_registry_for_family(Arc::new(
            crate::resolved::ResolvedRegistry::default(),
        ));
        let parameter = builder.binder(Type::Unit, origin.clone()).unwrap();
        let body = builder
            .variable(parameter.id(), Type::Unit, origin.clone())
            .unwrap();
        let function = builder
            .function(
                parameter,
                body,
                Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
                origin.clone(),
            )
            .unwrap();
        let argument = builder.unit(Type::Unit, origin.clone()).unwrap();
        let root = builder
            .application(function, argument, Type::Unit, origin)
            .unwrap();
        builder.finish(root).unwrap()
    }
    fn wide_pattern_draft(width: usize) -> super::super::UnvalidatedEffectProgram {
        let source = SourceFile::new("provider-wide-draft.ash", "x").unwrap();
        let origin = Origin::Source(source.span(ByteRange::new(0, 1).unwrap()).unwrap());
        let mut builder = CoreBuilder::<EffectOperationFamily>::with_registry_for_family(Arc::new(
            crate::resolved::ResolvedRegistry::default(),
        ));
        let unit = builder.unit(Type::Unit, origin.clone()).unwrap();
        let tuple_type = Type::Tuple(vec![Type::Unit; width].into_boxed_slice());
        let tuple = builder
            .tuple(vec![unit; width], tuple_type.clone(), origin.clone())
            .unwrap();
        let pattern = CorePattern::new(
            tuple_type,
            origin.clone(),
            CorePatternKind::Tuple(
                (0..width)
                    .map(|_| {
                        CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard)
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            ),
        );
        let root = builder
            .match_expression(
                tuple,
                vec![CoreMatchArm::new(pattern, unit, origin.clone())],
                Type::Unit,
                origin,
            )
            .unwrap();
        builder.finish(root).unwrap()
    }

    #[test]
    fn provider_draft_preparation_and_rebuild_charge_wide_payloads_cumulatively() {
        let prepare_cost = |width| {
            let program = wide_pattern_draft(width);
            let order = provider_draft_order(
                &program,
                &std::collections::HashSet::new(),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            let mut work = TypeWorkBudget::unbounded();
            drop(prepare_provider_draft_builder(&program, &order, &mut work).unwrap());
            work.used()
        };
        assert_eq!(prepare_cost(65) - prepare_cost(1), 128);
        let mut costs = Vec::new();
        for width in [1, 65] {
            let program = wide_pattern_draft(width);
            let order = provider_draft_order(
                &program,
                &std::collections::HashSet::new(),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
            let run = |work: &mut TypeWorkBudget| -> Result<(), TransformError> {
                let mut builder = prepare_provider_draft_builder(&program, &order, work)?;
                let mut remapped = vec![None; program.nodes.len()];
                for original in &order {
                    begin_provider_draft_work(&mut builder, work.remaining());
                    let result =
                        rebuild_provider_draft_node(&mut builder, &program, &remapped, *original);
                    discharge_provider_draft_work(&builder, work)?;
                    remapped[original.value() as usize] = Some(result?);
                }
                builder.finish(remapped[program.root.value() as usize].unwrap())?;
                Ok(())
            };
            let mut measured = TypeWorkBudget::unbounded();
            run(&mut measured).unwrap();
            let cost = measured.used();
            costs.push(cost);
            assert!(cost > prepare_cost(width));
            for prefix in [0, 17] {
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    run(&mut short),
                    Err(TransformError::Build(BuildError::TypeWorkExceeded))
                ));
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                    exact.charge(prefix).unwrap();
                    run(&mut exact).unwrap();
                    assert_eq!(exact.used(), prefix + cost);
                }
            }
        }
        assert!(costs[1] - costs[0] > 128);
    }

    #[test]
    fn provider_draft_rebuild_rejects_foreign_bounds_cycles_and_unreachable_source() {
        for mutation in 0..4 {
            let mut program = draft();
            match mutation {
                0 => {
                    let foreign = draft();
                    program.root = foreign.root;
                }
                1 => program.root = NodeId::new(program.arena, u32::MAX),
                2 => {
                    program.nodes[program.root.value() as usize].kind =
                        super::super::EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::Apply(super::super::function::ApplicationNode::new(
                                program.root,
                                program.root,
                            )),
                        ))
                }
                3 => program.root = NodeId::new(program.arena, 0),
                _ => unreachable!(),
            }
            assert!(
                provider_draft_order(
                    &program,
                    &std::collections::HashSet::new(),
                    &mut TypeWorkBudget::unbounded()
                )
                .is_err()
            );
        }
        let program = draft();
        let mut measured = TypeWorkBudget::unbounded();
        let order =
            provider_draft_order(&program, &std::collections::HashSet::new(), &mut measured)
                .unwrap();
        assert_eq!(order.len(), program.nodes.len());
        assert!(
            provider_draft_order(
                &program,
                &std::collections::HashSet::new(),
                &mut TypeWorkBudget::with_limit(measured.used() - 1)
            )
            .is_err()
        );
        assert_eq!(
            provider_draft_order(
                &program,
                &std::collections::HashSet::new(),
                &mut TypeWorkBudget::with_limit(measured.used())
            )
            .unwrap(),
            order
        );
    }
}

struct IterativeArgumentBuffer(Vec<crate::types::KindedArgument>);
impl IterativeArgumentBuffer {
    fn try_reserve(&mut self, count: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(count)
    }
    fn push(&mut self, argument: crate::types::KindedArgument) {
        self.0.push(argument);
    }
    fn into_vec(mut self) -> Vec<crate::types::KindedArgument> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for IterativeArgumentBuffer {
    fn drop(&mut self) {
        for argument in self.0.drain(..) {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}
