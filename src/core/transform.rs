//! Bounded transformations over independently validated pure Core.

use std::{error::Error, fmt};

use super::{
    BuildError, CoreBuilder, NodeId, Primitive, PureComputation, PureExprKind, PureValue,
    UnvalidatedProgram, ValidatedProgram,
};
use crate::source::{GeneratedReason, Origin};

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

fn rebuild(
    program: &ValidatedProgram,
    fold_literal_primitives: bool,
) -> Result<UnvalidatedProgram, TransformError> {
    let order = postorder(program, fold_literal_primitives)?;
    let mut builder = CoreBuilder::new();
    let binders = order.iter().filter_map(|id| {
        let expression = program.node(*id)?;
        match &expression.kind {
            PureExprKind::Value(PureValue::Function(function)) => Some(function.parameter().id()),
            PureExprKind::Computation(PureComputation::Bind(binding)) => {
                Some(binding.binder().id())
            }
            PureExprKind::Value(
                PureValue::Integer(_) | PureValue::Boolean(_) | PureValue::Unit(_),
            )
            | PureExprKind::Variable(_)
            | PureExprKind::Computation(
                PureComputation::Apply(_) | PureComputation::Primitive(_),
            ) => None,
        }
    });
    builder.reserve_resolved_binders(binders)?;

    let mut remapped = vec![None; program.node_count()];
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
    builder.finish(root).map_err(TransformError::from)
}

fn rebuild_node(
    builder: &mut CoreBuilder,
    program: &ValidatedProgram,
    remapped: &[Option<NodeId>],
    expression: &super::TypedExpr,
    fold_literal_primitives: bool,
) -> Result<NodeId, TransformError> {
    if fold_literal_primitives
        && let PureExprKind::Computation(PureComputation::Primitive(operation)) = &expression.kind
        && let Some(value) = folded_literal(program, *operation)
    {
        return builder
            .integer(
                value,
                expression.ty.clone(),
                Origin::Generated {
                    cause: Box::new(expression.origin.clone()),
                    reason: GeneratedReason::ConstantFolding,
                },
            )
            .map_err(TransformError::from);
    }

    match &expression.kind {
        PureExprKind::Value(PureValue::Integer(node)) => builder
            .integer(
                node.value().clone(),
                expression.ty.clone(),
                expression.origin.clone(),
            )
            .map_err(TransformError::from),
        PureExprKind::Value(PureValue::Boolean(node)) => builder
            .boolean(
                node.value(),
                expression.ty.clone(),
                expression.origin.clone(),
            )
            .map_err(TransformError::from),
        PureExprKind::Value(PureValue::Unit(_)) => builder
            .unit(expression.ty.clone(), expression.origin.clone())
            .map_err(TransformError::from),
        PureExprKind::Value(PureValue::Function(node)) => {
            let parameter = builder.resolved_binder(
                node.parameter().id(),
                node.parameter().ty().clone(),
                node.parameter().origin().clone(),
            )?;
            builder
                .function(
                    parameter,
                    remap(remapped, node.body())?,
                    expression.ty.clone(),
                    expression.origin.clone(),
                )
                .map_err(TransformError::from)
        }
        PureExprKind::Variable(node) => builder
            .variable(
                node.binder(),
                expression.ty.clone(),
                expression.origin.clone(),
            )
            .map_err(TransformError::from),
        PureExprKind::Computation(PureComputation::Bind(node)) => {
            let binder = builder.resolved_binder(
                node.binder().id(),
                node.binder().ty().clone(),
                node.binder().origin().clone(),
            )?;
            builder
                .binding(
                    binder,
                    remap(remapped, node.initializer())?,
                    remap(remapped, node.body())?,
                    expression.ty.clone(),
                    expression.origin.clone(),
                )
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Apply(node)) => builder
            .application(
                remap(remapped, node.function())?,
                remap(remapped, node.argument())?,
                expression.ty.clone(),
                expression.origin.clone(),
            )
            .map_err(TransformError::from),
        PureExprKind::Computation(PureComputation::Primitive(node)) => builder
            .primitive(
                node.primitive(),
                remap(remapped, node.left())?,
                remap(remapped, node.right())?,
                expression.ty.clone(),
                expression.origin.clone(),
            )
            .map_err(TransformError::from),
    }
}

fn postorder(
    program: &ValidatedProgram,
    fold_literal_primitives: bool,
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
                work.push(Task::Exit(id));
                let expression = program
                    .node(id)
                    .ok_or(TransformError::InvalidValidatedInput)?;
                let children = if fold_literal_primitives
                    && matches!(
                        &expression.kind,
                        PureExprKind::Computation(PureComputation::Primitive(operation))
                            if is_foldable_literal(program, *operation)
                    ) {
                    [None, None]
                } else {
                    expression.kind.children()
                };
                for child in children.into_iter().flatten().rev() {
                    work.push(Task::Enter(child));
                }
            }
            Task::Exit(id) => order.push(id),
        }
    }
    Ok(order)
}

fn folded_literal(
    program: &ValidatedProgram,
    operation: super::primitive::PrimitiveNode,
) -> Option<crate::integer::Integer> {
    let PureExprKind::Value(PureValue::Integer(left)) = &program.node(operation.left())?.kind
    else {
        return None;
    };
    let PureExprKind::Value(PureValue::Integer(right)) = &program.node(operation.right())?.kind
    else {
        return None;
    };
    match operation.primitive() {
        Primitive::Add => Some(left.value() + right.value()),
        Primitive::Multiply => Some(left.value() * right.value()),
        Primitive::Equal => None,
    }
}

fn is_foldable_literal(
    program: &ValidatedProgram,
    operation: super::primitive::PrimitiveNode,
) -> bool {
    matches!(operation.primitive(), Primitive::Add | Primitive::Multiply)
        && matches!(
            program.node(operation.left()).map(|node| &node.kind),
            Some(PureExprKind::Value(PureValue::Integer(_)))
        )
        && matches!(
            program.node(operation.right()).map(|node| &node.kind),
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
