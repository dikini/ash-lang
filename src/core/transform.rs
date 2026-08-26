//! Bounded transformations over independently validated pure Core.

use std::{error::Error, fmt, sync::Arc};

use super::{
    BuildError, CoreBuilder, CoreMatchArm, CorePattern, CorePatternKind, NodeId, Primitive,
    PureComputation, PureExprKind, PureValue, UnvalidatedProgram, ValidatedProgram,
};
use crate::source::{GeneratedReason, Origin};

struct CorePatternBuffer(Vec<CorePattern>);

impl CorePatternBuffer {
    fn push(&mut self, pattern: CorePattern) {
        self.0.push(pattern);
    }

    fn pop(&mut self) -> Option<CorePattern> {
        self.0.pop()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn split_off(&mut self, at: usize) -> Vec<CorePattern> {
        self.0.split_off(at)
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

fn rebuild(
    program: &ValidatedProgram,
    fold_literal_primitives: bool,
) -> Result<UnvalidatedProgram, TransformError> {
    let order = postorder(program, fold_literal_primitives)?;
    let mut builder = CoreBuilder::with_registry(Arc::clone(program.registry()));
    let mut binders = Vec::new();
    for id in &order {
        let expression = program
            .node(*id)
            .ok_or(TransformError::InvalidValidatedInput)?;
        match &expression.kind {
            PureExprKind::Value(PureValue::Function(function)) => {
                binders.push(function.parameter().id());
            }
            PureExprKind::Computation(PureComputation::Bind(binding)) => {
                binders.push(binding.binder().id());
            }
            PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                binders.extend(group.members().iter().map(|member| member.binder().id()));
            }
            PureExprKind::Computation(PureComputation::Match(match_node)) => {
                for arm in match_node.arms() {
                    let mut pattern_binders = Vec::new();
                    arm.pattern().binders(&mut pattern_binders);
                    binders.extend(pattern_binders.into_iter().map(|binder| binder.id()));
                }
            }
            PureExprKind::Value(
                PureValue::Integer(_)
                | PureValue::Boolean(_)
                | PureValue::Unit(_)
                | PureValue::Constructor(_),
            )
            | PureExprKind::Variable(_)
            | PureExprKind::Computation(
                PureComputation::Apply(_)
                | PureComputation::Primitive(_)
                | PureComputation::Tuple(_)
                | PureComputation::TypeAbstraction(_)
                | PureComputation::TypeApplication(_),
            ) => {}
        }
    }
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
        PureExprKind::Value(PureValue::Constructor(node)) => builder
            .constructor(
                node.constructor(),
                expression.ty.clone(),
                expression.origin.clone(),
            )
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
        PureExprKind::Computation(PureComputation::RecursiveBind(node)) => {
            let mut members = Vec::with_capacity(node.members().len());
            for member in node.members() {
                let binder = builder.resolved_binder(
                    member.binder().id(),
                    member.binder().ty().clone(),
                    member.binder().origin().clone(),
                )?;
                members.push((binder, remap(remapped, member.initializer())?));
            }
            builder
                .recursive_binding(
                    members,
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
        PureExprKind::Computation(PureComputation::Tuple(node)) => builder
            .tuple(
                node.elements()
                    .iter()
                    .map(|element| remap(remapped, *element))
                    .collect::<Result<Vec<_>, _>>()?,
                expression.ty.clone(),
                expression.origin.clone(),
            )
            .map_err(TransformError::from),
        PureExprKind::Computation(PureComputation::Match(node)) => {
            let arms = node
                .arms()
                .iter()
                .map(|arm| {
                    Ok(CoreMatchArm::new(
                        rebuild_pattern(builder, arm.pattern())?,
                        remap(remapped, arm.body())?,
                        arm.origin().clone(),
                    ))
                })
                .collect::<Result<Vec<_>, TransformError>>()?;
            builder
                .match_expression(
                    remap(remapped, node.scrutinee())?,
                    arms,
                    expression.ty.clone(),
                    expression.origin.clone(),
                )
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::TypeAbstraction(node)) => builder
            .type_abstraction(
                node.parameters().to_vec(),
                remap(remapped, node.body())?,
                expression.ty.clone(),
                expression.origin.clone(),
            )
            .map_err(TransformError::from),
        PureExprKind::Computation(PureComputation::TypeApplication(node)) => builder
            .type_application(
                remap(remapped, node.function())?,
                node.arguments().to_vec(),
                expression.ty.clone(),
                expression.origin.clone(),
            )
            .map_err(TransformError::from),
    }
}

fn rebuild_pattern(
    builder: &mut CoreBuilder,
    pattern: &CorePattern,
) -> Result<CorePattern, TransformError> {
    enum Task<'a> {
        Visit(&'a CorePattern),
        FinishTuple(&'a CorePattern, usize),
        FinishConstructor(&'a CorePattern, crate::types::ConstructorId, bool),
    }

    let mut work = vec![Task::Visit(pattern)];
    let mut rebuilt = CorePatternBuffer(Vec::new());
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(pattern) => match &pattern.kind {
                CorePatternKind::Binder(binder) => {
                    let binder = builder.resolved_binder(
                        binder.id(),
                        binder.ty().clone(),
                        binder.origin().clone(),
                    )?;
                    rebuilt.push(CorePattern::new(
                        pattern.ty.clone(),
                        pattern.origin.clone(),
                        CorePatternKind::Binder(binder),
                    ));
                }
                CorePatternKind::Wildcard => rebuilt.push(CorePattern::new(
                    pattern.ty.clone(),
                    pattern.origin.clone(),
                    CorePatternKind::Wildcard,
                )),
                CorePatternKind::Boolean(value) => rebuilt.push(CorePattern::new(
                    pattern.ty.clone(),
                    pattern.origin.clone(),
                    CorePatternKind::Boolean(*value),
                )),
                CorePatternKind::Unit => rebuilt.push(CorePattern::new(
                    pattern.ty.clone(),
                    pattern.origin.clone(),
                    CorePatternKind::Unit,
                )),
                CorePatternKind::Tuple(elements) => {
                    work.push(Task::FinishTuple(pattern, elements.len()));
                    work.extend(elements.iter().rev().map(Task::Visit));
                }
                CorePatternKind::Constructor {
                    constructor,
                    payload,
                } => {
                    work.push(Task::FinishConstructor(
                        pattern,
                        *constructor,
                        payload.is_some(),
                    ));
                    if let Some(payload) = payload.as_deref() {
                        work.push(Task::Visit(payload));
                    }
                }
            },
            Task::FinishTuple(pattern, count) => {
                if rebuilt.len() < count {
                    return Err(TransformError::InvalidValidatedInput);
                }
                let elements = rebuilt.split_off(rebuilt.len() - count);
                rebuilt.push(CorePattern::new(
                    pattern.ty.clone(),
                    pattern.origin.clone(),
                    CorePatternKind::Tuple(elements.into_boxed_slice()),
                ));
            }
            Task::FinishConstructor(pattern, constructor, has_payload) => {
                let payload = if has_payload {
                    Some(Box::new(
                        rebuilt.pop().ok_or(TransformError::InvalidValidatedInput)?,
                    ))
                } else {
                    None
                };
                rebuilt.push(CorePattern::new(
                    pattern.ty.clone(),
                    pattern.origin.clone(),
                    CorePatternKind::Constructor {
                        constructor,
                        payload,
                    },
                ));
            }
        }
    }
    let result = rebuilt.pop().ok_or(TransformError::InvalidValidatedInput)?;
    if rebuilt.is_empty() {
        Ok(result)
    } else {
        result.discard_iteratively();
        Err(TransformError::InvalidValidatedInput)
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
                let child_count = if fold_literal_primitives
                    && matches!(
                            &expression.kind,
                            PureExprKind::Computation(PureComputation::Primitive(operation))
                                if is_foldable_literal(program, *operation)
                    ) {
                    0
                } else {
                    expression.kind.child_count()
                };
                for child_index in (0..child_count).rev() {
                    let child = expression
                        .kind
                        .child_at(child_index)
                        .ok_or(TransformError::InvalidValidatedInput)?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        resolved::BinderId,
        source::{ByteRange, SourceFile},
        types::Type,
    };

    fn application_type(depth: usize) -> Type {
        let mut result = Type::Unit;
        for _ in 0..depth {
            result = Type::Application(Box::new(result), Box::new(Type::Unit));
        }
        result
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
}
