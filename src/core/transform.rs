//! Bounded transformations over independently validated pure Core.

use std::{error::Error, fmt, sync::Arc};

use super::{
    BuildError, CoreBuilder, CoreMatchArm, CorePattern, CorePatternKind, NodeId, Primitive,
    PureComputation, PureExprKind, PureValue, UnvalidatedProgram, ValidatedProgram,
};
use crate::{
    source::{GeneratedReason, Origin},
    types::{IterativeTypeOwner, Type, discard_type_iteratively},
};

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

    fn split_off(&mut self, at: usize) -> Self {
        Self(self.0.split_off(at))
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

fn rebuild(
    program: &ValidatedProgram,
    fold_literal_primitives: bool,
) -> Result<UnvalidatedProgram, TransformError> {
    rebuild_with_initial_type_work(program, fold_literal_primitives, 0)
}

fn rebuild_with_initial_type_work(
    program: &ValidatedProgram,
    fold_literal_primitives: bool,
    initial_type_work: usize,
) -> Result<UnvalidatedProgram, TransformError> {
    let order = postorder(program, fold_literal_primitives)?;
    let mut builder = CoreBuilder::with_registry(Arc::clone(program.registry()));
    #[cfg(test)]
    builder.charge_type_work_for_test(initial_type_work)?;
    #[cfg(not(test))]
    debug_assert_eq!(initial_type_work, 0);
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

    match &expression.kind {
        PureExprKind::Value(PureValue::Integer(node)) => {
            let ty = builder.clone_type_for_rebuild(&expression.ty)?;
            builder
                .integer(node.value().clone(), ty, expression.origin.clone())
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Boolean(node)) => {
            let ty = builder.clone_type_for_rebuild(&expression.ty)?;
            builder
                .boolean(node.value(), ty, expression.origin.clone())
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Unit(_)) => {
            let ty = builder.clone_type_for_rebuild(&expression.ty)?;
            builder
                .unit(ty, expression.origin.clone())
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Constructor(node)) => {
            let ty = builder.clone_type_for_rebuild(&expression.ty)?;
            builder
                .constructor(node.constructor(), ty, expression.origin.clone())
                .map_err(TransformError::from)
        }
        PureExprKind::Value(PureValue::Function(node)) => {
            let parameter_type = builder.clone_type_for_rebuild(node.parameter().ty())?;
            let parameter = builder.resolved_binder(
                node.parameter().id(),
                parameter_type,
                node.parameter().origin().clone(),
            )?;
            let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&expression.ty)?);
            let body = remap(remapped, node.body())?;
            let origin = expression.origin.clone();
            builder
                .function(parameter, body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Variable(node) => {
            let ty = builder.clone_type_for_rebuild(&expression.ty)?;
            builder
                .variable(node.binder(), ty, expression.origin.clone())
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Bind(node)) => {
            let binder_type = builder.clone_type_for_rebuild(node.binder().ty())?;
            let binder = builder.resolved_binder(
                node.binder().id(),
                binder_type,
                node.binder().origin().clone(),
            )?;
            let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&expression.ty)?);
            let initializer = remap(remapped, node.initializer())?;
            let body = remap(remapped, node.body())?;
            let origin = expression.origin.clone();
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
                let binder_type = builder.clone_type_for_rebuild(member.binder().ty())?;
                let binder = builder.resolved_binder(
                    member.binder().id(),
                    binder_type,
                    member.binder().origin().clone(),
                )?;
                members.push((binder, remap(remapped, member.initializer())?));
            }
            let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&expression.ty)?);
            let body = remap(remapped, node.body())?;
            let origin = expression.origin.clone();
            builder
                .recursive_binding(members, body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Apply(node)) => {
            let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&expression.ty)?);
            let function = remap(remapped, node.function())?;
            let argument = remap(remapped, node.argument())?;
            let origin = expression.origin.clone();
            builder
                .application(function, argument, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Primitive(node)) => {
            let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&expression.ty)?);
            let left = remap(remapped, node.left())?;
            let right = remap(remapped, node.right())?;
            let origin = expression.origin.clone();
            builder
                .primitive(node.primitive(), left, right, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Tuple(node)) => {
            let elements = node
                .elements()
                .iter()
                .map(|element| remap(remapped, *element))
                .collect::<Result<Vec<_>, _>>()?;
            let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&expression.ty)?);
            let origin = expression.origin.clone();
            builder
                .tuple(elements, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::Match(node)) => {
            let arms = node
                .arms()
                .iter()
                .map(|arm| {
                    let pattern = CorePatternOwner::new(rebuild_pattern(builder, arm.pattern())?);
                    let body = remap(remapped, arm.body())?;
                    let origin = arm.origin().clone();
                    Ok(CoreMatchArm::new(pattern.into_inner(), body, origin))
                })
                .collect::<Result<Vec<_>, TransformError>>()?;
            let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&expression.ty)?);
            let scrutinee = remap(remapped, node.scrutinee())?;
            let origin = expression.origin.clone();
            builder
                .match_expression(scrutinee, arms, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::TypeAbstraction(node)) => {
            let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&expression.ty)?);
            let body = remap(remapped, node.body())?;
            let origin = expression.origin.clone();
            builder
                .type_abstraction_from_borrowed(node.parameters(), body, ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
        PureExprKind::Computation(PureComputation::TypeApplication(node)) => {
            let mut arguments = IterativeTypeBuffer(Vec::new());
            arguments
                .try_reserve(node.arguments().len())
                .map_err(|_| TransformError::Build(BuildError::TypeWorkExceeded))?;
            for argument in node.arguments() {
                arguments.push(builder.clone_type_for_rebuild(argument)?);
            }
            let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&expression.ty)?);
            let function = remap(remapped, node.function())?;
            let origin = expression.origin.clone();
            builder
                .type_application(function, arguments.into_vec(), ty.into_inner(), origin)
                .map_err(TransformError::from)
        }
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
                    let binder_type = builder.clone_type_for_rebuild(binder.ty())?;
                    let binder = builder.resolved_binder(
                        binder.id(),
                        binder_type,
                        binder.origin().clone(),
                    )?;
                    let ty = builder.clone_type_for_rebuild(&pattern.ty)?;
                    rebuilt.push(CorePattern::new(
                        ty,
                        pattern.origin.clone(),
                        CorePatternKind::Binder(binder),
                    ));
                }
                CorePatternKind::Wildcard => {
                    let ty = builder.clone_type_for_rebuild(&pattern.ty)?;
                    rebuilt.push(CorePattern::new(
                        ty,
                        pattern.origin.clone(),
                        CorePatternKind::Wildcard,
                    ));
                }
                CorePatternKind::Boolean(value) => {
                    let ty = builder.clone_type_for_rebuild(&pattern.ty)?;
                    rebuilt.push(CorePattern::new(
                        ty,
                        pattern.origin.clone(),
                        CorePatternKind::Boolean(*value),
                    ));
                }
                CorePatternKind::Unit => {
                    let ty = builder.clone_type_for_rebuild(&pattern.ty)?;
                    rebuilt.push(CorePattern::new(
                        ty,
                        pattern.origin.clone(),
                        CorePatternKind::Unit,
                    ));
                }
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
                let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&pattern.ty)?);
                rebuilt.push(CorePattern::new(
                    ty.into_inner(),
                    pattern.origin.clone(),
                    CorePatternKind::Tuple(elements.into_boxed_slice()),
                ));
            }
            Task::FinishConstructor(pattern, constructor, has_payload) => {
                let payload = if has_payload {
                    Some(rebuilt.pop().ok_or(TransformError::InvalidValidatedInput)?)
                } else {
                    None
                };
                let ty = IterativeTypeOwner::new(builder.clone_type_for_rebuild(&pattern.ty)?);
                rebuilt.push(CorePattern::new(
                    ty.into_inner(),
                    pattern.origin.clone(),
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
        types::{ConstructorId, Kind, NominalTypeId, TYPE_WORK_LIMIT, Type, TypeVariableId},
    };

    fn application_type(depth: usize) -> Type {
        let mut result = Type::Unit;
        for _ in 0..depth {
            result = Type::Application(Box::new(result), Box::new(Type::Unit));
        }
        result
    }

    #[test]
    fn higher_kinded_transform_copies_have_an_exact_type_budget() {
        // Body: one retained clone + one admission visit = 2.
        // Abstraction scheme: six clone units and six admission units.
        // Abstraction parameters: one binder record + three Kind nodes = 4.
        const EXACT_WORK: usize = 18;
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
}
