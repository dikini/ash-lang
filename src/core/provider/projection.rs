//! Exact, bounded projections of checked code. Preparation projections may
//! contain conditional rows. Executable projections must be fully realized.

use super::{RetainedHandlerOrigin, charge, resource};
use crate::{
    core::{
        CorePattern, CorePatternKind, EffectExprKind, EffectOperation, NodeId, PureComputation,
        PureExprKind, PureValue, TypedBinder, ValidationError, dialect::StoredNode,
        effect::EffectOperationFamily,
    },
    interface::MethodId,
    resolved::{BinderId, ResourceDefinitionId, ResumeId},
    source::Origin,
    types::{
        ConstructorId, EffectId, EffectRow, IterativeArgumentOwner, IterativeTypeOwner, Kind,
        KindedArgument, NominalTypeId, OperationId, Type, TypeVariableId, TypeWorkBudget,
        clone_effect_row_with_budget, clone_kinded_argument_with_budget, clone_type_with_budget,
        same_effect_rows_with_budget, same_kind_with_budget, same_kinded_argument_with_budget,
        same_type_with_budget,
    },
};

/// Typed scalar identities keep nominal, term, control, and authority spaces
/// distinct. Tags also retain empty lists and pattern/operation boundaries.
#[derive(Debug, Eq, PartialEq)]
pub(in crate::core) enum Atom {
    Tag(u8),
    Count(usize),
    Boolean(bool),
    Literal(String),
    Packed(std::sync::Arc<[u8]>),
    Intrinsic(crate::core::packed::IntrinsicNode),
    Binder(BinderId),
    Variable(TypeVariableId),
    Nominal(NominalTypeId),
    Constructor(ConstructorId),
    Effect(EffectId),
    Operation(OperationId),
    Handler(crate::core::HandlerId),
    Resume(ResumeId),
    Method(MethodId),
    Definition(ResourceDefinitionId),
    Primitive(crate::core::Primitive),
    Direction(crate::core::NewtypeConversionDirection),
    ResumeUse(crate::core::ResumeUse),
    Acquisition(crate::resolved::ResourceAcquisition),
    Span(crate::source::Span),
}

pub(super) enum Metadata {
    Type(IterativeTypeOwner),
    Argument(IterativeArgumentOwner),
    Row(EffectRow),
    Kind(Kind),
}
#[derive(Clone, Copy)]
pub(in crate::core) enum MetadataView<'a> {
    Type(&'a Type),
    Argument(&'a KindedArgument),
    Row(&'a EffectRow),
    Kind(&'a Kind),
}
impl Metadata {
    pub(in crate::core) fn view(&self) -> MetadataView<'_> {
        match self {
            Self::Type(value) => MetadataView::Type(value),
            Self::Argument(value) => MetadataView::Argument(value),
            Self::Row(value) => MetadataView::Row(value),
            Self::Kind(value) => MetadataView::Kind(value),
        }
    }
}

impl std::fmt::Debug for Metadata {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Type(value) => formatter.debug_tuple("Type").field(&**value).finish(),
            Self::Argument(value) => formatter.debug_tuple("Argument").field(&**value).finish(),
            Self::Row(value) => formatter.debug_tuple("Row").field(value).finish(),
            Self::Kind(value) => formatter.debug_tuple("Kind").field(value).finish(),
        }
    }
}

#[derive(Debug)]
pub(in crate::core) struct NodeProjection {
    pub(super) node: NodeId,
    pub(super) children: Vec<NodeId>,
    pub(super) atoms: Vec<Atom>,
    pub(super) metadata: Vec<Metadata>,
    pub(super) origins: Vec<RetainedHandlerOrigin>,
}

/// Temporary specialized metadata with exact original, unchanged provenance.
/// It cannot outlive its original projection or escape as retained evidence.
pub(in crate::core) struct BorrowedOriginProjection<'a> {
    projection: NodeProjection,
    origins: Vec<&'a Origin>,
}
impl<'a> BorrowedOriginProjection<'a> {
    pub(super) fn new(
        projection: NodeProjection,
        original: &'a impl ProjectionView,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let mut origins = Vec::new();
        // The shared projection construction already prices each retained slot.
        origins
            .try_reserve_exact(original.origins().len())
            .map_err(|_| resource())?;
        for origin in original.origins() {
            let mut current = origin;
            let mut admitted = false;
            for _ in 0..=crate::core::dialect::CORE_PAYLOAD_DEPTH_LIMIT {
                // Visit the original chain without allocating a duplicate.
                charge(work, 1)?;
                match current {
                    Origin::Source(_) => {
                        admitted = true;
                        break;
                    }
                    Origin::Generated { cause, .. } => current = cause,
                    Origin::Related { primary, .. } => current = primary,
                }
            }
            if !admitted {
                return Err(resource());
            }
            origins.push(origin);
        }
        Ok(Self {
            projection,
            origins,
        })
    }
    pub(in crate::core) fn replace_effects(
        &mut self,
        row: EffectRow,
    ) -> Result<(), ValidationError> {
        self.projection.replace_effects(row)
    }
    pub(in crate::core) fn same_borrowed(
        &self,
        other: &BorrowedNodeProjection<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        same_projection(self, other, work)
    }
}
impl ProjectionView for BorrowedOriginProjection<'_> {
    fn node(&self) -> NodeId {
        self.projection.node
    }
    fn children(&self) -> &[NodeId] {
        &self.projection.children
    }
    fn atoms(&self) -> &[Atom] {
        &self.projection.atoms
    }
    fn metadata(&self) -> impl ExactSizeIterator<Item = MetadataView<'_>> {
        self.projection.metadata.iter().map(Metadata::view)
    }
    fn origins(&self) -> impl ExactSizeIterator<Item = &Origin> {
        self.origins.iter().copied()
    }
}

fn invalid() -> ValidationError {
    ValidationError::new(crate::core::ValidationReason::NodeType, None)
}

impl NodeProjection {
    pub(in crate::core) fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        uses.charge(self.atoms.len() + self.metadata.len())?;
        for atom in &self.atoms {
            match atom {
                Atom::Variable(id) => uses.id(*id)?,
                Atom::Acquisition(acquisition) => uses.id(acquisition.identity)?,
                _ => {}
            }
        }
        for metadata in &self.metadata {
            match metadata.view() {
                MetadataView::Type(ty) => uses.ty(ty)?,
                MetadataView::Argument(argument) => uses.argument(argument)?,
                MetadataView::Row(row) => uses.row(row)?,
                MetadataView::Kind(_) => {}
            }
        }
        Ok(())
    }
    pub(in crate::core) fn replace_effects(
        &mut self,
        row: EffectRow,
    ) -> Result<(), ValidationError> {
        let Some(Metadata::Row(effects)) = self.metadata.get_mut(1) else {
            return Err(invalid());
        };
        *effects = row;
        Ok(())
    }

    pub(in crate::core) fn node(&self) -> NodeId {
        self.node
    }
    pub(in crate::core) fn authenticate_source_node(
        &self,
        program: &crate::core::UnvalidatedEffectProgram,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let actual = project(self.node, super::node(program, self.node)?, work)?;
        if self.same(&actual, work)? {
            Ok(())
        } else {
            Err(super::invalid(self.node))
        }
    }
    fn atom(&mut self, atom: Atom, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        charge(work, 1)?;
        self.atoms.try_reserve(1).map_err(|_| resource())?;
        self.atoms.push(atom);
        Ok(())
    }
    fn metadata(
        &mut self,
        value: Metadata,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, 1)?;
        self.metadata.try_reserve(1).map_err(|_| resource())?;
        self.metadata.push(value);
        Ok(())
    }
    fn ty(&mut self, value: &Type, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        let value =
            IterativeTypeOwner::new(clone_type_with_budget(value, work).map_err(|()| resource())?);
        self.metadata(Metadata::Type(value), work)
    }
    fn row(&mut self, value: &EffectRow, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        let value = clone_effect_row_with_budget(value, work).map_err(|()| resource())?;
        self.metadata(Metadata::Row(value), work)
    }
    fn argument(
        &mut self,
        value: &KindedArgument,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let value = IterativeArgumentOwner::new(
            clone_kinded_argument_with_budget(value, work).map_err(|()| resource())?,
        );
        self.metadata(Metadata::Argument(value), work)
    }
    fn origin(&mut self, value: &Origin, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        let value = RetainedHandlerOrigin::copy(value, work)?;
        charge(work, 1)?;
        self.origins.try_reserve(1).map_err(|_| resource())?;
        self.origins.push(value);
        Ok(())
    }
}

/// Both owned evidence and borrowed comparison views use this one emitter.
/// Borrowing removes allocation/copy work only; it never skips a field or check.
trait ProjectionSink<'a> {
    fn atom(&mut self, atom: Atom, work: &mut TypeWorkBudget) -> Result<(), ValidationError>;
    fn ty(&mut self, value: &'a Type, work: &mut TypeWorkBudget) -> Result<(), ValidationError>;
    fn row(
        &mut self,
        value: &'a EffectRow,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError>;
    fn argument(
        &mut self,
        value: &'a KindedArgument,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError>;
    fn kind(&mut self, value: &'a Kind, work: &mut TypeWorkBudget) -> Result<(), ValidationError>;
    fn origin(
        &mut self,
        value: &'a Origin,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError>;
    fn children(&mut self) -> &mut Vec<NodeId>;
    fn binder(
        &mut self,
        binder: &'a TypedBinder,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        self.atom(Atom::Binder(binder.id()), work)?;
        self.ty(binder.ty(), work)?;
        self.origin(binder.origin(), work)
    }
    fn pattern(
        &mut self,
        root: &'a CorePattern,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, 1)?;
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| resource())?;
        pending.push(root);
        while let Some(pattern) = pending.pop() {
            charge(work, 1)?;
            self.ty(&pattern.ty, work)?;
            self.origin(&pattern.origin, work)?;
            match &pattern.kind {
                CorePatternKind::Wildcard => self.atom(Atom::Tag(0), work)?,
                CorePatternKind::Unit => self.atom(Atom::Tag(1), work)?,
                CorePatternKind::Boolean(value) => {
                    self.atom(Atom::Tag(2), work)?;
                    self.atom(Atom::Boolean(*value), work)?;
                }
                CorePatternKind::Binder(binder) => {
                    self.atom(Atom::Tag(3), work)?;
                    self.binder(binder, work)?;
                }
                CorePatternKind::Tuple(elements) => {
                    self.atom(Atom::Tag(4), work)?;
                    self.atom(Atom::Count(elements.len()), work)?;
                    charge(work, elements.len())?;
                    pending
                        .try_reserve(elements.len())
                        .map_err(|_| resource())?;
                    pending.extend(elements.iter().rev());
                }
                CorePatternKind::Constructor {
                    constructor,
                    payload,
                } => {
                    self.atom(Atom::Tag(5), work)?;
                    self.atom(Atom::Constructor(*constructor), work)?;
                    self.atom(Atom::Boolean(payload.is_some()), work)?;
                    if let Some(payload) = payload {
                        charge(work, 1)?;
                        pending.try_reserve(1).map_err(|_| resource())?;
                        pending.push(payload);
                    }
                }
            }
        }
        Ok(())
    }
    fn instance(
        &mut self,
        instance: &'a crate::types::EffectInstance,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        self.atom(Atom::Effect(instance.effect()), work)?;
        self.atom(Atom::Count(instance.arguments().len()), work)?;
        for argument in instance.arguments() {
            self.argument(argument, work)?;
        }
        Ok(())
    }
}
impl<'a> ProjectionSink<'a> for NodeProjection {
    fn atom(&mut self, value: Atom, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        NodeProjection::atom(self, value, work)
    }
    fn ty(&mut self, value: &'a Type, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        NodeProjection::ty(self, value, work)
    }
    fn row(
        &mut self,
        value: &'a EffectRow,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        NodeProjection::row(self, value, work)
    }
    fn argument(
        &mut self,
        value: &'a KindedArgument,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        NodeProjection::argument(self, value, work)
    }
    fn kind(&mut self, value: &'a Kind, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        self.metadata(
            Metadata::Kind(
                crate::types::clone_kind_with_budget(value, work).map_err(|()| resource())?,
            ),
            work,
        )
    }
    fn origin(
        &mut self,
        value: &'a Origin,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        NodeProjection::origin(self, value, work)
    }
    fn children(&mut self) -> &mut Vec<NodeId> {
        &mut self.children
    }
}

/// An invocation-local representation of exact immutable original/target
/// nodes. It cannot escape the arena borrow or stand for a checked result.
pub(in crate::core) struct BorrowedNodeProjection<'a> {
    pub(super) node: NodeId,
    pub(super) children: Vec<NodeId>,
    pub(super) atoms: Vec<Atom>,
    pub(super) metadata: Vec<MetadataView<'a>>,
    pub(super) origins: Vec<&'a Origin>,
}
impl<'a> ProjectionSink<'a> for BorrowedNodeProjection<'a> {
    fn atom(&mut self, atom: Atom, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        charge(work, 1)?;
        self.atoms.try_reserve(1).map_err(|_| resource())?;
        self.atoms.push(atom);
        Ok(())
    }
    fn ty(&mut self, value: &'a Type, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        self.metadata(MetadataView::Type(value), work)
    }
    fn row(
        &mut self,
        value: &'a EffectRow,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        self.metadata(MetadataView::Row(value), work)
    }
    fn argument(
        &mut self,
        value: &'a KindedArgument,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        self.metadata(MetadataView::Argument(value), work)
    }
    fn kind(&mut self, value: &'a Kind, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        self.metadata(MetadataView::Kind(value), work)
    }
    fn origin(
        &mut self,
        value: &'a Origin,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, 1)?;
        self.origins.try_reserve(1).map_err(|_| resource())?;
        self.origins.push(value);
        Ok(())
    }
    fn children(&mut self) -> &mut Vec<NodeId> {
        &mut self.children
    }
}
impl<'a> BorrowedNodeProjection<'a> {
    fn metadata(
        &mut self,
        value: MetadataView<'a>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, 1)?;
        self.metadata.try_reserve(1).map_err(|_| resource())?;
        self.metadata.push(value);
        Ok(())
    }
}

pub(in crate::core) trait ProjectionView {
    fn node(&self) -> NodeId;
    fn children(&self) -> &[NodeId];
    fn atoms(&self) -> &[Atom];
    fn metadata(&self) -> impl ExactSizeIterator<Item = MetadataView<'_>>;
    fn origins(&self) -> impl ExactSizeIterator<Item = &Origin>;
}
impl ProjectionView for NodeProjection {
    fn node(&self) -> NodeId {
        self.node
    }
    fn children(&self) -> &[NodeId] {
        &self.children
    }
    fn atoms(&self) -> &[Atom] {
        &self.atoms
    }
    fn metadata(&self) -> impl ExactSizeIterator<Item = MetadataView<'_>> {
        self.metadata.iter().map(Metadata::view)
    }
    fn origins(&self) -> impl ExactSizeIterator<Item = &Origin> {
        self.origins.iter().map(RetainedHandlerOrigin::as_origin)
    }
}
impl ProjectionView for BorrowedNodeProjection<'_> {
    fn node(&self) -> NodeId {
        self.node
    }
    fn children(&self) -> &[NodeId] {
        &self.children
    }
    fn atoms(&self) -> &[Atom] {
        &self.atoms
    }
    fn metadata(&self) -> impl ExactSizeIterator<Item = MetadataView<'_>> {
        self.metadata.iter().copied()
    }
    fn origins(&self) -> impl ExactSizeIterator<Item = &Origin> {
        self.origins.iter().copied()
    }
}

pub(in crate::core) fn project_clause(
    clause: &crate::core::EffectClause,
    work: &mut TypeWorkBudget,
) -> Result<NodeProjection, ValidationError> {
    let mut result = NodeProjection {
        node: clause.body(),
        children: Vec::new(),
        atoms: Vec::new(),
        metadata: Vec::new(),
        origins: Vec::new(),
    };
    result.atom(Atom::Operation(clause.operation()), work)?;
    result.atom(Atom::Resume(clause.resume()), work)?;
    result.pattern(clause.pattern(), work)?;
    result.origin(clause.origin(), work)?;
    Ok(result)
}

pub(in crate::core) fn project_binder(
    node: NodeId,
    binder: &TypedBinder,
    work: &mut TypeWorkBudget,
) -> Result<NodeProjection, ValidationError> {
    let mut result = NodeProjection {
        node,
        children: Vec::new(),
        atoms: Vec::new(),
        metadata: Vec::new(),
        origins: Vec::new(),
    };
    result.binder(binder, work)?;
    Ok(result)
}

pub(in crate::core) fn project_pattern(
    node: NodeId,
    pattern: &CorePattern,
    work: &mut TypeWorkBudget,
) -> Result<NodeProjection, ValidationError> {
    let mut result = NodeProjection {
        node,
        children: Vec::new(),
        atoms: Vec::new(),
        metadata: Vec::new(),
        origins: Vec::new(),
    };
    result.pattern(pattern, work)?;
    Ok(result)
}

/// Formatting is used only for arbitrary precision literal values. Every
/// written byte is charged before fallible storage; identities never use text.
fn literal(
    value: &crate::integer::Integer,
    work: &mut TypeWorkBudget,
) -> Result<String, ValidationError> {
    use std::fmt::Write;
    struct Output<'a> {
        text: String,
        work: &'a mut TypeWorkBudget,
    }
    impl Write for Output<'_> {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            self.work.charge(text.len()).map_err(|()| std::fmt::Error)?;
            self.text
                .try_reserve(text.len())
                .map_err(|_| std::fmt::Error)?;
            self.text.push_str(text);
            Ok(())
        }
    }
    let mut output = Output {
        text: String::new(),
        work,
    };
    write!(&mut output, "{value}").map_err(|_| resource())?;
    Ok(output.text)
}

pub(in crate::core) fn project(
    node: NodeId,
    stored: &StoredNode<EffectOperationFamily>,
    work: &mut TypeWorkBudget,
) -> Result<NodeProjection, ValidationError> {
    project_with::<EffectOperationFamily>(
        node,
        stored,
        |kind| match kind {
            EffectExprKind::Operation(operation) => Some(operation),
            EffectExprKind::Pure(_) => None,
        },
        work,
    )
}

enum ProjectionKind<'a> {
    Pure(&'a PureExprKind),
    Operation(&'a EffectOperation),
}

/// Borrows generic Core through its genuine pure/operation views. This shares
/// the exact projection encoding with ordinary Effect Core admission.
pub(in crate::core) fn project_with<F: crate::core::dialect::CoreOperationFamily>(
    node: NodeId,
    stored: &StoredNode<F>,
    operation: for<'a> fn(&'a F::Kind) -> Option<&'a EffectOperation>,
    work: &mut TypeWorkBudget,
) -> Result<NodeProjection, ValidationError> {
    let mut result = NodeProjection {
        node,
        children: Vec::new(),
        atoms: Vec::new(),
        metadata: Vec::new(),
        origins: Vec::new(),
    };
    emit_projection::<F, _>(&mut result, stored, operation, work)?;
    Ok(result)
}

pub(in crate::core) fn project_borrowed<'a>(
    node: NodeId,
    stored: &'a StoredNode<EffectOperationFamily>,
    work: &mut TypeWorkBudget,
) -> Result<BorrowedNodeProjection<'a>, ValidationError> {
    let mut result = BorrowedNodeProjection {
        node,
        children: Vec::new(),
        atoms: Vec::new(),
        metadata: Vec::new(),
        origins: Vec::new(),
    };
    emit_projection::<EffectOperationFamily, _>(
        &mut result,
        stored,
        |kind| match kind {
            EffectExprKind::Operation(operation) => Some(operation),
            EffectExprKind::Pure(_) => None,
        },
        work,
    )?;
    Ok(result)
}

fn emit_projection<'a, F: crate::core::dialect::CoreOperationFamily, S: ProjectionSink<'a>>(
    result: &mut S,
    stored: &'a StoredNode<F>,
    operation: for<'b> fn(&'b F::Kind) -> Option<&'b EffectOperation>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    result.ty(&stored.ty, work)?;
    result.row(F::effect_row(&stored.effects), work)?;
    result.origin(stored.origin.as_ref().ok_or_else(invalid)?, work)?;
    charge(work, F::child_count(&stored.kind))?;
    result
        .children()
        .try_reserve_exact(F::child_count(&stored.kind))
        .map_err(|_| resource())?;
    for ordinal in 0..F::child_count(&stored.kind) {
        result
            .children()
            .push(F::child_at(&stored.kind, ordinal).ok_or_else(invalid)?);
    }
    let kind = match (F::pure(&stored.kind), operation(&stored.kind)) {
        (Some(pure), None) => ProjectionKind::Pure(pure),
        (None, Some(operation)) => ProjectionKind::Operation(operation),
        _ => return Err(invalid()),
    };
    match kind {
        ProjectionKind::Pure(PureExprKind::Variable(variable)) => {
            result.atom(Atom::Tag(0), work)?;
            result.atom(Atom::Binder(variable.binder()), work)?;
        }
        ProjectionKind::Pure(PureExprKind::Value(value)) => match value {
            PureValue::String(string) => {
                result.atom(Atom::Tag(45), work)?;
                work.charge(string.bytes().len()).map_err(|()| resource())?;
                result.atom(Atom::Packed(std::sync::Arc::clone(string.bytes())), work)?;
            }
            PureValue::Intrinsic(intrinsic) => {
                result.atom(Atom::Tag(46), work)?;
                result.atom(Atom::Intrinsic(*intrinsic), work)?;
            }
            PureValue::Integer(integer) => {
                result.atom(Atom::Tag(1), work)?;
                let text = literal(integer.value(), work)?;
                result.atom(Atom::Literal(text), work)?;
            }
            PureValue::Boolean(boolean) => {
                result.atom(Atom::Tag(2), work)?;
                result.atom(Atom::Boolean(boolean.value()), work)?;
            }
            PureValue::Unit(_) => result.atom(Atom::Tag(3), work)?,
            PureValue::Function(function) => {
                result.atom(Atom::Tag(4), work)?;
                result.binder(function.parameter(), work)?;
            }
            PureValue::Constructor(constructor) => {
                result.atom(Atom::Tag(5), work)?;
                result.atom(Atom::Constructor(constructor.constructor()), work)?;
            }
        },
        ProjectionKind::Pure(PureExprKind::Computation(computation)) => match computation {
            PureComputation::Bind(binding) => {
                result.atom(Atom::Tag(6), work)?;
                result.binder(binding.binder(), work)?;
            }
            PureComputation::RecursiveBind(group) => {
                result.atom(Atom::Tag(7), work)?;
                result.atom(Atom::Count(group.members().len()), work)?;
                for member in group.members() {
                    result.binder(member.binder(), work)?;
                }
            }
            PureComputation::Apply(_) => result.atom(Atom::Tag(8), work)?,
            PureComputation::Primitive(primitive) => {
                result.atom(Atom::Tag(9), work)?;
                result.atom(Atom::Primitive(primitive.primitive()), work)?;
            }
            PureComputation::Tuple(tuple) => {
                result.atom(Atom::Tag(10), work)?;
                result.atom(Atom::Count(tuple.elements().len()), work)?;
            }
            PureComputation::Match(matching) => {
                result.atom(Atom::Tag(11), work)?;
                result.atom(Atom::Count(matching.arms().len()), work)?;
                for arm in matching.arms() {
                    result.pattern(arm.pattern(), work)?;
                    result.origin(arm.origin(), work)?;
                }
            }
            PureComputation::NewtypeConversion(conversion) => {
                result.atom(Atom::Tag(12), work)?;
                result.atom(Atom::Nominal(conversion.owner()), work)?;
                result.atom(Atom::Direction(conversion.direction()), work)?;
            }
            PureComputation::LocalNominalScope(scope) => {
                result.atom(Atom::Tag(13), work)?;
                result.atom(Atom::Nominal(scope.owner()), work)?;
            }
            PureComputation::TypeAbstraction(abstraction) => {
                result.atom(Atom::Tag(14), work)?;
                result.atom(Atom::Count(abstraction.parameters().len()), work)?;
                for (identity, kind) in abstraction.parameters() {
                    result.atom(Atom::Variable(*identity), work)?;
                    result.kind(kind, work)?;
                }
            }
            PureComputation::TypeApplication(application) => {
                result.atom(Atom::Tag(15), work)?;
                result.atom(Atom::Count(application.arguments().len()), work)?;
                for argument in application.arguments() {
                    result.ty(argument, work)?;
                }
                result.atom(Atom::Count(application.row_arguments().len()), work)?;
                for argument in application.row_arguments() {
                    result.row(argument, work)?;
                }
            }
        },
        ProjectionKind::Operation(operation) => match operation {
            EffectOperation::Request(request) => {
                result.atom(Atom::Tag(16), work)?;
                result.atom(Atom::Operation(request.operation()), work)?;
                result.instance(request.effect(), work)?;
            }
            EffectOperation::Resume(resume) => {
                result.atom(Atom::Tag(17), work)?;
                result.atom(Atom::Handler(resume.handler()), work)?;
                result.atom(Atom::Resume(resume.owner()), work)?;
                result.atom(Atom::ResumeUse(resume.use_state()), work)?;
            }
            EffectOperation::Discard(discard) => {
                result.atom(Atom::Tag(18), work)?;
                result.atom(Atom::Handler(discard.handler()), work)?;
                result.atom(Atom::Resume(discard.owner()), work)?;
                result.atom(Atom::ResumeUse(discard.use_state()), work)?;
            }
            EffectOperation::Handler(handler) => {
                // Hook source contracts require their own copied authority
                // relation; omitting them from a projection grants no proof.
                if handler.hook_root().is_some() || handler.hook_registration.is_some() {
                    return Err(invalid());
                }
                result.atom(Atom::Tag(19), work)?;
                result.atom(Atom::Handler(handler.id()), work)?;
                result.instance(handler.effect(), work)?;
                result.atom(Atom::Count(handler.clauses().len()), work)?;
                for clause in handler.clauses() {
                    result.atom(Atom::Operation(clause.operation()), work)?;
                    result.atom(Atom::Resume(clause.resume()), work)?;
                    result.pattern(clause.pattern(), work)?;
                    result.origin(clause.origin(), work)?;
                }
            }
            EffectOperation::ProviderStateAccess(access) => {
                result.atom(Atom::Tag(20), work)?;
                result.atom(Atom::Method(access.method()), work)?;
                result.atom(Atom::Definition(access.definition()), work)?;
                result.atom(Atom::Count(access.arguments().len()), work)?;
                for argument in access.arguments() {
                    result.argument(argument, work)?;
                }
            }
            EffectOperation::Cleanup(cleanup) => {
                result.atom(Atom::Tag(21), work)?;
                result.atom(Atom::Binder(cleanup.callback), work)?;
                result.atom(Atom::Span(cleanup.span), work)?;
                result.atom(Atom::Span(cleanup.action_span), work)?;
            }
            EffectOperation::Registration(registration) => {
                result.atom(Atom::Tag(22), work)?;
                result.atom(Atom::Handler(registration.handler), work)?;
                result.atom(Atom::Binder(registration.callback), work)?;
                result.atom(Atom::Span(registration.span), work)?;
            }
            EffectOperation::Resource(resource) => {
                result.atom(Atom::Tag(23), work)?;
                result.atom(Atom::Acquisition(resource.acquisition), work)?;
                result.binder(&resource.handle, work)?;
            }
            EffectOperation::SourceCopyWindow(scope) => {
                result.atom(Atom::Tag(24), work)?;
                result.atom(Atom::Nominal(scope.family().nominal()), work)?;
                result.atom(Atom::Variable(scope.identity()), work)?;
                result.atom(Atom::Count(scope.arguments().len()), work)?;
                for argument in scope.arguments() {
                    result.argument(argument, work)?;
                }
                result.atom(Atom::Count(scope.interpretations().len()), work)?;
                for interpretation in scope.interpretations() {
                    result.atom(Atom::Operation(interpretation.symbol().operation()), work)?;
                    result.instance(interpretation.effect(), work)?;
                }
            }
            // Nested scopes carry independently admitted proof projections.
            // They cannot enter an original-template certificate implicitly.
            EffectOperation::ProviderScope(_)
            | EffectOperation::SourceResourceScope(_)
            | EffectOperation::NativeInterpret(_) => {
                return Err(invalid());
            }
        },
    }
    Ok(())
}

impl NodeProjection {
    pub(in crate::core) fn same(
        &self,
        other: &Self,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        same_projection(self, other, work)
    }
    #[cfg(test)]
    pub(in crate::core) fn same_borrowed(
        &self,
        other: &BorrowedNodeProjection<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        same_projection(self, other, work)
    }
}
fn same_projection(
    left: &impl ProjectionView,
    right: &impl ProjectionView,
    work: &mut TypeWorkBudget,
) -> Result<bool, ValidationError> {
    charge(
        work,
        left.children()
            .len()
            .checked_add(left.atoms().len())
            .and_then(|n| n.checked_add(left.metadata().len()))
            .and_then(|n| n.checked_add(left.origins().len()))
            .ok_or_else(resource)?,
    )?;
    if left.node() != right.node()
        || left.children() != right.children()
        || left.atoms().len() != right.atoms().len()
        || left.metadata().len() != right.metadata().len()
        || left.origins().len() != right.origins().len()
    {
        return Ok(false);
    }
    for (left, right) in left.atoms().iter().zip(right.atoms()) {
        if let (Atom::Literal(left), Atom::Literal(right)) = (left, right) {
            charge(work, left.len().max(right.len()))?;
        }
        if let (Atom::Packed(left), Atom::Packed(right)) = (left, right) {
            charge(work, left.len().max(right.len()))?;
        }
        if left != right {
            return Ok(false);
        }
    }
    for (left, right) in left.metadata().zip(right.metadata()) {
        let same = match (left, right) {
            (MetadataView::Type(left), MetadataView::Type(right)) => {
                same_type_with_budget(left, right, work).map_err(|()| resource())?
            }
            (MetadataView::Row(left), MetadataView::Row(right)) => {
                same_effect_rows_with_budget(left, right, work).map_err(|()| resource())?
            }
            (MetadataView::Argument(left), MetadataView::Argument(right)) => {
                same_kinded_argument_with_budget(left, right, work).map_err(|()| resource())?
            }
            (MetadataView::Kind(left), MetadataView::Kind(right)) => {
                same_kind_with_budget(left, right, work).map_err(|()| resource())?
            }
            _ => false,
        };
        if !same {
            return Ok(false);
        }
    }
    for (left, right) in left.origins().zip(right.origins()) {
        if !crate::resolved::same_origin_with_budget(left, right, work).map_err(|()| resource())? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod borrowed_origin_tests {
    use super::*;
    use crate::core::provider::specialization::{
        ProviderFreshening, ProviderTemplateSubstitution, SourceScopeFreshening,
        specialize_source_projection, specialize_source_projection_borrowing_origins,
    };

    #[test]
    fn borrowed_original_origins_keep_donors_depth_and_exact_work() {
        let source = crate::source::SourceFile::new("origin.ash", "x").unwrap();
        let span = source
            .span(crate::source::ByteRange::new(0, 1).unwrap())
            .unwrap();
        let origin = Origin::Related {
            primary: Box::new(Origin::Generated {
                cause: Box::new(Origin::Source(span)),
                reason: crate::source::GeneratedReason::TypeChecking,
            }),
            related: vec![span, span],
        };
        let node = NodeId::new(crate::core::dialect::ArenaId::new(1), 0);
        let unit = Type::Unit;
        let row = EffectRow::empty();
        let original = BorrowedNodeProjection {
            node,
            children: vec![],
            atoms: vec![],
            metadata: vec![MetadataView::Type(&unit), MetadataView::Row(&row)],
            origins: vec![&origin],
        };
        let copied = std::collections::HashMap::from([(node, node)]);
        let types = std::collections::HashMap::new();
        let rows = std::collections::HashMap::new();
        let pending = std::collections::HashMap::new();
        let variables = std::collections::HashMap::new();
        let nominals = std::collections::HashMap::new();
        let sigma = ProviderTemplateSubstitution {
            types: &types,
            rows: &rows,
            pending: &pending,
        };
        let renaming = crate::types::TemplateIdentityRenaming {
            variables: &variables,
            nominals: &nominals,
        };
        let fresh = ProviderFreshening {
            binders: &[],
            types: &[],
            handlers: &[],
            resumes: &[],
            nominals: &[],
            lexicals: &[],
        };
        let lookup =
            SourceScopeFreshening::new(&fresh, &variables, &mut TypeWorkBudget::default()).unwrap();
        let make = |work: &mut TypeWorkBudget| {
            let value = specialize_source_projection_borrowing_origins(
                &original, &copied, &lookup, &sigma, &renaming, work,
            )?;
            assert!(value.same_borrowed(&original, work)?);
            Ok::<_, ValidationError>(())
        };
        let mut measured = TypeWorkBudget::default();
        make(&mut measured).unwrap();
        let cost = measured.used();
        let mut retained_work = TypeWorkBudget::default();
        let owned = specialize_source_projection(
            &original,
            &copied,
            &lookup,
            &sigma,
            &renaming,
            &mut retained_work,
        )
        .unwrap();
        assert!(owned.same_borrowed(&original, &mut retained_work).unwrap());
        assert!(cost < retained_work.used());
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                make(&mut short).unwrap_err().reason(),
                crate::core::ValidationReason::Resource
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                make(&mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
                assert_eq!(
                    make(&mut exact).unwrap_err().reason(),
                    crate::core::ValidationReason::Resource
                );
            }
        }
        let donor = crate::source::SourceFile::new("donor.ash", "x").unwrap();
        let mut target = BorrowedNodeProjection {
            node,
            children: vec![],
            atoms: vec![],
            metadata: vec![MetadataView::Type(&unit), MetadataView::Row(&row)],
            origins: vec![&origin],
        };
        let donor_origin = Origin::Related {
            primary: Box::new(Origin::Generated {
                cause: Box::new(Origin::Source(
                    donor
                        .span(crate::source::ByteRange::new(0, 1).unwrap())
                        .unwrap(),
                )),
                reason: crate::source::GeneratedReason::TypeChecking,
            }),
            related: vec![span, span],
        };
        target.origins[0] = &donor_origin;
        let value = specialize_source_projection_borrowing_origins(
            &original,
            &copied,
            &lookup,
            &sigma,
            &renaming,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        assert!(
            !value
                .same_borrowed(&target, &mut TypeWorkBudget::default())
                .unwrap()
        );
        for depth in [
            crate::core::dialect::CORE_PAYLOAD_DEPTH_LIMIT,
            crate::core::dialect::CORE_PAYLOAD_DEPTH_LIMIT + 1,
        ] {
            let mut depth_origin = Origin::Source(span);
            for _ in 0..depth {
                depth_origin = Origin::Generated {
                    cause: Box::new(depth_origin),
                    reason: crate::source::GeneratedReason::TypeChecking,
                };
            }
            let view = BorrowedNodeProjection {
                node,
                children: vec![],
                atoms: vec![],
                metadata: vec![],
                origins: vec![&depth_origin],
            };
            let result = specialize_source_projection_borrowing_origins(
                &view,
                &copied,
                &lookup,
                &sigma,
                &renaming,
                &mut TypeWorkBudget::default(),
            );
            if depth == crate::core::dialect::CORE_PAYLOAD_DEPTH_LIMIT {
                assert!(result.is_ok());
            } else {
                match result {
                    Err(e) => assert_eq!(e.reason(), crate::core::ValidationReason::Resource),
                    Ok(_) => panic!("overdeep original must refuse"),
                };
            }
        }
    }
}
