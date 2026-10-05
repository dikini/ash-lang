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
pub(super) enum Atom {
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

fn invalid() -> ValidationError {
    ValidationError::new(crate::core::ValidationReason::NodeType, None)
}

impl NodeProjection {
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
    fn binder(
        &mut self,
        binder: &TypedBinder,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        self.atom(Atom::Binder(binder.id()), work)?;
        self.ty(binder.ty(), work)?;
        self.origin(binder.origin(), work)
    }
    fn pattern(
        &mut self,
        root: &CorePattern,
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
        instance: &crate::types::EffectInstance,
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

pub(super) fn project_binder(
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
    let mut result = NodeProjection {
        node,
        children: Vec::new(),
        atoms: Vec::new(),
        metadata: Vec::new(),
        origins: Vec::new(),
    };
    result.ty(&stored.ty, work)?;
    result.row(&stored.effects, work)?;
    result.origin(stored.origin.as_ref().ok_or_else(invalid)?, work)?;
    charge(work, stored.kind.child_count())?;
    result
        .children
        .try_reserve_exact(stored.kind.child_count())
        .map_err(|_| resource())?;
    for ordinal in 0..stored.kind.child_count() {
        result
            .children
            .push(stored.kind.child_at(ordinal).ok_or_else(invalid)?);
    }
    match &stored.kind {
        EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
            result.atom(Atom::Tag(0), work)?;
            result.atom(Atom::Binder(variable.binder()), work)?;
        }
        EffectExprKind::Pure(PureExprKind::Value(value)) => match value {
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
        EffectExprKind::Pure(PureExprKind::Computation(computation)) => match computation {
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
                    let kind = crate::types::clone_kind_with_budget(kind, work)
                        .map_err(|()| resource())?;
                    result.metadata(Metadata::Kind(kind), work)?;
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
        EffectExprKind::Operation(operation) => match operation {
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
            // Nested scopes carry independently admitted proof projections.
            // They cannot enter an original-template certificate implicitly.
            EffectOperation::ProviderScope(_) => return Err(invalid()),
        },
    }
    Ok(result)
}

impl NodeProjection {
    pub(in crate::core) fn same(
        &self,
        other: &Self,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        charge(
            work,
            self.children
                .len()
                .checked_add(self.atoms.len())
                .and_then(|n| n.checked_add(self.metadata.len()))
                .and_then(|n| n.checked_add(self.origins.len()))
                .ok_or_else(resource)?,
        )?;
        if self.node != other.node
            || self.children != other.children
            || self.atoms.len() != other.atoms.len()
            || self.metadata.len() != other.metadata.len()
            || self.origins.len() != other.origins.len()
        {
            return Ok(false);
        }
        for (left, right) in self.atoms.iter().zip(&other.atoms) {
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
        for (left, right) in self.metadata.iter().zip(&other.metadata) {
            let same = match (left, right) {
                (Metadata::Type(left), Metadata::Type(right)) => {
                    same_type_with_budget(left, right, work).map_err(|()| resource())?
                }
                (Metadata::Row(left), Metadata::Row(right)) => {
                    same_effect_rows_with_budget(left, right, work).map_err(|()| resource())?
                }
                (Metadata::Argument(left), Metadata::Argument(right)) => {
                    same_kinded_argument_with_budget(left, right, work).map_err(|()| resource())?
                }
                (Metadata::Kind(left), Metadata::Kind(right)) => {
                    same_kind_with_budget(left, right, work).map_err(|()| resource())?
                }
                _ => false,
            };
            if !same {
                return Ok(false);
            }
        }
        for (left, right) in self.origins.iter().zip(&other.origins) {
            if !crate::resolved::same_origin_with_budget(left.as_origin(), right.as_origin(), work)
                .map_err(|()| resource())?
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
