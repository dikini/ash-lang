//! Effect operations hosted by the shared typed Core substrate.

use std::sync::Arc;

use super::{
    CoreBuilder, CoreMatchArm, CorePattern, NodeId, PureExprKind,
    dialect::{
        CoreOperationFamily, CoreTypedExpr, UnvalidatedCoreProgram, ValidatedCoreProgram,
        discard_pure_expr_kind_metadata,
    },
    validate::{ValidationError, validate_effect_family, validate_effect_modules_family},
};
use crate::{
    foreign::checked_source::CheckedForeignSymbol,
    resolved::{ResolvedRegistry, ResumeId},
    source::{Origin, discard_origin_iteratively},
    types::{
        EffectInstance, EffectRow, OperationId, Type, TypeWorkBudget, clone_effect_row_with_budget,
        discard_type_iteratively,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AshEffectDialect;

impl AshEffectDialect {
    pub const NAME: &'static str = "ash.effect";
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HandlerId(u32);

impl HandlerId {
    #[must_use]
    pub const fn new(value: u32) -> Self {
        Self(value)
    }
    #[must_use]
    pub const fn value(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResumeUse {
    Available,
    Consumed,
}

/// An exact native instance and its original checked source authority.
/// This metadata grants no bridge linkage or evaluator binding by itself.
#[derive(Clone, Debug)]
pub struct NativeInterpretation {
    pub(super) effect: EffectInstance,
    pub(super) symbol: Arc<CheckedForeignSymbol>,
}

impl NativeInterpretation {
    pub(crate) fn new(effect: EffectInstance, symbol: Arc<CheckedForeignSymbol>) -> Self {
        Self { effect, symbol }
    }
    #[must_use]
    pub const fn effect(&self) -> &EffectInstance {
        &self.effect
    }
    #[must_use]
    pub const fn symbol(&self) -> &Arc<CheckedForeignSymbol> {
        &self.symbol
    }
}

impl PartialEq for NativeInterpretation {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.symbol, &other.symbol) && self.effect == other.effect
    }
}
impl Eq for NativeInterpretation {}

/// Native symbol interpretation over the shared body and operation vector.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NativeInterpretNode {
    pub(super) body: NodeId,
    pub(super) interpretations: Box<[NativeInterpretation]>,
}

impl NativeInterpretNode {
    #[must_use]
    pub const fn body(&self) -> NodeId {
        self.body
    }
    #[must_use]
    pub fn interpretations(&self) -> &[NativeInterpretation] {
        &self.interpretations
    }
    pub(crate) fn into_parts(self) -> (NodeId, Box<[NativeInterpretation]>) {
        (self.body, self.interpretations)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RequestNode {
    pub(super) effect: EffectInstance,
    pub(super) operation: OperationId,
    pub(super) operand: NodeId,
}

impl RequestNode {
    pub(crate) fn new(effect: EffectInstance, operation: OperationId, operand: NodeId) -> Self {
        Self {
            effect,
            operation,
            operand,
        }
    }
    #[must_use]
    pub const fn effect(&self) -> &EffectInstance {
        &self.effect
    }
    #[must_use]
    pub const fn operation(&self) -> OperationId {
        self.operation
    }
    #[must_use]
    pub const fn operand(&self) -> NodeId {
        self.operand
    }
    pub(crate) fn into_parts(self) -> (EffectInstance, OperationId, NodeId) {
        (self.effect, self.operation, self.operand)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResumeNode {
    pub(super) handler: HandlerId,
    pub(super) owner: ResumeId,
    pub(super) use_state: ResumeUse,
    pub(super) value: NodeId,
}

impl ResumeNode {
    pub(crate) fn new(
        handler: HandlerId,
        owner: ResumeId,
        use_state: ResumeUse,
        value: NodeId,
    ) -> Self {
        Self {
            handler,
            owner,
            use_state,
            value,
        }
    }
    #[must_use]
    pub const fn handler(&self) -> HandlerId {
        self.handler
    }
    #[must_use]
    pub const fn owner(&self) -> ResumeId {
        self.owner
    }
    #[must_use]
    pub const fn use_state(&self) -> ResumeUse {
        self.use_state
    }
    #[must_use]
    pub const fn value(&self) -> NodeId {
        self.value
    }
    pub(crate) const fn into_parts(self) -> (HandlerId, ResumeId, ResumeUse, NodeId) {
        (self.handler, self.owner, self.use_state, self.value)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiscardNode {
    pub(super) handler: HandlerId,
    pub(super) owner: ResumeId,
    pub(super) use_state: ResumeUse,
}

impl DiscardNode {
    pub(crate) const fn new(handler: HandlerId, owner: ResumeId, use_state: ResumeUse) -> Self {
        Self {
            handler,
            owner,
            use_state,
        }
    }
    #[must_use]
    pub const fn handler(&self) -> HandlerId {
        self.handler
    }
    #[must_use]
    pub const fn owner(&self) -> ResumeId {
        self.owner
    }
    #[must_use]
    pub const fn use_state(&self) -> ResumeUse {
        self.use_state
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectClause {
    pub(super) operation: OperationId,
    pub(super) resume: ResumeId,
    pub(super) arm: CoreMatchArm,
}

impl EffectClause {
    #[must_use]
    pub const fn new(operation: OperationId, resume: ResumeId, arm: CoreMatchArm) -> Self {
        Self {
            operation,
            resume,
            arm,
        }
    }
    #[must_use]
    pub const fn operation(&self) -> OperationId {
        self.operation
    }
    #[must_use]
    pub const fn resume(&self) -> ResumeId {
        self.resume
    }
    #[must_use]
    pub fn pattern(&self) -> &CorePattern {
        self.arm.pattern()
    }
    #[must_use]
    pub const fn body(&self) -> NodeId {
        self.arm.body()
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        self.arm.origin()
    }
    pub(crate) fn into_parts(self) -> (OperationId, ResumeId, CoreMatchArm) {
        (self.operation, self.resume, self.arm)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HandlerNode {
    pub(super) hook_registration: Option<Box<crate::resolved::HookRegistrationContract>>,
    pub(super) hook_root: Option<crate::resolved::HookRootContract>,
    pub(super) id: HandlerId,
    pub(super) body: NodeId,
    pub(super) effect: EffectInstance,
    pub(super) clauses: Box<[EffectClause]>,
}

impl HandlerNode {
    pub(crate) fn new(
        id: HandlerId,
        body: NodeId,
        effect: EffectInstance,
        clauses: Vec<EffectClause>,
    ) -> Self {
        Self {
            hook_root: None,
            hook_registration: None,
            id,
            body,
            effect,
            clauses: clauses.into_boxed_slice(),
        }
    }
    #[must_use]
    pub const fn id(&self) -> HandlerId {
        self.id
    }
    #[must_use]
    pub const fn body(&self) -> NodeId {
        self.body
    }
    #[must_use]
    pub const fn effect(&self) -> &EffectInstance {
        &self.effect
    }
    #[must_use]
    pub const fn clauses(&self) -> &[EffectClause] {
        &self.clauses
    }
    #[must_use]
    pub const fn hook_root(&self) -> Option<&crate::resolved::HookRootContract> {
        self.hook_root.as_ref()
    }
    pub(crate) fn hook_registration(&self) -> Option<&crate::resolved::HookRegistrationContract> {
        self.hook_registration.as_deref()
    }
    pub(crate) fn with_hook_root(
        mut self,
        root: Option<crate::resolved::HookRootContract>,
    ) -> Self {
        self.hook_root = root;
        self
    }
    pub(crate) fn with_hook_registration(
        mut self,
        registration: Option<crate::resolved::HookRegistrationContract>,
    ) -> Self {
        self.hook_registration = registration.map(Box::new);
        self
    }
    #[allow(clippy::type_complexity)] // Ownership deconstruction keeps independent root and registration contracts explicit.
    pub(crate) fn into_parts(
        self,
    ) -> (
        HandlerId,
        NodeId,
        EffectInstance,
        Vec<EffectClause>,
        Option<crate::resolved::HookRootContract>,
        Option<Box<crate::resolved::HookRegistrationContract>>,
    ) {
        (
            self.id,
            self.body,
            self.effect,
            self.clauses.into_vec(),
            self.hook_root,
            self.hook_registration,
        )
    }
}

/// Required completion surrounding one generated registration handler.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RegistrationScopeNode {
    pub(crate) handler: HandlerId,
    pub(crate) callback: crate::resolved::BinderId,
    pub(crate) body: NodeId,
    pub(crate) span: crate::source::Span,
}

/// A non-interpreting owner; `action` is the authenticated callback application.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CleanupScopeNode {
    pub(crate) callback: crate::resolved::BinderId,
    pub(crate) body: NodeId,
    pub(crate) action: NodeId,
    pub(crate) span: crate::source::Span,
    pub(crate) action_span: crate::source::Span,
}

/// An acquisition owns its rigid identity and body-local handle. Its fixed-type
/// initializer is a preceding-scope child, not an ordinary constructor payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceScopeNode {
    pub(crate) acquisition: crate::resolved::ResourceAcquisition,
    pub(super) handle: super::TypedBinder,
    pub(super) initializer: NodeId,
    pub(super) body: NodeId,
}

impl ResourceScopeNode {
    /// Reconstruct the complete exact instance from the carrier's handle type.
    /// This checks shape only; linked validation authenticates defining facts.
    pub(crate) fn instance_with_budget(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<EffectInstance, super::BuildError> {
        let api = self
            .acquisition
            .api()
            .ok_or(super::BuildError::InvalidPayload)?;
        work.charge(api.argument_count() + 4)
            .map_err(|()| super::BuildError::TypeWorkExceeded)?;
        let (owner, payload) = if api.generic() {
            let Type::Application(owner, payload) = self.handle.ty() else {
                return Err(super::BuildError::InvalidPayload);
            };
            (&**owner, Some(&**payload))
        } else {
            (self.handle.ty(), None)
        };
        if !matches!(owner, Type::Application(head, argument) if **head == Type::Nominal(api.handle()) && **argument == Type::Variable(self.acquisition.identity))
        {
            return Err(super::BuildError::InvalidPayload);
        }
        let mut arguments = Vec::new();
        arguments
            .try_reserve_exact(api.argument_count())
            .map_err(|_| super::BuildError::TypeWorkExceeded)?;
        arguments.push(Type::Variable(self.acquisition.identity));
        if let Some(payload) = payload {
            arguments.push(
                crate::types::clone_type_with_budget(payload, work)
                    .map_err(|()| super::BuildError::TypeWorkExceeded)?,
            );
        }
        Ok(EffectInstance::new(api.ops(), arguments.into_boxed_slice()))
    }

    pub(crate) fn handle(&self) -> &super::TypedBinder {
        &self.handle
    }

    pub(crate) fn initializer(&self) -> NodeId {
        self.initializer
    }

    pub(crate) fn body(&self) -> NodeId {
        self.body
    }

    pub(crate) fn new(
        acquisition: crate::resolved::ResourceAcquisition,
        handle: super::TypedBinder,
        initializer: NodeId,
        body: NodeId,
    ) -> Self {
        Self {
            acquisition,
            handle,
            initializer,
            body,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EffectOperation {
    NativeInterpret(NativeInterpretNode),
    Cleanup(CleanupScopeNode),
    Registration(RegistrationScopeNode),
    Resource(Box<ResourceScopeNode>),

    Request(RequestNode),
    Handler(HandlerNode),
    Resume(ResumeNode),
    Discard(DiscardNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EffectExprKind {
    Pure(PureExprKind),
    Operation(EffectOperation),
}

impl EffectExprKind {
    #[must_use]
    pub fn child_count(&self) -> usize {
        EffectOperationFamily::child_count(self)
    }
    #[must_use]
    pub fn child_at(&self, index: usize) -> Option<NodeId> {
        EffectOperationFamily::child_at(self, index)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EffectOperationFamily;

impl CoreOperationFamily for EffectOperationFamily {
    type Kind = EffectExprKind;
    type Operation = EffectOperation;
    type Effects = EffectRow;
    const DIALECT_NAME: &'static str = AshEffectDialect::NAME;
    const REQUIRES_EMPTY_ROWS: bool = false;
    const ALLOWS_EFFECTFUL_TYPES: bool = true;

    fn from_pure(kind: PureExprKind) -> Self::Kind {
        EffectExprKind::Pure(kind)
    }
    fn from_operation(operation: Self::Operation) -> Self::Kind {
        EffectExprKind::Operation(operation)
    }
    fn pure(kind: &Self::Kind) -> Option<&PureExprKind> {
        match kind {
            EffectExprKind::Pure(kind) => Some(kind),
            EffectExprKind::Operation(_) => None,
        }
    }
    fn pure_mut(kind: &mut Self::Kind) -> Option<&mut PureExprKind> {
        match kind {
            EffectExprKind::Pure(kind) => Some(kind),
            EffectExprKind::Operation(_) => None,
        }
    }

    fn visit_operation_binders<'a>(
        kind: &'a Self::Kind,
        visit: &mut dyn FnMut(&'a super::TypedBinder),
    ) {
        if let EffectExprKind::Operation(EffectOperation::Resource(resource)) = kind {
            visit(&resource.handle);
        }
        let handler = match kind {
            EffectExprKind::Operation(EffectOperation::Handler(handler)) => handler,
            _ => return,
        };
        for clause in &handler.clauses {
            for binder in clause.pattern().binder_iter() {
                visit(binder);
            }
        }
    }

    fn visit_operation_type_metadata<'a>(
        kind: &'a Self::Kind,
        visit: &mut dyn FnMut(super::dialect::OperationTypeMetadata<'a>),
    ) {
        let EffectExprKind::Operation(operation) = kind else {
            return;
        };
        let instance = match operation {
            EffectOperation::NativeInterpret(boundary) => {
                for interpretation in &boundary.interpretations {
                    for argument in interpretation.effect.arguments() {
                        visit(super::dialect::OperationTypeMetadata::Argument(argument));
                    }
                }
                None
            }

            EffectOperation::Resource(resource) => {
                visit(super::dialect::OperationTypeMetadata::Type(
                    resource.handle.ty(),
                ));
                None
            }
            EffectOperation::Request(request) => Some(&request.effect),
            EffectOperation::Handler(handler) => {
                if let Some(registration) = &handler.hook_registration {
                    for argument in registration.target.arguments() {
                        visit(super::dialect::OperationTypeMetadata::Argument(argument));
                    }
                }
                if let Some(root) = &handler.hook_root {
                    for argument in root.target.arguments() {
                        visit(super::dialect::OperationTypeMetadata::Argument(argument));
                    }
                }
                for clause in &handler.clauses {
                    visit(super::dialect::OperationTypeMetadata::Pattern(
                        clause.pattern(),
                    ));
                }
                Some(&handler.effect)
            }
            EffectOperation::Cleanup(_)
            | EffectOperation::Registration(_)
            | EffectOperation::Resume(_)
            | EffectOperation::Discard(_) => None,
        };
        if let Some(instance) = instance {
            for argument in instance.arguments() {
                visit(super::dialect::OperationTypeMetadata::Argument(argument));
            }
        }
    }

    fn store_effects(effects: EffectRow) -> Self::Effects {
        effects
    }

    fn rewrite_operation_type_metadata(
        kind: &mut Self::Kind,
        rewrite: &mut dyn FnMut(&Type) -> Result<Type, super::BuildError>,
        charge: &mut dyn FnMut(usize) -> Result<(), super::BuildError>,
    ) -> Result<(), super::BuildError> {
        let instance = match kind {
            EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) => {
                charge(boundary.interpretations.len())?;
                for interpretation in &mut boundary.interpretations {
                    rewrite_effect_instance(&mut interpretation.effect, rewrite, charge)?;
                }
                return Ok(());
            }

            EffectExprKind::Operation(EffectOperation::Resource(resource)) => {
                charge(1)?;
                resource.handle.rewrite_type(&mut |ty| rewrite(ty))?;
                return Ok(());
            }
            EffectExprKind::Operation(EffectOperation::Request(request)) => &mut request.effect,
            EffectExprKind::Operation(EffectOperation::Handler(handler)) => {
                if let Some(registration) = &mut handler.hook_registration {
                    rewrite_effect_instance(&mut registration.target, rewrite, charge)?;
                }
                if let Some(root) = &mut handler.hook_root {
                    rewrite_effect_instance(&mut root.target, rewrite, charge)?;
                }
                charge(handler.clauses.len())?;
                for clause in &mut handler.clauses {
                    clause
                        .arm
                        .pattern_mut()
                        .rewrite_types(&mut |ty| rewrite(ty))?;
                }
                &mut handler.effect
            }
            _ => return Ok(()),
        };
        rewrite_effect_instance(instance, rewrite, charge)
    }

    fn effect_row(effects: &Self::Effects) -> &EffectRow {
        effects
    }

    fn discard_effects(effects: Self::Effects) {
        drop(effects);
    }
    fn child_count(kind: &Self::Kind) -> usize {
        match kind {
            EffectExprKind::Pure(kind) => kind.child_count(),
            EffectExprKind::Operation(EffectOperation::Cleanup(_)) => 2,

            EffectExprKind::Operation(EffectOperation::Registration(_)) => 1,
            EffectExprKind::Operation(EffectOperation::Resource(_)) => 2,

            EffectExprKind::Operation(
                EffectOperation::NativeInterpret(_)
                | EffectOperation::Request(_)
                | EffectOperation::Resume(_),
            ) => 1,
            EffectExprKind::Operation(EffectOperation::Discard(_)) => 0,

            EffectExprKind::Operation(EffectOperation::Handler(node)) => node.clauses.len() + 1,
        }
    }
    fn operation_extra_edge_count(kind: &Self::Kind) -> usize {
        match kind {
            EffectExprKind::Operation(EffectOperation::Handler(node)) => node.clauses.len(),
            _ => 0,
        }
    }
    fn child_at(kind: &Self::Kind, index: usize) -> Option<NodeId> {
        match kind {
            EffectExprKind::Pure(kind) => kind.child_at(index),
            EffectExprKind::Operation(EffectOperation::Cleanup(scope)) => match index {
                0 => Some(scope.body),
                1 => Some(scope.action),
                _ => None,
            },
            EffectExprKind::Operation(EffectOperation::Registration(scope)) => {
                (index == 0).then_some(scope.body)
            }

            EffectExprKind::Operation(EffectOperation::Resource(resource)) => match index {
                0 => Some(resource.initializer),
                1 => Some(resource.body),
                _ => None,
            },
            EffectExprKind::Operation(EffectOperation::Discard(_)) => None,
            EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) => {
                (index == 0).then_some(boundary.body)
            }
            EffectExprKind::Operation(EffectOperation::Request(node)) => {
                (index == 0).then_some(node.operand)
            }

            EffectExprKind::Operation(EffectOperation::Resume(node)) => {
                (index == 0).then_some(node.value)
            }
            EffectExprKind::Operation(EffectOperation::Handler(node)) => {
                if index == 0 {
                    Some(node.body)
                } else {
                    node.clauses.get(index - 1).map(EffectClause::body)
                }
            }
        }
    }
    fn discard_metadata(kind: Self::Kind) {
        match kind {
            EffectExprKind::Pure(kind) => discard_pure_expr_kind_metadata(kind),
            // Each EffectInstance owns iterative argument disposal. The shared
            // descriptor contains no copied recursive source/type structure.
            EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) => drop(boundary),
            EffectExprKind::Operation(
                EffectOperation::Registration(_) | EffectOperation::Cleanup(_),
            ) => {}
            EffectExprKind::Operation(EffectOperation::Resource(resource)) => drop(resource),

            EffectExprKind::Operation(EffectOperation::Request(mut node)) => {
                let placeholder = EffectInstance::new(node.effect.effect(), Box::new([]));
                let (_, arguments) = std::mem::replace(&mut node.effect, placeholder).into_parts();
                for argument in arguments {
                    crate::types::discard_kinded_argument_iteratively(argument);
                }
            }
            EffectExprKind::Operation(EffectOperation::Resume(_) | EffectOperation::Discard(_)) => {
            }
            EffectExprKind::Operation(EffectOperation::Handler(mut node)) => {
                let placeholder = EffectInstance::new(node.effect.effect(), Box::new([]));
                let (_, arguments) = std::mem::replace(&mut node.effect, placeholder).into_parts();
                for argument in arguments {
                    crate::types::discard_kinded_argument_iteratively(argument);
                }
                drop(std::mem::take(&mut node.clauses));
            }
        }
    }
}

pub type EffectExpr = CoreTypedExpr<EffectOperationFamily>;
pub type EffectCoreBuilder = CoreBuilder<EffectOperationFamily>;
pub type UnvalidatedEffectProgram = UnvalidatedCoreProgram<EffectOperationFamily>;
pub type ValidatedEffectProgram = ValidatedCoreProgram<EffectOperationFamily>;

impl CoreBuilder<EffectOperationFamily> {
    pub(crate) fn resource_scope(
        &mut self,
        resource: Box<ResourceScopeNode>,
        ty: Type,
        effects: EffectRow,
        origin: Origin,
    ) -> Result<NodeId, super::BuildError> {
        self.push_operation(ty, effects, origin, EffectOperation::Resource(resource))
    }
    pub fn with_effect_registry(registry: Arc<ResolvedRegistry>) -> Self {
        Self::with_registry_for_family(registry)
    }

    pub(crate) fn recompute_effect_rows_in_range(
        &mut self,
        range: std::ops::Range<usize>,
        output: &EffectRow,
        handler: HandlerId,
        owner: ResumeId,
    ) -> Result<(), super::BuildError> {
        self.replay_effect_rows_in_range(range, output, handler, owner, false)
    }

    fn replay_effect_rows_in_range(
        &mut self,
        range: std::ops::Range<usize>,
        output: &EffectRow,
        handler: HandlerId,
        owner: ResumeId,
        provisional: bool,
    ) -> Result<(), super::BuildError> {
        self.invalidate_settled_zonk_range(range.clone())?;
        enum Equation {
            Registration(NodeId),
            Cleanup(NodeId, NodeId),
            Pure,
            Replace,
            Request(NodeId, EffectInstance),
            NativeInterpret(NodeId, Box<[NativeInterpretation]>),
            Handler(EffectInstance, usize, bool),
            Resource(EffectInstance, NodeId, NodeId),

            Keep,
        }

        if range.start > range.end || range.end > self.nodes.len() {
            return Err(super::BuildError::InvalidNodeId);
        }
        self.charge_effect_metadata(range.len())?;
        let mut undo = Vec::new();
        undo.try_reserve_exact(range.len())
            .map_err(|_| super::BuildError::TypeWorkExceeded)?;
        let result = (|| {
            for index in range {
                self.charge_effect_metadata(1)?;
                let equation = match &self.nodes[index].kind {
                    EffectExprKind::Operation(EffectOperation::Cleanup(scope)) => {
                        Equation::Cleanup(scope.body, scope.action)
                    }
                    EffectExprKind::Operation(EffectOperation::Registration(scope)) => {
                        Equation::Registration(scope.body)
                    }
                    EffectExprKind::Operation(EffectOperation::Resource(resource)) => {
                        Equation::Resource(
                            resource.instance_with_budget(&mut self.type_work)?,
                            resource.initializer,
                            resource.body,
                        )
                    }

                    EffectExprKind::Pure(_) => Equation::Pure,
                    EffectExprKind::Operation(EffectOperation::Resume(resume))
                        if resume.handler == handler && resume.owner == owner =>
                    {
                        Equation::Replace
                    }
                    EffectExprKind::Operation(
                        EffectOperation::Resume(_) | EffectOperation::Discard(_),
                    ) => Equation::Keep,
                    EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) => {
                        Equation::NativeInterpret(
                            boundary.body,
                            copy_native_interpretations_with_budget(
                                &boundary.interpretations,
                                &mut self.type_work,
                            )?,
                        )
                    }
                    EffectExprKind::Operation(EffectOperation::Request(request)) => {
                        Equation::Request(
                            request.operand,
                            clone_effect_instance_with_budget(
                                &request.effect,
                                &mut self.type_work,
                            )?,
                        )
                    }
                    EffectExprKind::Operation(EffectOperation::Handler(nested)) => {
                        Equation::Handler(
                            if nested.hook_root.is_some() || nested.hook_registration.is_some() {
                                crate::types::clone_effect_instance_with_budget(
                                    &nested.effect,
                                    &mut self.type_work,
                                )
                                .map_err(|()| super::BuildError::TypeWorkExceeded)?
                            } else {
                                clone_effect_instance_with_budget(
                                    &nested.effect,
                                    &mut self.type_work,
                                )?
                            },
                            nested.clauses.len(),
                            nested.hook_root.is_some() || nested.hook_registration.is_some(),
                        )
                    }
                };
                let effects = match equation {
                    Equation::Cleanup(body, action) => {
                        let body = clone_effect_row_with_budget(
                            &self
                                .nodes
                                .get(body.index()?)
                                .ok_or(super::BuildError::InvalidNodeId)?
                                .effects,
                            &mut self.type_work,
                        )
                        .map_err(|()| super::BuildError::TypeWorkExceeded)?;
                        let action = &self
                            .nodes
                            .get(action.index()?)
                            .ok_or(super::BuildError::InvalidNodeId)?
                            .effects;
                        body.union_with_budget(action, &mut self.type_work)
                            .map_err(|()| super::BuildError::TypeWorkExceeded)?
                            .map_err(|_| super::BuildError::InvalidPayload)?
                    }
                    Equation::Registration(body) => clone_effect_row_with_budget(
                        &self
                            .nodes
                            .get(body.index()?)
                            .ok_or(super::BuildError::InvalidNodeId)?
                            .effects,
                        &mut self.type_work,
                    )
                    .map_err(|()| super::BuildError::TypeWorkExceeded)?,
                    Equation::Resource(instance, initializer, body) => {
                        let body = &self
                            .nodes
                            .get(body.index()?)
                            .ok_or(super::BuildError::InvalidNodeId)?
                            .effects;
                        let outward = match body
                            .remove_exact_with_budget(&instance, &mut self.type_work)
                            .map_err(|()| super::BuildError::TypeWorkExceeded)?
                        {
                            Ok(row) => row,
                            Err(crate::types::EffectRowError::Missing) => {
                                clone_effect_row_with_budget(body, &mut self.type_work)
                                    .map_err(|()| super::BuildError::TypeWorkExceeded)?
                            }
                            Err(_) => return Err(super::BuildError::InvalidPayload),
                        };
                        self.nodes
                            .get(initializer.index()?)
                            .ok_or(super::BuildError::InvalidNodeId)?
                            .effects
                            .union_with_budget(&outward, &mut self.type_work)
                            .map_err(|()| super::BuildError::TypeWorkExceeded)?
                            .map_err(|_| super::BuildError::InvalidPayload)?
                    }

                    Equation::Pure => self.infer_pure_effects_at(index)?,
                    Equation::Replace => clone_effect_row_with_budget(output, &mut self.type_work)
                        .map_err(|()| super::BuildError::TypeWorkExceeded)?,
                    Equation::Request(operand, effect) => {
                        let operand = operand.index()?;
                        let requested = EffectRow::singleton(effect);

                        self.nodes
                            .get(operand)
                            .ok_or(super::BuildError::InvalidNodeId)?
                            .effects
                            .union_with_budget(&requested, &mut self.type_work)
                            .map_err(|()| super::BuildError::TypeWorkExceeded)?
                            .map_err(|_| super::BuildError::InvalidPayload)?
                    }

                    Equation::NativeInterpret(body, interpretations) => {
                        let body = &self
                            .nodes
                            .get(body.index()?)
                            .ok_or(super::BuildError::InvalidNodeId)?
                            .effects;
                        native_interpret_outward_row(body, &interpretations, &mut self.type_work)?
                    }
                    Equation::Handler(effect, clause_count, hook_root) => {
                        self.charge_effect_metadata(clause_count)?;
                        let body = EffectOperationFamily::child_at(&self.nodes[index].kind, 0)
                            .ok_or(super::BuildError::InvalidPayload)?
                            .index()?;
                        let body_effects = &self
                            .nodes
                            .get(body)
                            .ok_or(super::BuildError::InvalidNodeId)?
                            .effects;
                        let mut effects = match body_effects
                            .remove_exact_with_budget(&effect, &mut self.type_work)
                            .map_err(|()| super::BuildError::TypeWorkExceeded)?
                        {
                            Ok(row) => row,
                            Err(crate::types::EffectRowError::Missing)
                                if hook_root || provisional =>
                            {
                                clone_effect_row_with_budget(body_effects, &mut self.type_work)
                                    .map_err(|()| super::BuildError::TypeWorkExceeded)?
                            }
                            Err(_) => return Err(super::BuildError::InvalidPayload),
                        };
                        for clause in 0..clause_count {
                            let body = EffectOperationFamily::child_at(
                                &self.nodes[index].kind,
                                clause + 1,
                            )
                            .ok_or(super::BuildError::InvalidPayload)?
                            .index()?;
                            effects = effects
                                .union_with_budget(
                                    &self
                                        .nodes
                                        .get(body)
                                        .ok_or(super::BuildError::InvalidNodeId)?
                                        .effects,
                                    &mut self.type_work,
                                )
                                .map_err(|()| super::BuildError::TypeWorkExceeded)?
                                .map_err(|_| super::BuildError::InvalidPayload)?;
                        }
                        effects
                    }
                    Equation::Keep => continue,
                };
                let previous = std::mem::replace(&mut self.nodes[index].effects, effects);
                undo.push((index, previous));
            }
            Ok(())
        })();
        if let Err(error) = result {
            while let Some((index, previous)) = undo.pop() {
                drop(std::mem::replace(&mut self.nodes[index].effects, previous));
            }
            return Err(error);
        }
        Ok(())
    }

    /// Completes source-only cleanup row replay after its row variables are solved.
    pub(crate) fn finish_cleanup_effect_rows(&mut self) -> Result<(), super::BuildError> {
        self.settled_zonk_nodes.clear();
        let count = self.nodes.len();
        self.charge_effect_metadata(count)?;
        let mut previous = Vec::new();
        previous
            .try_reserve_exact(count)
            .map_err(|_| super::BuildError::TypeWorkExceeded)?;
        let mut handlers = std::collections::HashMap::new();
        for index in 0..count {
            self.charge_effect_metadata(1)?;
            previous.push(
                clone_effect_row_with_budget(&self.nodes[index].effects, &mut self.type_work)
                    .map_err(|()| super::BuildError::TypeWorkExceeded)?,
            );

            let handler = match &self.nodes[index].kind {
                EffectExprKind::Operation(EffectOperation::Handler(handler)) => Some(handler),

                _ => None,
            };
            if let Some(handler) = handler {
                self.type_work
                    .charge(handler.clauses.len())
                    .map_err(|()| super::BuildError::TypeWorkExceeded)?;
                handlers
                    .try_reserve(handler.clauses.len())
                    .map_err(|_| super::BuildError::TypeWorkExceeded)?;
                for clause in &handler.clauses {
                    if handlers
                        .insert((handler.id, clause.resume), index)
                        .is_some()
                    {
                        return Err(super::BuildError::InvalidPayload);
                    }
                }
            }
        }
        let result = (|| {
            // Final type coincidence can shrink an earlier handler output. Start
            // derived resume edges at bottom rather than retaining self-supporting
            // cached labels or tails. Stable call/discard leaves retain their rows
            // and authenticated lacks and reintroduce them during the replay.
            for index in 0..count {
                self.charge_effect_metadata(1)?;
                if matches!(
                    self.nodes[index].kind,
                    EffectExprKind::Operation(EffectOperation::Resume(_))
                ) {
                    self.nodes[index].effects = EffectRow::empty();
                }
            }
            // Solving fixes tail identities and exclusions. Replaying union and exact
            // removal only propagates the finite known-label vocabulary monotonically.
            // A nested handler can acquire an outer resume's output after its own
            // clause was visited; refresh those resume edges until none changes.
            loop {
                self.replay_effect_rows_in_range(
                    0..count,
                    &EffectRow::empty(),
                    HandlerId::new(u32::MAX),
                    ResumeId::new(u32::MAX),
                    true,
                )?;
                let mut changed = false;
                for index in 0..count {
                    self.charge_effect_metadata(1)?;
                    let EffectExprKind::Operation(EffectOperation::Resume(resume)) =
                        &self.nodes[index].kind
                    else {
                        continue;
                    };
                    let owner = *handlers
                        .get(&(resume.handler, resume.owner))
                        .ok_or(super::BuildError::InvalidPayload)?;
                    // Operand work is intrinsic even while the owner output is
                    // bottom. At the fixed point it is included in that output.
                    let owner_output = &self.nodes[owner].effects;
                    let output = owner_output
                        .union_with_budget(
                            &self.nodes[resume.value.index()?].effects,
                            &mut self.type_work,
                        )
                        .map_err(|()| super::BuildError::TypeWorkExceeded)?
                        .map_err(|_| super::BuildError::InvalidPayload)?;
                    if !crate::types::same_effect_rows_with_budget(
                        &self.nodes[index].effects,
                        &output,
                        &mut self.type_work,
                    )
                    .map_err(|()| super::BuildError::TypeWorkExceeded)?
                    {
                        self.nodes[index].effects = output;
                        changed = true;
                    }
                }
                if !changed {
                    return self.recompute_effect_rows_in_range(
                        0..count,
                        &EffectRow::empty(),
                        HandlerId::new(u32::MAX),
                        ResumeId::new(u32::MAX),
                    );
                }
            }
        })();
        if result.is_err() {
            for (node, row) in self.nodes.iter_mut().zip(previous) {
                node.effects = row;
            }
        }
        result
    }

    pub fn native_interpret(
        &mut self,
        body: NodeId,
        mut interpretations: Box<[NativeInterpretation]>,
        result_type: Type,
        effects: EffectRow,
        origin: Origin,
    ) -> Result<NodeId, super::BuildError> {
        let admitted = (|| {
            self.charge_effect_metadata(interpretations.len())?;
            for interpretation in &mut interpretations {
                let placeholder = EffectInstance::new(interpretation.effect.effect(), Box::new([]));
                let instance = std::mem::replace(&mut interpretation.effect, placeholder);
                interpretation.effect = self.admit_effect_instance(instance)?;
            }
            Ok(())
        })();
        if let Err(error) = admitted {
            discard_type_iteratively(result_type);
            drop(effects);
            discard_origin_iteratively(origin);
            return Err(error);
        }
        self.push_operation(
            result_type,
            effects,
            origin,
            EffectOperation::NativeInterpret(NativeInterpretNode {
                body,
                interpretations,
            }),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn request(
        &mut self,
        effect: EffectInstance,
        operation: OperationId,
        operand: NodeId,
        result_type: Type,
        effects: EffectRow,
        origin: Origin,
    ) -> Result<NodeId, super::BuildError> {
        let effect = match self.admit_effect_instance(effect) {
            Ok(effect) => effect,
            Err(error) => {
                discard_type_iteratively(result_type);
                drop(effects);
                discard_origin_iteratively(origin);
                return Err(error);
            }
        };
        self.push_operation(
            result_type,
            effects,
            origin,
            EffectOperation::Request(RequestNode::new(effect, operation, operand)),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn resume(
        &mut self,
        handler: HandlerId,
        owner: ResumeId,
        use_state: ResumeUse,
        value: NodeId,
        result_type: Type,
        effects: EffectRow,
        origin: Origin,
    ) -> Result<NodeId, super::BuildError> {
        self.push_operation(
            result_type,
            effects,
            origin,
            EffectOperation::Resume(ResumeNode::new(handler, owner, use_state, value)),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn discard(
        &mut self,
        handler: HandlerId,
        owner: ResumeId,
        use_state: ResumeUse,
        result_type: Type,
        effects: EffectRow,
        origin: Origin,
    ) -> Result<NodeId, super::BuildError> {
        self.push_operation(
            result_type,
            effects,
            origin,
            EffectOperation::Discard(DiscardNode::new(handler, owner, use_state)),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn handler(
        &mut self,
        id: HandlerId,
        body: NodeId,
        effect: EffectInstance,
        clauses: Vec<EffectClause>,
        result_type: Type,
        effects: EffectRow,
        origin: Origin,
    ) -> Result<NodeId, super::BuildError> {
        self.handler_with_root(
            id,
            body,
            effect,
            clauses,
            result_type,
            effects,
            origin,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn handler_with_root(
        &mut self,
        id: HandlerId,
        body: NodeId,
        effect: EffectInstance,
        clauses: Vec<EffectClause>,
        result_type: Type,
        effects: EffectRow,
        origin: Origin,
        hook_root: Option<crate::resolved::HookRootContract>,
    ) -> Result<NodeId, super::BuildError> {
        self.handler_with_contracts(
            id,
            body,
            effect,
            clauses,
            result_type,
            effects,
            origin,
            hook_root,
            None,
        )
    }

    pub(crate) fn cleanup_scope(
        &mut self,
        scope: CleanupScopeNode,
        ty: Type,
        effects: EffectRow,
        origin: Origin,
    ) -> Result<NodeId, super::BuildError> {
        self.push_operation(ty, effects, origin, EffectOperation::Cleanup(scope))
    }

    pub(crate) fn registration_scope(
        &mut self,
        scope: RegistrationScopeNode,
        ty: Type,
        effects: EffectRow,
        origin: Origin,
    ) -> Result<NodeId, super::BuildError> {
        self.push_operation(ty, effects, origin, EffectOperation::Registration(scope))
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn handler_with_contracts(
        &mut self,
        id: HandlerId,
        body: NodeId,
        effect: EffectInstance,
        clauses: Vec<EffectClause>,
        result_type: Type,
        effects: EffectRow,
        origin: Origin,
        hook_root: Option<crate::resolved::HookRootContract>,
        hook_registration: Option<Box<crate::resolved::HookRegistrationContract>>,
    ) -> Result<NodeId, super::BuildError> {
        let effect = match self.admit_effect_instance(effect) {
            Ok(effect) => effect,
            Err(error) => {
                drop(clauses);
                discard_type_iteratively(result_type);
                drop(effects);
                discard_origin_iteratively(origin);
                return Err(error);
            }
        };
        if let Err(error) = self.charge_effect_metadata(
            clauses
                .len()
                .saturating_add(usize::from(hook_root.is_some()))
                .saturating_add(usize::from(hook_registration.is_some())),
        ) {
            drop(effect);
            drop(clauses);
            discard_type_iteratively(result_type);
            drop(effects);
            discard_origin_iteratively(origin);
            return Err(error);
        }
        let mut admitted = Vec::new();
        if admitted.try_reserve_exact(clauses.len()).is_err() {
            drop(effect);
            drop(clauses);
            discard_type_iteratively(result_type);
            drop(effects);
            discard_origin_iteratively(origin);
            return Err(super::BuildError::TypeWorkExceeded);
        }
        let mut remaining = clauses.into_iter();
        while let Some(clause) = remaining.next() {
            let (operation, resume, arm) = clause.into_parts();
            match self.admit_effect_clause_arm(arm) {
                Ok(arm) => admitted.push(EffectClause::new(operation, resume, arm)),
                Err(error) => {
                    drop(effect);
                    drop(admitted);
                    drop(remaining);
                    discard_type_iteratively(result_type);
                    drop(effects);
                    discard_origin_iteratively(origin);
                    return Err(error);
                }
            }
        }
        let clauses = admitted;
        let mut handler = HandlerNode::new(id, body, effect, clauses).with_hook_root(hook_root);
        handler.hook_registration = hook_registration;
        self.push_operation(
            result_type,
            effects,
            origin,
            EffectOperation::Handler(handler),
        )
    }
}

fn rewrite_effect_instance(
    instance: &mut EffectInstance,
    rewrite: &mut dyn FnMut(&Type) -> Result<Type, super::BuildError>,
    charge: &mut dyn FnMut(usize) -> Result<(), super::BuildError>,
) -> Result<(), super::BuildError> {
    let count = instance.arguments().len();
    charge(
        count
            .checked_mul(2)
            .ok_or(super::BuildError::TypeWorkExceeded)?,
    )?;
    let mut staged = Vec::new();
    staged
        .try_reserve(count)
        .map_err(|_| super::BuildError::TypeWorkExceeded)?;
    let mut meter = |cells| charge(cells);
    for argument in instance.arguments() {
        let argument = crate::types::map_kinded_argument_types_with_budget(
            argument,
            &mut |ty, _| rewrite(ty),
            &mut meter,
            &mut |_| super::BuildError::TypeWorkExceeded,
        )?;
        staged.push(crate::types::IterativeArgumentOwner::new(argument));
    }
    let mut arguments = Vec::new();
    arguments
        .try_reserve(count)
        .map_err(|_| super::BuildError::TypeWorkExceeded)?;
    arguments.extend(
        staged
            .into_iter()
            .map(crate::types::IterativeArgumentOwner::into_inner),
    );
    let replacement = EffectInstance::new_kinded(instance.effect(), arguments.into_boxed_slice());
    drop(std::mem::replace(instance, replacement));
    Ok(())
}

pub(crate) fn clone_effect_instance_with_budget(
    instance: &EffectInstance,
    budget: &mut TypeWorkBudget,
) -> Result<EffectInstance, super::BuildError> {
    // The shared clone charges the instance root; retain the existing
    // per-argument envelope charge for nonempty Type-only instances.
    budget
        .charge(instance.arguments().len().saturating_sub(1))
        .map_err(|()| super::BuildError::TypeWorkExceeded)?;
    crate::types::clone_effect_instance_with_budget(instance, budget)
        .map_err(|()| super::BuildError::TypeWorkExceeded)
}

pub fn validate_effect(
    program: UnvalidatedEffectProgram,
    sources: &[&crate::source::SourceFile],
) -> Result<ValidatedEffectProgram, ValidationError> {
    validate_effect_family(program, sources)
}

pub fn validate_effect_modules(
    program: UnvalidatedEffectProgram,
    sources: &[&crate::source::SourceFile],
    module_sources: &[(crate::module::ModuleId, crate::source::SourceId)],
) -> Result<ValidatedEffectProgram, ValidationError> {
    validate_effect_modules_family(program, sources, module_sources)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::Primitive,
        integer::Integer,
        module::ModuleId,
        resolved::ResumeId,
        source::{ByteRange, SourceFile},
        types::{EffectId, TYPE_WORK_LIMIT},
    };

    #[test]
    fn discard_has_no_children_and_keeps_its_empty_row_during_recomputation() {
        let source = SourceFile::new("discard-core.ash", "discard").unwrap();
        let origin = Origin::Source(source.span(ByteRange::new(0, 7).unwrap()).unwrap());
        let mut builder =
            EffectCoreBuilder::with_effect_registry(Arc::new(ResolvedRegistry::default()));
        let root = builder
            .discard(
                HandlerId::new(0),
                ResumeId::new(0),
                ResumeUse::Consumed,
                Type::Unit,
                EffectRow::empty(),
                origin,
            )
            .unwrap();
        let row = EffectRow::singleton(EffectInstance::new(
            EffectId::new(ModuleId::new(0), 0),
            Box::new([]),
        ));
        builder
            .recompute_effect_rows_in_range(0..1, &row, HandlerId::new(0), ResumeId::new(0))
            .unwrap();
        let node = &builder.nodes[root.index().unwrap()];
        assert_eq!(node.kind.child_count(), 0);
        assert_eq!(node.kind.child_at(0), None);
        assert_eq!(node.kind.child_at(usize::MAX), None);
        assert_eq!(
            EffectOperationFamily::operation_extra_edge_count(&node.kind),
            0
        );
        assert_eq!(node.ty, Type::Unit);
        assert!(node.effects.is_empty());
    }

    fn range_fixture(
        depth: usize,
    ) -> (
        EffectCoreBuilder,
        std::ops::Range<usize>,
        EffectRow,
        NodeId,
        NodeId,
    ) {
        let source = SourceFile::new("effect-range.ash", "()").expect("test source");
        let origin = Origin::Source(
            source
                .span(ByteRange::new(0, 2).expect("ordered range"))
                .expect("fixture span"),
        );
        let mut builder =
            EffectCoreBuilder::with_effect_registry(Arc::new(ResolvedRegistry::default()));
        let value = builder
            .integer(
                Integer::parse_decimal("0").expect("integer literal"),
                Type::Int,
                origin.clone(),
            )
            .expect("resume value");
        let start = builder.node_checkpoint();
        let resume = builder
            .resume(
                HandlerId::new(0),
                ResumeId::new(0),
                ResumeUse::Consumed,
                value,
                Type::Int,
                EffectRow::empty(),
                origin.clone(),
            )
            .expect("resume node");
        let mut root = resume;
        for _ in 0..depth {
            root = builder
                .primitive(Primitive::Add, value, root, Type::Int, origin.clone())
                .expect("range wrapper");
        }
        let effect = EffectInstance::new(EffectId::new(ModuleId::new(0), 0), Box::new([]));
        let clauses = (0..2)
            .map(|ordinal| {
                EffectClause::new(
                    OperationId::new(effect.effect(), ordinal),
                    ResumeId::new(ordinal + 1),
                    CoreMatchArm::new(
                        CorePattern::new(
                            Type::Int,
                            origin.clone(),
                            crate::core::CorePatternKind::Wildcard,
                        ),
                        value,
                        origin.clone(),
                    ),
                )
            })
            .collect();
        root = builder
            .handler(
                HandlerId::new(1),
                root,
                effect.clone(),
                clauses,
                Type::Int,
                EffectRow::empty(),
                origin,
            )
            .expect("nested multi-clause handler");
        (
            builder,
            start..root.index().expect("local root") + 1,
            EffectRow::singleton(effect),
            root,
            resume,
        )
    }

    fn recompute(
        builder: &mut EffectCoreBuilder,
        range: std::ops::Range<usize>,
        output: &EffectRow,
    ) -> Result<(), super::super::BuildError> {
        builder.recompute_effect_rows_in_range(range, output, HandlerId::new(0), ResumeId::new(0))
    }

    #[test]
    fn nested_hook_recompute_owns_partial_target_clones() {
        const CHILD: &str = "ASH_HOOK_RECOMPUTE_STACK_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let status = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "core::effect::tests::nested_hook_recompute_owns_partial_target_clones",
                    "--nocapture",
                ])
                .env(CHILD, "1")
                .status()
                .unwrap();
            assert!(
                status.success(),
                "fresh hook recomputation process: {status}"
            );
            return;
        }
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let fixture = || {
                    let source =
                        SourceFile::new("nested-hook-range", "hook Mark<A, B> { 42 }").unwrap();
                    let span = source
                        .span(ByteRange::new(0, source.text().len() as u32).unwrap())
                        .unwrap();
                    let origin = Origin::Source(span);
                    let effect = EffectId::new(ModuleId::new(0), 0);
                    let target = || {
                        let mut argument = Type::Unit;
                        for _ in 0..32_000 {
                            argument = Type::Application(Box::new(argument), Box::new(Type::Unit));
                        }
                        EffectInstance::new(effect, Box::new([argument, Type::Unit]))
                    };
                    let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(
                        ResolvedRegistry::default(),
                    ));
                    let value = builder
                        .integer(
                            Integer::parse_decimal("42").unwrap(),
                            Type::Int,
                            origin.clone(),
                        )
                        .unwrap();
                    let binder = builder.binder(Type::Int, origin.clone()).unwrap();
                    let input = binder.id();
                    let variable = builder.variable(input, Type::Int, origin.clone()).unwrap();
                    let identity = builder
                        .resume(
                            HandlerId::new(1),
                            ResumeId::new(1),
                            ResumeUse::Consumed,
                            variable,
                            Type::Int,
                            EffectRow::empty(),
                            origin.clone(),
                        )
                        .unwrap();
                    let start = builder.node_checkpoint();
                    let resume = builder
                        .resume(
                            HandlerId::new(0),
                            ResumeId::new(0),
                            ResumeUse::Consumed,
                            value,
                            Type::Int,
                            EffectRow::empty(),
                            origin.clone(),
                        )
                        .unwrap();
                    let root = builder
                        .handler_with_root(
                            HandlerId::new(1),
                            resume,
                            target(),
                            vec![EffectClause::new(
                                OperationId::new(effect, 0),
                                ResumeId::new(1),
                                CoreMatchArm::new(
                                    CorePattern::new(
                                        Type::Int,
                                        origin.clone(),
                                        crate::core::CorePatternKind::Binder(binder),
                                    ),
                                    identity,
                                    origin.clone(),
                                ),
                            )],
                            Type::Int,
                            EffectRow::empty(),
                            origin,
                            Some(crate::resolved::HookRootContract {
                                target: target(),
                                span,
                                target_span: span,
                                operation: OperationId::new(effect, 0),
                                input,
                                resume: ResumeId::new(1),
                            }),
                        )
                        .unwrap();
                    let output = EffectRow::singleton(EffectInstance::new(
                        EffectId::new(ModuleId::new(0), 1),
                        Box::new([]),
                    ));
                    (
                        builder,
                        start..root.index().unwrap() + 1,
                        output,
                        root,
                        resume,
                    )
                };
                let (mut prefix, range, output, root, _) = fixture();
                let before = prefix.type_work.used();
                recompute(&mut prefix, range.start..root.index().unwrap(), &output).unwrap();
                let prefix_work = prefix.type_work.used() - before;
                let EffectExprKind::Operation(EffectOperation::Handler(handler)) =
                    &prefix.nodes[root.index().unwrap()].kind
                else {
                    unreachable!()
                };
                let mut clone_work = TypeWorkBudget::unbounded();
                drop(crate::types::IterativeArgumentOwner::new(
                    crate::types::clone_kinded_argument_with_budget(
                        &handler.effect.arguments()[0],
                        &mut clone_work,
                    )
                    .unwrap(),
                ));
                // One extra range slot, the hook node, two argument slots, and the
                // complete first clone. The second argument has no work remaining.
                let after_first_clone = prefix_work + 1 + 1 + 2 + clone_work.used();
                drop(prefix);
                let (mut short, range, output, _, _) = fixture();
                let retained = short
                    .nodes
                    .iter()
                    .map(|node| node.effects.clone())
                    .collect::<Vec<_>>();
                short
                    .charge_type_work_for_test(
                        TYPE_WORK_LIMIT - short.type_work.used() - after_first_clone,
                    )
                    .unwrap();
                assert_eq!(
                    recompute(&mut short, range, &output),
                    Err(super::super::BuildError::TypeWorkExceeded)
                );
                assert_eq!(
                    short
                        .nodes
                        .iter()
                        .map(|node| node.effects.clone())
                        .collect::<Vec<_>>(),
                    retained
                );
                drop(short);
                let (mut measured, range, output, root, resume) = fixture();
                let before = measured.type_work.used();
                recompute(&mut measured, range, &output).unwrap();
                let exact = measured.type_work.used() - before;
                assert_eq!(measured.nodes[root.index().unwrap()].effects, output);
                assert_eq!(measured.nodes[resume.index().unwrap()].effects, output);
                drop(measured);
                for allowance in [exact - 1, exact, exact] {
                    let (mut retry, range, output, root, resume) = fixture();
                    retry
                        .charge_type_work_for_test(
                            TYPE_WORK_LIMIT - retry.type_work.used() - allowance,
                        )
                        .unwrap();
                    let result = recompute(&mut retry, range, &output);
                    if allowance < exact {
                        assert_eq!(result, Err(super::super::BuildError::TypeWorkExceeded));
                        assert!(retry.nodes.iter().all(|node| node.effects.is_empty()));
                    } else {
                        result.unwrap();
                        assert_eq!(retry.type_work.used(), TYPE_WORK_LIMIT);
                        assert_eq!(retry.nodes[root.index().unwrap()].effects, output);
                        assert_eq!(retry.nodes[resume.index().unwrap()].effects, output);
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn range_recompute_is_exact_retryable_and_stack_safe() {
        const DEPTH: usize = 16;
        let (mut measured, range, output, root, resume) = range_fixture(DEPTH);
        let before = measured.type_work.used();
        recompute(&mut measured, range, &output).expect("measured range should fit");
        let work = measured.type_work.used() - before;
        assert_eq!(measured.nodes[resume.index().unwrap()].effects, output);
        assert_eq!(
            measured.nodes[root.index().unwrap()].effects,
            EffectRow::empty()
        );

        let (mut short, range, output, _, _) = range_fixture(DEPTH);
        let retained = short
            .nodes
            .iter()
            .map(|node| node.effects.clone())
            .collect::<Vec<_>>();
        short
            .charge_type_work_for_test(TYPE_WORK_LIMIT - short.type_work.used() - (work - 1))
            .expect("one-short prefix");
        assert_eq!(
            recompute(&mut short, range, &output),
            Err(super::super::BuildError::TypeWorkExceeded),
        );
        assert_eq!(
            short
                .nodes
                .iter()
                .map(|node| node.effects.clone())
                .collect::<Vec<_>>(),
            retained,
        );

        for _ in 0..2 {
            let (mut retry, range, output, _, _) = range_fixture(DEPTH);
            retry
                .charge_type_work_for_test(TYPE_WORK_LIMIT - retry.type_work.used() - work)
                .expect("exact prefix");
            recompute(&mut retry, range, &output).expect("fresh exact retry");
        }

        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let (mut deep, range, output, _, _) = range_fixture(4_096);
                recompute(&mut deep, range, &output).expect("deep range remains iterative");
            })
            .expect("small-stack worker")
            .join()
            .expect("range teardown remains stack-safe");
    }

    #[test]
    fn completed_cleanup_rows_propagate_nested_resumes_with_exact_atomic_retry() {
        fn fixture() -> (EffectCoreBuilder, NodeId, NodeId, EffectRow) {
            let source = SourceFile::new("nested-row-replay", "()").unwrap();
            let origin = Origin::Source(source.span(ByteRange::new(0, 2).unwrap()).unwrap());
            let mut builder =
                EffectCoreBuilder::with_effect_registry(Arc::new(ResolvedRegistry::default()));
            let unit = builder.unit(Type::Unit, origin.clone()).unwrap();
            let effects = (0..3)
                .map(|id| EffectInstance::new(EffectId::new(ModuleId::new(0), id), Box::new([])))
                .collect::<Vec<_>>();
            let mut request = |index: usize| {
                builder
                    .request(
                        effects[index].clone(),
                        OperationId::new(effects[index].effect(), 0),
                        unit,
                        Type::Unit,
                        EffectRow::singleton(effects[index].clone()),
                        origin.clone(),
                    )
                    .unwrap()
            };
            let first = request(0);
            let outward = request(2);
            let nested = request(1);
            let binder = builder.binder(Type::Unit, origin.clone()).unwrap();
            let body = builder
                .binding(binder, first, outward, Type::Unit, origin.clone())
                .unwrap();
            let outer_resume = builder
                .resume(
                    HandlerId::new(0),
                    ResumeId::new(0),
                    ResumeUse::Consumed,
                    unit,
                    Type::Unit,
                    EffectRow::empty(),
                    origin.clone(),
                )
                .unwrap();
            let binder = builder.binder(Type::Unit, origin.clone()).unwrap();
            let nested_body = builder
                .binding(binder, nested, outer_resume, Type::Unit, origin.clone())
                .unwrap();
            let inner_resume = builder
                .resume(
                    HandlerId::new(1),
                    ResumeId::new(1),
                    ResumeUse::Consumed,
                    unit,
                    Type::Unit,
                    EffectRow::empty(),
                    origin.clone(),
                )
                .unwrap();
            let clause = |index: usize, body| {
                EffectClause::new(
                    OperationId::new(effects[index].effect(), 0),
                    ResumeId::new(index as u32),
                    CoreMatchArm::new(
                        CorePattern::new(
                            Type::Unit,
                            origin.clone(),
                            crate::core::CorePatternKind::Wildcard,
                        ),
                        body,
                        origin.clone(),
                    ),
                )
            };
            let inner = builder
                .handler(
                    HandlerId::new(1),
                    nested_body,
                    effects[1].clone(),
                    vec![clause(1, inner_resume)],
                    Type::Unit,
                    EffectRow::empty(),
                    origin.clone(),
                )
                .unwrap();
            let row = EffectRow::singleton(effects[2].clone());
            builder
                .handler(
                    HandlerId::new(0),
                    body,
                    effects[0].clone(),
                    vec![clause(0, inner)],
                    Type::Unit,
                    row.clone(),
                    origin,
                )
                .unwrap();
            (builder, outer_resume, inner_resume, row)
        }
        let (mut measured, outer, inner, row) = fixture();
        let before = measured.type_work.used();
        measured.finish_cleanup_effect_rows().unwrap();
        let work = measured.type_work.used() - before;
        // The inner owner learns D only after outer resume's first refresh,
        // so reaching both equalities requires multiple full replay rounds.
        assert_eq!(measured.nodes[outer.index().unwrap()].effects, row);
        assert_eq!(measured.nodes[inner.index().unwrap()].effects, row);

        let (mut short, _, _, _) = fixture();
        let rows = short
            .nodes
            .iter()
            .map(|node| node.effects.clone())
            .collect::<Vec<_>>();
        short
            .charge_type_work_for_test(TYPE_WORK_LIMIT - short.type_work.used() - work + 1)
            .unwrap();
        assert_eq!(
            short.finish_cleanup_effect_rows(),
            Err(super::super::BuildError::TypeWorkExceeded)
        );
        assert_eq!(
            short
                .nodes
                .iter()
                .map(|node| node.effects.clone())
                .collect::<Vec<_>>(),
            rows
        );
        for _ in 0..2 {
            let (mut retry, outer, inner, row) = fixture();
            retry
                .charge_type_work_for_test(TYPE_WORK_LIMIT - retry.type_work.used() - work)
                .unwrap();
            retry.finish_cleanup_effect_rows().unwrap();
            assert_eq!(retry.nodes[outer.index().unwrap()].effects, row);
            assert_eq!(retry.nodes[inner.index().unwrap()].effects, row);
            assert_eq!(retry.type_work.used(), TYPE_WORK_LIMIT);
        }
        // After generic identities coincide, an old removed-label cache can
        // become a self-supporting but nonleast H = base union Resume(H).
        let (mut stale, outer, inner, row) = fixture();
        for id in [outer, inner] {
            stale.nodes[id.index().unwrap()].effects = EffectRow::singleton(EffectInstance::new(
                EffectId::new(ModuleId::new(0), 0),
                Box::new([]),
            ));
        }
        stale.finish_cleanup_effect_rows().unwrap();
        assert_eq!(stale.nodes[outer.index().unwrap()].effects, row);
        assert_eq!(stale.nodes[inner.index().unwrap()].effects, row);

        // The nested handler's member arrives only through the outer resume.
        let (mut delayed, outer, inner, row) = fixture();
        for node in &mut delayed.nodes {
            if let EffectExprKind::Operation(EffectOperation::Handler(handler)) = &mut node.kind
                && handler.id == HandlerId::new(1)
            {
                handler.body = outer;
                handler.effect = row.known()[0].clone();
            }
        }
        delayed.finish_cleanup_effect_rows().unwrap();
        assert_eq!(delayed.nodes[outer.index().unwrap()].effects, row);
        assert!(delayed.nodes[inner.index().unwrap()].effects.is_empty());

        // A genuinely absent member still fails the strict final sweep, with
        // every entry row restored despite preceding successful replay rounds.
        let (mut missing, _, _, _) = fixture();
        for node in &mut missing.nodes {
            if let EffectExprKind::Operation(EffectOperation::Handler(handler)) = &mut node.kind
                && handler.id == HandlerId::new(0)
            {
                handler.effect =
                    EffectInstance::new(EffectId::new(ModuleId::new(0), 9), Box::new([]));
            }
        }
        let rows = missing
            .nodes
            .iter()
            .map(|node| node.effects.clone())
            .collect::<Vec<_>>();
        assert_eq!(
            missing.finish_cleanup_effect_rows(),
            Err(super::super::BuildError::InvalidPayload)
        );
        assert_eq!(
            missing
                .nodes
                .iter()
                .map(|node| node.effects.clone())
                .collect::<Vec<_>>(),
            rows
        );
    }
}

#[cfg(test)]
mod rewrite_tests {
    use super::*;

    #[test]
    fn hook_target_retention_is_exact_retryable_and_disposes_deep_partial_clones() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    crate::source::SourceFile::new("hook-target", "hook Mark<Unit> {}").unwrap();
                let span = source
                    .span(crate::source::ByteRange::new(0, 18).unwrap())
                    .unwrap();
                let mut deep = Type::Unit;
                for _ in 0..32_000 {
                    deep = Type::Application(Box::new(Type::Unit), Box::new(deep));
                }
                let effect = crate::types::EffectId::new(crate::module::ModuleId::new(0), 0);
                let root = crate::resolved::HookRootContract {
                    target: EffectInstance::new(effect, Box::new([deep, Type::Unit])),
                    span,
                    target_span: span,
                    operation: crate::types::OperationId::new(effect, 0),
                    input: crate::resolved::BinderId::generated(0),
                    resume: crate::resolved::ResumeId::new(0),
                };
                let mut measured = TypeWorkBudget::unbounded();
                drop(root.clone_with_budget(&mut measured).unwrap());
                let exact = measured.used();
                for limit in [0, exact - 1, exact - 2, exact - 3] {
                    assert!(
                        root.clone_with_budget(&mut TypeWorkBudget::with_limit(limit))
                            .is_err()
                    );
                }
                for _ in 0..2 {
                    let mut retry = TypeWorkBudget::with_limit(exact);
                    drop(root.clone_with_budget(&mut retry).unwrap());
                    assert_eq!(retry.used(), exact);
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn operation_rewrite_is_exact_retryable_and_drops_partial_deep_arguments() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                use crate::{
                    module::ModuleId,
                    types::{EffectId, IterativeTypeOwner},
                };
                const DEPTH: usize = 32_000;
                let effect = EffectId::new(ModuleId::new(0), 0);
                let deep = || {
                    (0..DEPTH).fold(Type::Unit, |ty, _| {
                        Type::Application(Box::new(ty), Box::new(Type::Unit))
                    })
                };
                let node = NodeId::new(super::super::dialect::ArenaId::new(0), 0);
                let mut request =
                    EffectExprKind::Operation(EffectOperation::Request(RequestNode::new(
                        EffectInstance::new(effect, Box::new([deep(), Type::Unit])),
                        OperationId::new(effect, 0),
                        node,
                    )));
                let rewrite = |request: &mut EffectExprKind, limit| {
                    let work = std::cell::RefCell::new(TypeWorkBudget::with_limit(limit));
                    let result = EffectOperationFamily::rewrite_operation_type_metadata(
                        request,
                        &mut |ty| {
                            crate::types::clone_type_with_budget(ty, &mut *work.borrow_mut())
                                .map_err(|()| crate::core::BuildError::TypeWorkExceeded)
                        },
                        &mut |cells| {
                            work.borrow_mut()
                                .charge(cells)
                                .map_err(|()| crate::core::BuildError::TypeWorkExceeded)
                        },
                    );
                    (result, work.into_inner().used())
                };
                // Two argument vectors plus the deep Type and final Unit.
                let required = 2 * DEPTH + 6;
                assert_eq!(
                    rewrite(&mut request, required - 1).0,
                    Err(crate::core::BuildError::TypeWorkExceeded)
                );
                for _ in 0..2 {
                    assert_eq!(rewrite(&mut request, required), (Ok(()), required));
                }
                let EffectExprKind::Operation(EffectOperation::Request(request)) = request else {
                    unreachable!()
                };
                assert_eq!(request.effect().effect(), effect);
                assert_eq!(request.operation(), OperationId::new(effect, 0));
                assert_eq!(request.operand(), node);
                let expected = IterativeTypeOwner::new(deep());
                assert!(matches!(&request.effect().arguments()[0], crate::types::KindedArgument::TypeArg(actual)
                    if crate::types::same_type(&expected, actual)));
                drop(request);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

/// Copies only actual arguments; checked ABI/source preparation stays shared.
pub(crate) fn copy_native_interpretations_with_budget(
    source: &[NativeInterpretation],
    work: &mut TypeWorkBudget,
) -> Result<Box<[NativeInterpretation]>, super::BuildError> {
    work.charge(source.len())
        .map_err(|()| super::BuildError::TypeWorkExceeded)?;
    let mut result = Vec::new();
    result
        .try_reserve_exact(source.len())
        .map_err(|_| super::BuildError::TypeWorkExceeded)?;
    for interpretation in source {
        let effect = clone_effect_instance_with_budget(&interpretation.effect, work)?;
        result.push(NativeInterpretation::new(
            effect,
            Arc::clone(&interpretation.symbol),
        ));
    }
    Ok(result.into_boxed_slice())
}

/// Exact set subtraction never masks another actual vector of the same API.
pub(crate) fn native_interpret_outward_row(
    body: &EffectRow,
    interpretations: &[NativeInterpretation],
    work: &mut TypeWorkBudget,
) -> Result<EffectRow, super::BuildError> {
    work.charge(interpretations.len())
        .map_err(|()| super::BuildError::TypeWorkExceeded)?;
    let mut row = clone_effect_row_with_budget(body, work)
        .map_err(|()| super::BuildError::TypeWorkExceeded)?;
    for interpretation in interpretations {
        match row
            .remove_exact_with_budget(&interpretation.effect, work)
            .map_err(|()| super::BuildError::TypeWorkExceeded)?
        {
            Ok(remaining) => row = remaining,
            Err(crate::types::EffectRowError::Missing) => {}
            Err(_) => return Err(super::BuildError::InvalidPayload),
        }
    }
    Ok(row)
}

/// Entry preparation distinguishes a residual source requirement from refusal
/// while representing checked metadata. Neither variant grants execution.
pub(crate) enum NativeEntryBuildFailure {
    ResidualEffects,
    Build(super::BuildError),
}

/// Classifies already checked entry metadata without cloning ABI or actuals.
/// The original source registry still receives independent final validation.
pub(crate) fn owner_free_native_entry_row<'registry>(
    registry_for: impl Fn(crate::types::EffectId) -> Option<&'registry ResolvedRegistry>,
    row: &EffectRow,
    work: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    if row.is_empty() {
        return Ok(true);
    }
    work.charge(1)?;
    if row.tail().is_some() {
        return Ok(false);
    }
    work.charge(row.known().len())?;
    for instance in row.known() {
        work.charge(3)?;
        let Some(registry) = registry_for(instance.effect()) else {
            return Ok(false);
        };
        let operation = OperationId::new(instance.effect(), 0);
        let Some(symbol) = registry.native_symbol(operation) else {
            return Ok(false);
        };
        let Some(declaration) = registry.effect(instance.effect()) else {
            return Ok(false);
        };
        if symbol.effect() != instance.effect()
            || symbol.operation() != operation
            || !declaration
                .native_contract
                .as_ref()
                .is_some_and(|original| Arc::ptr_eq(original, symbol))
        {
            return Ok(false);
        }
    }
    Ok(true)
}

impl CoreBuilder<EffectOperationFamily> {
    /// Wraps only the authorized finalizer's already zonked entry body.
    /// The caller retains the phase meter; unchecked Core remains unchecked.
    pub(crate) fn prepare_owner_free_native_entry(
        &mut self,
        body: NodeId,
        origin: crate::source::Span,
        work: &mut TypeWorkBudget,
    ) -> Result<NodeId, NativeEntryBuildFailure> {
        use NativeEntryBuildFailure::{Build, ResidualEffects};
        work.charge(1)
            .map_err(|()| Build(super::BuildError::TypeWorkExceeded))?;
        let index = body.index().map_err(Build)?;
        self.node_at_ordinal(body, index).map_err(Build)?;
        let stored = self
            .nodes
            .get(index)
            .ok_or(Build(super::BuildError::InvalidNodeId))?;
        if stored.effects.is_empty() {
            return Ok(body);
        }
        if !owner_free_native_entry_row(|_| Some(self.registry()), &stored.effects, work)
            .map_err(|()| Build(super::BuildError::TypeWorkExceeded))?
        {
            return Err(ResidualEffects);
        }
        work.charge(stored.effects.known().len())
            .map_err(|()| Build(super::BuildError::TypeWorkExceeded))?;
        let mut interpretations = Vec::new();
        interpretations
            .try_reserve_exact(stored.effects.known().len())
            .map_err(|_| Build(super::BuildError::TypeWorkExceeded))?;
        for instance in stored.effects.known() {
            work.charge(1)
                .map_err(|()| Build(super::BuildError::TypeWorkExceeded))?;
            let symbol = self
                .registry()
                .native_symbol(OperationId::new(instance.effect(), 0))
                .ok_or(Build(super::BuildError::InvalidPayload))?;
            interpretations.push(NativeInterpretation::new(
                clone_effect_instance_with_budget(instance, work).map_err(Build)?,
                Arc::clone(symbol),
            ));
        }
        let ty = crate::types::IterativeTypeOwner::new(
            crate::types::clone_type_with_budget(&stored.ty, work)
                .map_err(|()| Build(super::BuildError::TypeWorkExceeded))?,
        );
        // Every known member was retained and the source row was closed.
        // Independent Core validation reconstructs this exact subtraction.
        self.with_caller_type_work(work, |builder| {
            builder.native_interpret(
                body,
                interpretations.into_boxed_slice(),
                ty.into_inner(),
                EffectRow::empty(),
                Origin::Source(origin),
            )
        })
        .map_err(Build)
    }
}
