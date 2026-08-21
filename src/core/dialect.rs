//! Closed assembly of the named pure Mini-Ash Core dialect.

use std::{
    collections::HashSet,
    error::Error,
    fmt,
    sync::{
        Arc,
        atomic::{AtomicU32, Ordering},
    },
};

use super::{
    binding::BindingNode,
    function::{ApplicationNode, FunctionNode},
    literal::{BooleanNode, IntegerNode, UnitNode},
    primitive::{Primitive, PrimitiveNode},
    variable::{TypedBinder, VariableNode},
};
use crate::{
    integer::Integer,
    resolved::BinderId,
    source::{GeneratedReason, Origin, Span},
    types::Type,
};

/// Names the closed pure Core dialect selected by Mini-Ash.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MiniAshPureDialect;

impl MiniAshPureDialect {
    /// Stable compiler-facing name of the selected Core dialect.
    pub const NAME: &'static str = "mini-ash.pure";
}

/// Maximum recursive Type or Origin wrappers admitted into Core storage.
///
/// This is replaceable compiler resource behavior aligned with the current
/// parser structural budget. It is not an Ash language-semantic limit.
pub const CORE_PAYLOAD_DEPTH_LIMIT: usize = 128;

/// Identifies a node inside one Core arena.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NodeId {
    arena: ArenaId,
    index: u32,
}

impl NodeId {
    pub(super) const fn new(arena: ArenaId, index: u32) -> Self {
        Self { arena, index }
    }

    /// Returns the arena-local numeric handle.
    #[must_use]
    pub const fn value(self) -> u32 {
        self.index
    }

    pub(super) const fn arena(self) -> ArenaId {
        self.arena
    }

    pub(super) fn index(self) -> Result<usize, BuildError> {
        usize::try_from(self.index).map_err(|_| BuildError::InvalidNodeId)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct ArenaId(u32);

impl ArenaId {
    #[cfg(test)]
    pub(super) const fn new(value: u32) -> Self {
        Self(value)
    }
}

static ARENA_IDS: ArenaIdAllocator = ArenaIdAllocator::with_next(0);

struct ArenaIdAllocator {
    next: AtomicU32,
}

impl ArenaIdAllocator {
    const fn with_next(next: u32) -> Self {
        Self {
            next: AtomicU32::new(next),
        }
    }

    fn allocate(&self) -> Result<ArenaId, BuildError> {
        self.next
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, checked_add_one)
            .map(ArenaId)
            .map_err(|_| BuildError::ArenaIdExhausted)
    }
}

const fn checked_add_one(value: u32) -> Option<u32> {
    value.checked_add(1)
}

/// A typed expression in the pure Mini-Ash dialect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypedExpr {
    /// The structural result type.
    pub ty: Type,
    /// Causal source provenance.
    pub origin: Origin,
    /// The selected pure feature payload.
    pub kind: PureExprKind,
}

/// The closed expression families in the pure Mini-Ash dialect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PureExprKind {
    /// A value node.
    Value(PureValue),
    /// A resolved variable occurrence.
    Variable(VariableNode),
    /// A strict pure computation.
    Computation(PureComputation),
}

/// The closed value families in the pure Mini-Ash dialect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PureValue {
    /// An arbitrary-precision integer.
    Integer(IntegerNode),
    /// A Boolean value.
    Boolean(BooleanNode),
    /// The unit value.
    Unit(UnitNode),
    /// A unary function value.
    Function(FunctionNode),
}

/// The closed computation families in the pure Mini-Ash dialect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PureComputation {
    /// A sequential nonrecursive binding.
    Bind(BindingNode),
    /// A strict unary application.
    Apply(ApplicationNode),
    /// A primitive operation.
    Primitive(PrimitiveNode),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DialectId(&'static str);

impl DialectId {
    pub(super) const PURE: Self = Self(MiniAshPureDialect::NAME);

    #[cfg(test)]
    pub(super) const FOREIGN: Self = Self("test.foreign");
}

#[derive(Debug)]
pub(super) struct StoredNode {
    pub(super) dialect: DialectId,
    pub(super) ty: Type,
    pub(super) origin: Option<Origin>,
    pub(super) kind: PureExprKind,
}

/// An unchecked Core arena which must cross [`super::validate()`] before use.
#[derive(Debug)]
pub struct UnvalidatedProgram {
    pub(super) arena: ArenaId,
    pub(super) nodes: Vec<StoredNode>,
    pub(super) root: NodeId,
}

/// A pure Core arena whose graph, types, scope, dialect, and provenance hold.
#[derive(Debug)]
pub struct PureProgram {
    arena: ArenaId,
    nodes: Box<[TypedExpr]>,
    root: NodeId,
}

impl PureProgram {
    pub(super) fn new(arena: ArenaId, nodes: Vec<TypedExpr>, root: NodeId) -> Self {
        Self {
            arena,
            nodes: nodes.into_boxed_slice(),
            root,
        }
    }

    /// Returns the root expression.
    #[must_use]
    pub const fn root(&self) -> NodeId {
        self.root
    }

    /// Returns a node when the arena-local handle belongs to this program.
    #[must_use]
    pub fn node(&self, id: NodeId) -> Option<&TypedExpr> {
        if id.arena() != self.arena {
            return None;
        }
        usize::try_from(id.value())
            .ok()
            .and_then(|index| self.nodes.get(index))
    }

    /// Returns the number of validated nodes.
    #[must_use]
    pub const fn node_count(&self) -> usize {
        self.nodes.len()
    }
}

/// The capability required by all later Core consumers.
#[derive(Debug)]
pub struct ValidatedProgram(Arc<PureProgram>);

impl ValidatedProgram {
    pub(super) fn new(program: PureProgram) -> Self {
        Self(Arc::new(program))
    }

    #[allow(dead_code, reason = "reserved for the validated evaluator boundary")]
    pub(crate) fn shared(&self) -> Arc<PureProgram> {
        Arc::clone(&self.0)
    }

    /// Returns the validated root expression.
    #[must_use]
    pub fn root(&self) -> NodeId {
        self.0.root()
    }

    /// Returns a validated node when the handle belongs to this program.
    #[must_use]
    pub fn node(&self, id: NodeId) -> Option<&TypedExpr> {
        self.0.node(id)
    }

    /// Returns the number of validated nodes.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.0.node_count()
    }
}

/// Why unchecked Core construction could not be represented.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuildError {
    /// The process cannot assign another distinct Core arena identity.
    ArenaIdExhausted,
    /// The arena cannot assign another `u32` node handle.
    NodeIdExhausted,
    /// The builder cannot assign another resolver-compatible binder identity.
    BinderIdExhausted,
    /// A resolver identity occurs more than once in namespace reservations.
    DuplicateBinderReservation,
    /// Resolver namespace reservation was attempted after binder work began.
    BinderReservationPhaseStarted,
    /// A resolver identity was materialized without an upfront reservation.
    UnreservedResolvedBinder,
    /// A reserved resolver identity was materialized more than once.
    DuplicateResolvedBinder,
    /// A binder capability belongs to another Core arena.
    ForeignBinder,
    /// A Type contains more recursive wrappers than Core currently admits.
    TypeDepthExceeded,
    /// An Origin contains more recursive wrappers than Core currently admits.
    OriginDepthExceeded,
    /// Iterative payload rebuilding found inconsistent internal state.
    InvalidPayload,
    /// The requested root does not belong to this arena.
    InvalidNodeId,
}

impl fmt::Display for BuildError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::ArenaIdExhausted => "core arena identity space is exhausted",
            Self::NodeIdExhausted => "core node identity space is exhausted",
            Self::BinderIdExhausted => "core binder identity space is exhausted",
            Self::DuplicateBinderReservation => {
                "core resolved binder namespace contains a duplicate identity"
            }
            Self::BinderReservationPhaseStarted => {
                "core resolved binder namespace must be reserved before binder construction"
            }
            Self::UnreservedResolvedBinder => {
                "core resolved binder identity was not reserved upfront"
            }
            Self::DuplicateResolvedBinder => {
                "core resolved binder identity was already materialized"
            }
            Self::ForeignBinder => "core binder capability belongs to another arena",
            Self::TypeDepthExceeded => "core type structural depth is exceeded",
            Self::OriginDepthExceeded => "core origin structural depth is exceeded",
            Self::InvalidPayload => "core payload admission state is inconsistent",
            Self::InvalidNodeId => "core node identity does not belong to the arena",
        })
    }
}

impl Error for BuildError {}

/// Builds an unchecked pure Core arena with checked identity allocation.
#[derive(Debug, Default)]
#[must_use]
pub struct CoreBuilder {
    arena: Option<ArenaId>,
    nodes: Vec<StoredNode>,
    next_binder: u32,
    reserved_resolved: HashSet<BinderId>,
    materialized_resolved: HashSet<BinderId>,
    generated_binders: HashSet<BinderId>,
    binder_phase_started: bool,
}

impl CoreBuilder {
    /// Starts an empty Core arena.
    pub fn new() -> Self {
        Self {
            arena: None,
            nodes: Vec::new(),
            next_binder: 0,
            reserved_resolved: HashSet::new(),
            materialized_resolved: HashSet::new(),
            generated_binders: HashSet::new(),
            binder_phase_started: false,
        }
    }

    /// Reserves the complete resolver-assigned binder namespace.
    ///
    /// Callers may make multiple reservations before binder construction
    /// starts, but every identity must be globally unique across those calls.
    /// The reservation is transactional: an error leaves the namespace
    /// unchanged.
    ///
    /// # Errors
    ///
    /// Returns [`BuildError::DuplicateBinderReservation`] when an identity is
    /// duplicated within this input or was reserved by an earlier call.
    /// Returns [`BuildError::BinderReservationPhaseStarted`] once any binder
    /// allocation or resolved-binder materialization has started.
    pub fn reserve_resolved_binders<I>(&mut self, ids: I) -> Result<(), BuildError>
    where
        I: IntoIterator<Item = BinderId>,
    {
        if self.binder_phase_started {
            return Err(BuildError::BinderReservationPhaseStarted);
        }
        let mut pending = HashSet::new();
        for id in ids {
            if self.reserved_resolved.contains(&id) || !pending.insert(id) {
                return Err(BuildError::DuplicateBinderReservation);
            }
        }
        self.reserved_resolved.extend(pending);
        Ok(())
    }

    /// Creates a fresh typed binder for a definition payload.
    ///
    /// # Errors
    ///
    /// Returns a payload resource failure before allocating any builder state.
    /// Returns [`BuildError::BinderIdExhausted`] when no identity remains, or
    /// [`BuildError::ArenaIdExhausted`] without consuming the computed binder
    /// identity when no arena identity remains.
    pub fn binder(&mut self, ty: Type, origin: Origin) -> Result<TypedBinder, BuildError> {
        let (ty, origin) = admit_payloads(ty, origin)?;
        let (id, next) = self.next_binder_candidate()?;
        let arena = self.ensure_arena()?;
        if !self.generated_binders.insert(id) {
            return Err(BuildError::InvalidPayload);
        }
        self.next_binder = next;
        self.binder_phase_started = true;
        Ok(TypedBinder::new(arena, id, ty, origin))
    }

    /// Materializes an upfront-reserved resolver identity in a typed binder.
    ///
    /// # Errors
    ///
    /// Returns a payload resource failure without allocating an arena or
    /// materializing the identity. Returns [`BuildError::ArenaIdExhausted`]
    /// without materializing the identity when no arena identity remains.
    /// Returns [`BuildError::UnreservedResolvedBinder`] when `id` was not in
    /// the upfront namespace, or [`BuildError::DuplicateResolvedBinder`] when
    /// that reserved identity was already materialized.
    pub fn resolved_binder(
        &mut self,
        id: BinderId,
        ty: Type,
        origin: Origin,
    ) -> Result<TypedBinder, BuildError> {
        let (ty, origin) = admit_payloads(ty, origin)?;
        if !self.reserved_resolved.contains(&id) {
            return Err(BuildError::UnreservedResolvedBinder);
        }
        if self.materialized_resolved.contains(&id) {
            return Err(BuildError::DuplicateResolvedBinder);
        }
        let arena = self.ensure_arena()?;
        self.materialized_resolved.insert(id);
        self.binder_phase_started = true;
        Ok(TypedBinder::new(arena, id, ty, origin))
    }

    /// Adds an integer payload with an unchecked result annotation.
    pub fn integer(
        &mut self,
        value: Integer,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        self.push(
            ty,
            origin,
            PureExprKind::Value(PureValue::Integer(IntegerNode::new(value))),
        )
    }

    /// Adds a Boolean payload with an unchecked result annotation.
    pub fn boolean(&mut self, value: bool, ty: Type, origin: Origin) -> Result<NodeId, BuildError> {
        self.push(
            ty,
            origin,
            PureExprKind::Value(PureValue::Boolean(BooleanNode::new(value))),
        )
    }

    /// Adds a unit payload with an unchecked result annotation.
    pub fn unit(&mut self, ty: Type, origin: Origin) -> Result<NodeId, BuildError> {
        self.push(ty, origin, PureExprKind::Value(PureValue::Unit(UnitNode)))
    }

    /// Adds a variable occurrence with an unchecked result annotation.
    pub fn variable(
        &mut self,
        binder: BinderId,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        self.push(
            ty,
            origin,
            PureExprKind::Variable(VariableNode::new(binder)),
        )
    }

    /// Adds a unary function value with an unchecked result annotation.
    ///
    /// Payload admission precedes the binder-capability check, so rejected
    /// recursive payloads are dismantled within Core's resource boundary.
    ///
    /// # Errors
    ///
    /// Returns [`BuildError::ForeignBinder`] when `parameter` was produced by
    /// another Core builder, after reporting any payload resource failure.
    pub fn function(
        &mut self,
        parameter: TypedBinder,
        body: NodeId,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        let (ty, origin) = admit_payloads(ty, origin)?;
        if self.arena != Some(parameter.arena()) {
            return Err(BuildError::ForeignBinder);
        }
        self.push_admitted(
            ty,
            origin,
            PureExprKind::Value(PureValue::Function(FunctionNode::new(parameter, body))),
        )
    }

    /// Adds a sequential binding with an unchecked result annotation.
    ///
    /// Payload admission precedes the binder-capability check, so rejected
    /// recursive payloads are dismantled within Core's resource boundary.
    ///
    /// # Errors
    ///
    /// Returns [`BuildError::ForeignBinder`] when `binder` was produced by
    /// another Core builder, after reporting any payload resource failure.
    pub fn binding(
        &mut self,
        binder: TypedBinder,
        initializer: NodeId,
        body: NodeId,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        let (ty, origin) = admit_payloads(ty, origin)?;
        if self.arena != Some(binder.arena()) {
            return Err(BuildError::ForeignBinder);
        }
        self.push_admitted(
            ty,
            origin,
            PureExprKind::Computation(PureComputation::Bind(BindingNode::new(
                binder,
                initializer,
                body,
            ))),
        )
    }

    /// Adds a strict unary application with an unchecked result annotation.
    pub fn application(
        &mut self,
        function: NodeId,
        argument: NodeId,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        self.push(
            ty,
            origin,
            PureExprKind::Computation(PureComputation::Apply(ApplicationNode::new(
                function, argument,
            ))),
        )
    }

    /// Adds a primitive operation with an unchecked result annotation.
    pub fn primitive(
        &mut self,
        primitive: Primitive,
        left: NodeId,
        right: NodeId,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        self.push(
            ty,
            origin,
            PureExprKind::Computation(PureComputation::Primitive(PrimitiveNode::new(
                primitive, left, right,
            ))),
        )
    }

    /// Finishes unchecked construction at `root`.
    ///
    /// # Errors
    ///
    /// Returns [`BuildError::InvalidNodeId`] unless `root` belongs to this arena.
    pub fn finish(self, root: NodeId) -> Result<UnvalidatedProgram, BuildError> {
        let Some(arena) = self.arena else {
            return Err(BuildError::InvalidNodeId);
        };
        if root.arena() != arena {
            return Err(BuildError::InvalidNodeId);
        }
        let index = root.index()?;
        if index >= self.nodes.len() {
            return Err(BuildError::InvalidNodeId);
        }
        Ok(UnvalidatedProgram {
            arena,
            nodes: self.nodes,
            root,
        })
    }

    fn push(&mut self, ty: Type, origin: Origin, kind: PureExprKind) -> Result<NodeId, BuildError> {
        let (ty, origin) = admit_payloads(ty, origin)?;
        self.push_admitted(ty, origin, kind)
    }

    fn push_admitted(
        &mut self,
        ty: Type,
        origin: Origin,
        kind: PureExprKind,
    ) -> Result<NodeId, BuildError> {
        let index = u32::try_from(self.nodes.len()).map_err(|_| BuildError::NodeIdExhausted)?;
        let arena = self.ensure_arena()?;
        self.nodes.push(StoredNode {
            dialect: DialectId::PURE,
            ty,
            origin: Some(origin),
            kind,
        });
        Ok(NodeId::new(arena, index))
    }

    fn ensure_arena(&mut self) -> Result<ArenaId, BuildError> {
        if let Some(arena) = self.arena {
            return Ok(arena);
        }
        let arena = ARENA_IDS.allocate()?;
        self.arena = Some(arena);
        Ok(arena)
    }

    fn next_binder_candidate(&self) -> Result<(BinderId, u32), BuildError> {
        let mut candidate = self.next_binder;
        loop {
            let id = BinderId::new(candidate);
            let next = candidate
                .checked_add(1)
                .ok_or(BuildError::BinderIdExhausted)?;
            if !self.reserved_resolved.contains(&id) && !self.generated_binders.contains(&id) {
                return Ok((id, next));
            }
            candidate = next;
        }
    }
}

fn admit_payloads(ty: Type, origin: Origin) -> Result<(Type, Origin), BuildError> {
    let admitted_type = admit_type(ty);
    let admitted_origin = admit_origin(origin);
    match (admitted_type, admitted_origin) {
        (Ok(ty), Ok(origin)) => Ok((ty, origin)),
        (Err(error), Ok(_)) | (Err(error), Err(_)) => Err(error),
        (Ok(_), Err(error)) => Err(error),
    }
}

enum TypeAdmissionTask {
    Visit(Type, usize),
    FinishFunction,
}

enum TypeToken {
    Int,
    Bool,
    Unit,
    Function,
}

fn admit_type(ty: Type) -> Result<Type, BuildError> {
    let mut work = vec![TypeAdmissionTask::Visit(ty, 0)];
    let mut tokens = Vec::new();
    let mut exceeded = false;
    while let Some(task) = work.pop() {
        match task {
            TypeAdmissionTask::Visit(Type::Int, _) => tokens.push(TypeToken::Int),
            TypeAdmissionTask::Visit(Type::Bool, _) => tokens.push(TypeToken::Bool),
            TypeAdmissionTask::Visit(Type::Unit, _) => tokens.push(TypeToken::Unit),
            TypeAdmissionTask::Visit(Type::Function(domain, codomain), depth) => {
                let child_depth = depth.saturating_add(1);
                exceeded |= child_depth > CORE_PAYLOAD_DEPTH_LIMIT;
                work.push(TypeAdmissionTask::FinishFunction);
                work.push(TypeAdmissionTask::Visit(*codomain, child_depth));
                work.push(TypeAdmissionTask::Visit(*domain, child_depth));
            }
            TypeAdmissionTask::FinishFunction => tokens.push(TypeToken::Function),
        }
    }
    if exceeded {
        return Err(BuildError::TypeDepthExceeded);
    }

    let mut rebuilt = Vec::new();
    for token in tokens {
        match token {
            TypeToken::Int => rebuilt.push(Type::Int),
            TypeToken::Bool => rebuilt.push(Type::Bool),
            TypeToken::Unit => rebuilt.push(Type::Unit),
            TypeToken::Function => {
                let Some(codomain) = rebuilt.pop() else {
                    return Err(BuildError::InvalidPayload);
                };
                let Some(domain) = rebuilt.pop() else {
                    return Err(BuildError::InvalidPayload);
                };
                rebuilt.push(Type::Function(Box::new(domain), Box::new(codomain)));
            }
        }
    }
    let Some(result) = rebuilt.pop() else {
        return Err(BuildError::InvalidPayload);
    };
    if !rebuilt.is_empty() {
        return Err(BuildError::InvalidPayload);
    }
    Ok(result)
}

enum OriginAdmissionTask {
    Visit(Origin, usize),
    FinishGenerated(GeneratedReason),
    FinishRelated(Vec<Span>),
}

enum OriginToken {
    Source(Span),
    Generated(GeneratedReason),
    Related(Vec<Span>),
}

fn admit_origin(origin: Origin) -> Result<Origin, BuildError> {
    let mut work = vec![OriginAdmissionTask::Visit(origin, 0)];
    let mut tokens = Vec::new();
    let mut exceeded = false;
    while let Some(task) = work.pop() {
        match task {
            OriginAdmissionTask::Visit(Origin::Source(span), _) => {
                tokens.push(OriginToken::Source(span));
            }
            OriginAdmissionTask::Visit(Origin::Generated { cause, reason }, depth) => {
                let child_depth = depth.saturating_add(1);
                exceeded |= child_depth > CORE_PAYLOAD_DEPTH_LIMIT;
                work.push(OriginAdmissionTask::FinishGenerated(reason));
                work.push(OriginAdmissionTask::Visit(*cause, child_depth));
            }
            OriginAdmissionTask::Visit(Origin::Related { primary, related }, depth) => {
                let child_depth = depth.saturating_add(1);
                exceeded |= child_depth > CORE_PAYLOAD_DEPTH_LIMIT;
                work.push(OriginAdmissionTask::FinishRelated(related));
                work.push(OriginAdmissionTask::Visit(*primary, child_depth));
            }
            OriginAdmissionTask::FinishGenerated(reason) => {
                tokens.push(OriginToken::Generated(reason));
            }
            OriginAdmissionTask::FinishRelated(related) => {
                tokens.push(OriginToken::Related(related));
            }
        }
    }
    if exceeded {
        return Err(BuildError::OriginDepthExceeded);
    }

    let mut rebuilt = Vec::new();
    for token in tokens {
        match token {
            OriginToken::Source(span) => rebuilt.push(Origin::Source(span)),
            OriginToken::Generated(reason) => {
                let Some(cause) = rebuilt.pop() else {
                    return Err(BuildError::InvalidPayload);
                };
                rebuilt.push(Origin::Generated {
                    cause: Box::new(cause),
                    reason,
                });
            }
            OriginToken::Related(related) => {
                let Some(primary) = rebuilt.pop() else {
                    return Err(BuildError::InvalidPayload);
                };
                rebuilt.push(Origin::Related {
                    primary: Box::new(primary),
                    related,
                });
            }
        }
    }
    let Some(result) = rebuilt.pop() else {
        return Err(BuildError::InvalidPayload);
    };
    if !rebuilt.is_empty() {
        return Err(BuildError::InvalidPayload);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::{ByteRange, GeneratedReason, SourceFile};

    #[test]
    fn arena_allocator_reserves_maximum_as_its_exhaustion_sentinel() {
        let allocator = ArenaIdAllocator::with_next(u32::MAX - 1);

        assert_eq!(allocator.allocate(), Ok(ArenaId::new(u32::MAX - 1)));
        assert_eq!(allocator.allocate(), Err(BuildError::ArenaIdExhausted));
    }

    fn function_type(depth: usize) -> Type {
        let mut ty = Type::Unit;
        for _ in 0..depth {
            ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
        }
        ty
    }

    fn generated_origin(source: &SourceFile, depth: usize) -> Origin {
        let range = ByteRange::new(0, 2).expect("ordered test range");
        let mut origin = Origin::Source(source.span(range).expect("test span"));
        for _ in 0..depth {
            origin = Origin::Generated {
                cause: Box::new(origin),
                reason: GeneratedReason::TypeChecking,
            };
        }
        origin
    }

    fn related_origin(source: &SourceFile, depth: usize) -> Origin {
        let range = ByteRange::new(0, 2).expect("ordered test range");
        let span = source.span(range).expect("test span");
        let mut origin = Origin::Source(span);
        for _ in 0..depth {
            origin = Origin::Related {
                primary: Box::new(origin),
                related: vec![span],
            };
        }
        origin
    }

    #[test]
    fn payload_limit_and_deep_rejection_are_stack_safe_and_transactional() {
        std::thread::Builder::new()
            .name("core-payload-boundary".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("payload.ash", "()").expect("test source");
                let shallow = generated_origin(&source, 0);

                let mut builder = CoreBuilder::new();
                assert_eq!(
                    builder.unit(function_type(CORE_PAYLOAD_DEPTH_LIMIT + 1), shallow.clone(),),
                    Err(BuildError::TypeDepthExceeded)
                );
                assert!(builder.arena.is_none());
                assert!(builder.nodes.is_empty());

                assert_eq!(
                    builder.unit(
                        Type::Unit,
                        generated_origin(&source, CORE_PAYLOAD_DEPTH_LIMIT + 1),
                    ),
                    Err(BuildError::OriginDepthExceeded)
                );
                assert_eq!(
                    builder.unit(
                        Type::Unit,
                        related_origin(&source, CORE_PAYLOAD_DEPTH_LIMIT + 1),
                    ),
                    Err(BuildError::OriginDepthExceeded)
                );

                assert_eq!(
                    builder.unit(function_type(50_000), shallow.clone(),),
                    Err(BuildError::TypeDepthExceeded)
                );
                assert!(builder.arena.is_none());
                assert!(builder.nodes.is_empty());

                assert_eq!(
                    builder.unit(Type::Unit, generated_origin(&source, 50_000)),
                    Err(BuildError::OriginDepthExceeded)
                );
                assert_eq!(
                    builder.unit(Type::Unit, related_origin(&source, 50_000)),
                    Err(BuildError::OriginDepthExceeded)
                );
                assert_eq!(
                    builder.unit(function_type(50_000), generated_origin(&source, 50_000),),
                    Err(BuildError::TypeDepthExceeded)
                );
                assert_eq!(
                    builder.binder(Type::Unit, generated_origin(&source, 50_000)),
                    Err(BuildError::OriginDepthExceeded)
                );
                assert!(builder.arena.is_none());
                assert!(builder.nodes.is_empty());
                assert_eq!(builder.next_binder, 0);
                assert!(builder.reserved_resolved.is_empty());
                assert!(builder.materialized_resolved.is_empty());
                assert!(builder.generated_binders.is_empty());
                assert!(!builder.binder_phase_started);
            })
            .expect("test thread should start")
            .join()
            .expect("payload admission should not overflow its small stack");
    }

    #[test]
    fn exact_payload_limit_validates_and_drops_on_a_small_stack() {
        std::thread::Builder::new()
            .name("core-payload-exact-limit".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("payload.ash", "()").expect("test source");
                let shallow = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();
                let mut root = builder
                    .unit(
                        Type::Unit,
                        generated_origin(&source, CORE_PAYLOAD_DEPTH_LIMIT),
                    )
                    .expect("exact origin depth is admitted");
                for depth in 1..=CORE_PAYLOAD_DEPTH_LIMIT {
                    let parameter = builder
                        .binder(Type::Unit, shallow.clone())
                        .expect("bounded binder");
                    root = builder
                        .function(parameter, root, function_type(depth), shallow.clone())
                        .expect("exact type depth is admitted");
                }
                let related = builder
                    .unit(
                        Type::Unit,
                        related_origin(&source, CORE_PAYLOAD_DEPTH_LIMIT),
                    )
                    .expect("exact related-origin depth is admitted");
                let binder = builder
                    .binder(Type::Unit, shallow.clone())
                    .expect("bounded binder");
                let root = builder
                    .binding(
                        binder,
                        related,
                        root,
                        function_type(CORE_PAYLOAD_DEPTH_LIMIT),
                        shallow,
                    )
                    .expect("exact result type depth is admitted");
                let program = builder.finish(root).expect("valid root");
                super::super::validate::validate(program, &[&source])
                    .expect("exact-limit Core validates");
            })
            .expect("test thread should start")
            .join()
            .expect("exact-limit Core should validate and drop on a small stack");
    }

    #[test]
    fn reserved_resolved_namespace_and_generated_identities_do_not_collide() {
        let source = SourceFile::new("binder.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let mut builder = CoreBuilder::new();
        builder
            .reserve_resolved_binders([BinderId::new(0), BinderId::new(1)])
            .expect("complete resolved namespace is reserved");
        assert_eq!(
            builder.resolved_binder(
                BinderId::new(0),
                function_type(CORE_PAYLOAD_DEPTH_LIMIT + 1),
                origin.clone(),
            ),
            Err(BuildError::TypeDepthExceeded)
        );
        let resolved = builder
            .resolved_binder(BinderId::new(0), Type::Unit, origin.clone())
            .expect("first resolved identity is admitted");
        let generated = builder
            .binder(Type::Unit, origin.clone())
            .expect("fresh generated identity");
        let second_resolved = builder
            .resolved_binder(BinderId::new(1), Type::Unit, origin.clone())
            .expect("later reserved identity remains materializable");

        assert_ne!(resolved.id(), generated.id());
        assert_ne!(second_resolved.id(), generated.id());
        assert_eq!(generated.id().value(), 2);
        assert_eq!(
            builder.resolved_binder(BinderId::new(0), Type::Unit, origin),
            Err(BuildError::DuplicateResolvedBinder)
        );
    }

    #[test]
    fn sparse_high_reservation_keeps_low_generated_ids_available() {
        let source = SourceFile::new("binder.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let mut builder = CoreBuilder::new();
        builder
            .reserve_resolved_binders([BinderId::new(u32::MAX - 1)])
            .expect("high resolved identity is reserved");

        let generated = builder
            .binder(Type::Unit, origin)
            .expect("low generated identity remains available");
        assert_eq!(generated.id().value(), 0);
    }

    #[test]
    fn reservation_is_transactional_and_closes_after_allocation_starts() {
        let source = SourceFile::new("binder.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let mut builder = CoreBuilder::new();
        builder
            .reserve_resolved_binders([BinderId::new(2)])
            .expect("first reservation");
        assert_eq!(
            builder.reserve_resolved_binders([BinderId::new(3), BinderId::new(3)]),
            Err(BuildError::DuplicateBinderReservation)
        );
        assert!(!builder.reserved_resolved.contains(&BinderId::new(3)));

        builder
            .binder(Type::Unit, origin)
            .expect("generated allocation starts the binder phase");
        assert_eq!(
            builder.reserve_resolved_binders([BinderId::new(4)]),
            Err(BuildError::BinderReservationPhaseStarted)
        );
        assert!(!builder.reserved_resolved.contains(&BinderId::new(4)));
    }

    #[test]
    fn resolved_materialization_requires_reservation_and_is_unique() {
        let source = SourceFile::new("binder.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let mut builder = CoreBuilder::new();
        assert_eq!(
            builder.resolved_binder(BinderId::new(0), Type::Unit, origin.clone()),
            Err(BuildError::UnreservedResolvedBinder)
        );
        builder
            .reserve_resolved_binders([BinderId::new(0)])
            .expect("resolved identity is reserved");
        builder
            .resolved_binder(BinderId::new(0), Type::Unit, origin.clone())
            .expect("first materialization");
        assert_eq!(
            builder.resolved_binder(BinderId::new(0), Type::Unit, origin),
            Err(BuildError::DuplicateResolvedBinder)
        );
    }

    #[test]
    fn binder_allocator_reserves_maximum_as_its_exhaustion_sentinel() {
        let source = SourceFile::new("binder.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let mut builder = CoreBuilder::new();
        builder.next_binder = u32::MAX - 1;

        let last = builder
            .binder(Type::Unit, origin.clone())
            .expect("last allocatable binder");
        assert_eq!(last.id().value(), u32::MAX - 1);
        assert_eq!(
            builder.binder(Type::Unit, origin),
            Err(BuildError::BinderIdExhausted)
        );
        assert!(!builder.generated_binders.contains(&BinderId::new(u32::MAX)));
    }

    #[test]
    fn failed_reserved_payload_admission_can_be_retried() {
        let source = SourceFile::new("binder.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let id = BinderId::new(7);
        let mut builder = CoreBuilder::new();
        builder
            .reserve_resolved_binders([id])
            .expect("resolved identity is reserved");
        assert_eq!(
            builder.resolved_binder(
                id,
                function_type(CORE_PAYLOAD_DEPTH_LIMIT + 1),
                origin.clone(),
            ),
            Err(BuildError::TypeDepthExceeded)
        );
        assert!(!builder.materialized_resolved.contains(&id));

        let binder = builder
            .resolved_binder(id, Type::Unit, origin)
            .expect("retry materializes the reserved identity");
        assert_eq!(binder.id(), id);
    }
}
