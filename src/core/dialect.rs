//! Closed assembly of the named pure Ash Core dialect.

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
    data::{ConstructorNode, CoreMatchArm, CorePattern, CorePatternKind, MatchNode, TupleNode},
    function::{ApplicationNode, FunctionNode},
    literal::{BooleanNode, IntegerNode, UnitNode},
    primitive::{Primitive, PrimitiveNode},
    recursion::{RecursiveBindingMember, RecursiveBindingNode},
    type_ops::{TypeAbstractionNode, TypeApplicationNode},
    variable::{TypedBinder, VariableNode},
};
use crate::{
    integer::Integer,
    resolved::{BinderId, ResolvedRegistry},
    source::{GeneratedReason, Origin, Span, discard_origin_iteratively},
    types::{Type, TypeWorkBudget, discard_type_iteratively, replace_type_iteratively},
};

/// Names the closed pure Core dialect selected by Ash.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AshPureDialect;

impl AshPureDialect {
    /// Stable compiler-facing name of the selected Core dialect.
    pub const NAME: &'static str = "ash.pure";
}

/// Maximum recursive Type or Origin wrappers admitted into Core storage.
///
/// This is replaceable compiler resource behavior aligned with the current
/// parser structural budget plus the two wrappers that retained lowering may
/// synthesize for tuple domains and constructor/function values. It is not an
/// Ash language-semantic limit.
pub const CORE_PAYLOAD_DEPTH_LIMIT: usize = 130;

/// Maximum structured-pattern wrappers admitted into one Core pattern.
pub const CORE_PATTERN_DEPTH_LIMIT: usize = 33;

pub(super) fn origin_depth_within_limit(root: &Origin) -> bool {
    let mut current = root;
    for _ in 0..=CORE_PAYLOAD_DEPTH_LIMIT {
        match current {
            Origin::Source(_) => return true,
            Origin::Generated { cause, .. } => current = cause,
            Origin::Related { primary, .. } => current = primary,
        }
    }
    false
}

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

/// A typed expression in the pure Ash dialect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypedExpr {
    /// The structural result type.
    pub ty: Type,
    /// Causal source provenance.
    pub origin: Origin,
    /// The selected pure feature payload.
    pub kind: PureExprKind,
}

impl TypedExpr {
    /// Consumes a standalone expression and dismantles its structural type
    /// without following the host call stack.
    pub fn discard_iteratively(self) {
        let Self { ty, origin, kind } = self;
        discard_type_iteratively(ty);
        discard_origin_iteratively(origin);
        discard_pure_expr_kind_metadata(kind);
    }
}

/// The closed expression families in the pure Ash dialect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PureExprKind {
    /// A value node.
    Value(PureValue),
    /// A resolved variable occurrence.
    Variable(VariableNode),
    /// A strict pure computation.
    Computation(PureComputation),
}

impl PureExprKind {
    /// Returns the number of graph edges owned by this closed payload.
    #[must_use]
    pub fn child_count(&self) -> usize {
        match self {
            Self::Value(value) => match value {
                PureValue::Integer(node) => fixed_child_count(node.children()),
                PureValue::Boolean(node) => fixed_child_count(node.children()),
                PureValue::Unit(node) => fixed_child_count(node.children()),
                PureValue::Function(node) => fixed_child_count(node.children()),
                PureValue::Constructor(_) => 0,
            },
            Self::Variable(node) => fixed_child_count(node.children()),
            Self::Computation(computation) => match computation {
                PureComputation::Bind(node) => fixed_child_count(node.children()),
                PureComputation::RecursiveBind(node) => node.child_count(),
                PureComputation::Apply(node) => fixed_child_count(node.children()),
                PureComputation::Primitive(node) => fixed_child_count(node.children()),
                PureComputation::Tuple(node) => node.elements().len(),
                PureComputation::Match(node) => node.arms().len() + 1,
                PureComputation::TypeAbstraction(_) | PureComputation::TypeApplication(_) => 1,
            },
        }
    }

    /// Returns one graph edge in deterministic evaluation-independent order.
    #[must_use]
    pub fn child_at(&self, index: usize) -> Option<NodeId> {
        match self {
            Self::Value(value) => match value {
                PureValue::Integer(node) => fixed_child_at(node.children(), index),
                PureValue::Boolean(node) => fixed_child_at(node.children(), index),
                PureValue::Unit(node) => fixed_child_at(node.children(), index),
                PureValue::Function(node) => fixed_child_at(node.children(), index),
                PureValue::Constructor(_) => None,
            },
            Self::Variable(node) => fixed_child_at(node.children(), index),
            Self::Computation(computation) => match computation {
                PureComputation::Bind(node) => fixed_child_at(node.children(), index),
                PureComputation::RecursiveBind(node) => node.child_at(index),
                PureComputation::Apply(node) => fixed_child_at(node.children(), index),
                PureComputation::Primitive(node) => fixed_child_at(node.children(), index),
                PureComputation::Tuple(node) => node.elements().get(index).copied(),
                PureComputation::Match(node) => {
                    if index == 0 {
                        Some(node.scrutinee())
                    } else {
                        node.arms().get(index - 1).map(CoreMatchArm::body)
                    }
                }
                PureComputation::TypeAbstraction(node) => {
                    fixed_child_at([Some(node.body())], index)
                }
                PureComputation::TypeApplication(node) => {
                    fixed_child_at([Some(node.function())], index)
                }
            },
        }
    }
}

fn fixed_child_count<const N: usize>(children: [Option<NodeId>; N]) -> usize {
    children.into_iter().flatten().count()
}

fn fixed_child_at<const N: usize>(children: [Option<NodeId>; N], index: usize) -> Option<NodeId> {
    children.into_iter().flatten().nth(index)
}

/// The closed value families in the pure Ash dialect.
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
    /// A nullary value or payload-constructor function.
    Constructor(ConstructorNode),
}

/// The closed computation families in the pure Ash dialect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PureComputation {
    /// A sequential nonrecursive binding.
    Bind(BindingNode),
    /// A simultaneous recursive binding group.
    RecursiveBind(RecursiveBindingNode),
    /// A strict unary application.
    Apply(ApplicationNode),
    /// A primitive operation.
    Primitive(PrimitiveNode),
    /// Strict tuple construction.
    Tuple(TupleNode),
    /// Structured first-match selection.
    Match(MatchNode),
    /// An explicit erased rank-1 type abstraction.
    TypeAbstraction(TypeAbstractionNode),
    /// An explicit erased rank-1 type application.
    TypeApplication(TypeApplicationNode),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DialectId(&'static str);

impl DialectId {
    pub(super) const PURE: Self = Self(AshPureDialect::NAME);

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
    pub(super) registry: Arc<ResolvedRegistry>,
    pub(super) arena: ArenaId,
    pub(super) nodes: Vec<StoredNode>,
    pub(super) root: NodeId,
}

impl UnvalidatedProgram {
    pub(super) fn discard_iteratively(mut self) {
        self.discard_contents();
    }

    pub(super) fn into_parts(
        mut self,
    ) -> (Arc<ResolvedRegistry>, ArenaId, Vec<StoredNode>, NodeId) {
        let registry = std::mem::take(&mut self.registry);
        let nodes = std::mem::take(&mut self.nodes);
        (registry, self.arena, nodes, self.root)
    }

    fn discard_contents(&mut self) {
        for stored in std::mem::take(&mut self.nodes) {
            discard_type_iteratively(stored.ty);
            if let Some(origin) = stored.origin {
                discard_origin_iteratively(origin);
            }
            match stored.kind {
                PureExprKind::Value(PureValue::Function(function)) => {
                    function.discard_metadata();
                }
                PureExprKind::Computation(PureComputation::Bind(binding)) => {
                    binding.discard_metadata();
                }
                PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                    group.discard_metadata();
                }
                PureExprKind::Computation(PureComputation::Match(match_node)) => {
                    match_node.discard_metadata();
                }
                PureExprKind::Computation(PureComputation::TypeApplication(operation)) => {
                    operation.discard_metadata();
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
                    | PureComputation::TypeAbstraction(_),
                ) => {}
            }
        }
        if let Ok(registry) = Arc::try_unwrap(std::mem::take(&mut self.registry)) {
            registry.discard_iteratively();
        }
    }
}

impl Drop for UnvalidatedProgram {
    fn drop(&mut self) {
        self.discard_contents();
    }
}

/// A pure Core arena whose graph, types, scope, dialect, and provenance hold.
#[derive(Debug)]
pub struct PureProgram {
    registry: Arc<ResolvedRegistry>,
    arena: ArenaId,
    nodes: Box<[TypedExpr]>,
    root: NodeId,
}

impl PureProgram {
    pub(super) fn new(
        registry: Arc<ResolvedRegistry>,
        arena: ArenaId,
        nodes: Vec<TypedExpr>,
        root: NodeId,
    ) -> Self {
        Self {
            registry,
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

    /// Returns the immutable nominal and constructor registry.
    #[must_use]
    pub const fn registry(&self) -> &Arc<ResolvedRegistry> {
        &self.registry
    }
}

impl Drop for PureProgram {
    fn drop(&mut self) {
        let nodes = std::mem::take(&mut self.nodes);
        for typed in nodes {
            discard_type_iteratively(typed.ty);
            discard_origin_iteratively(typed.origin);
            match typed.kind {
                PureExprKind::Value(PureValue::Function(function)) => {
                    function.discard_metadata();
                }
                PureExprKind::Computation(PureComputation::Bind(binding)) => {
                    binding.discard_metadata();
                }
                PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                    group.discard_metadata();
                }
                PureExprKind::Computation(PureComputation::Match(match_node)) => {
                    match_node.discard_metadata();
                }
                PureExprKind::Computation(PureComputation::TypeApplication(operation)) => {
                    operation.discard_metadata();
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
                    | PureComputation::TypeAbstraction(_),
                ) => {}
            }
        }
        let registry = std::mem::replace(&mut self.registry, Arc::new(ResolvedRegistry::default()));
        if let Ok(registry) = Arc::try_unwrap(registry) {
            registry.discard_iteratively();
        }
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

    /// Returns the immutable nominal and constructor registry.
    #[must_use]
    pub fn registry(&self) -> &Arc<ResolvedRegistry> {
        self.0.registry()
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
    /// Cumulative structural type work exceeded the compiler budget.
    TypeWorkExceeded,
    /// An Origin contains more recursive wrappers than Core currently admits.
    OriginDepthExceeded,
    /// A structured pattern contains more wrappers than Core currently admits.
    PatternDepthExceeded,
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
            Self::TypeWorkExceeded => "core cumulative type work is exceeded",
            Self::OriginDepthExceeded => "core origin structural depth is exceeded",
            Self::PatternDepthExceeded => "core pattern structural depth is exceeded",
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
    registry: Arc<ResolvedRegistry>,
    arena: Option<ArenaId>,
    nodes: Vec<StoredNode>,
    next_binder: u32,
    reserved_resolved: HashSet<BinderId>,
    materialized_resolved: HashSet<BinderId>,
    generated_binders: HashSet<BinderId>,
    inference_binders: HashSet<BinderId>,
    binder_phase_started: bool,
    type_work: TypeWorkBudget,
    rewrite_type_work: TypeWorkBudget,
    requires_type_rewrite: bool,
}

/// Identifies the first Core node after an elaboration-local type boundary.
#[derive(Clone, Copy, Debug)]
pub(crate) struct TypeRewriteCheckpoint(usize);

impl CoreBuilder {
    /// Starts an empty Core arena.
    pub fn new() -> Self {
        Self {
            registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
            arena: None,
            nodes: Vec::new(),
            next_binder: 0,
            reserved_resolved: HashSet::new(),
            materialized_resolved: HashSet::new(),
            generated_binders: HashSet::new(),
            inference_binders: HashSet::new(),
            binder_phase_started: false,
            type_work: TypeWorkBudget::default(),
            rewrite_type_work: TypeWorkBudget::default(),
            requires_type_rewrite: false,
        }
    }

    /// Starts an empty arena carrying an immutable resolved data registry.
    pub fn with_registry(registry: Arc<ResolvedRegistry>) -> Self {
        let mut builder = Self::new();
        builder.registry = registry;
        builder
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
        let (ty, origin, requires_type_rewrite) = admit_payloads(ty, origin, &mut self.type_work)?;
        let (id, next) = match self.next_binder_candidate() {
            Ok(candidate) => candidate,
            Err(error) => {
                discard_admitted_payload(ty, origin);
                return Err(error);
            }
        };
        let arena = match self.ensure_arena() {
            Ok(arena) => arena,
            Err(error) => {
                discard_admitted_payload(ty, origin);
                return Err(error);
            }
        };
        if !self.generated_binders.insert(id) {
            discard_admitted_payload(ty, origin);
            return Err(BuildError::InvalidPayload);
        }
        self.next_binder = next;
        self.binder_phase_started = true;
        if requires_type_rewrite {
            self.inference_binders.insert(id);
        }
        self.requires_type_rewrite |= requires_type_rewrite;
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
        let (ty, origin, requires_type_rewrite) = admit_payloads(ty, origin, &mut self.type_work)?;
        if !self.reserved_resolved.contains(&id) {
            discard_admitted_payload(ty, origin);
            return Err(BuildError::UnreservedResolvedBinder);
        }
        if self.materialized_resolved.contains(&id) {
            discard_admitted_payload(ty, origin);
            return Err(BuildError::DuplicateResolvedBinder);
        }
        let arena = match self.ensure_arena() {
            Ok(arena) => arena,
            Err(error) => {
                discard_admitted_payload(ty, origin);
                return Err(error);
            }
        };
        self.materialized_resolved.insert(id);
        self.binder_phase_started = true;
        if requires_type_rewrite {
            self.inference_binders.insert(id);
        }
        self.requires_type_rewrite |= requires_type_rewrite;
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

    /// Adds an unchecked constructor occurrence.
    pub fn constructor(
        &mut self,
        constructor: crate::types::ConstructorId,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        self.push(
            ty,
            origin,
            PureExprKind::Value(PureValue::Constructor(ConstructorNode::new(constructor))),
        )
    }

    /// Adds strict tuple construction with an unchecked result annotation.
    pub fn tuple(
        &mut self,
        elements: Vec<NodeId>,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        self.push(
            ty,
            origin,
            PureExprKind::Computation(PureComputation::Tuple(TupleNode::new(elements))),
        )
    }

    /// Adds a structured match with unchecked pattern and branch invariants.
    pub fn match_expression(
        &mut self,
        scrutinee: NodeId,
        arms: Vec<CoreMatchArm>,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        let admitted_arms = admit_match_arms(arms, &mut self.type_work, &self.inference_binders);
        let admitted_result = admit_payloads(ty, origin, &mut self.type_work);
        match (admitted_arms, admitted_result) {
            (Ok((arms, arm_rewrite)), Ok((ty, origin, result_rewrite))) => self
                .push_admitted_tracking(
                    ty,
                    origin,
                    PureExprKind::Computation(PureComputation::Match(MatchNode::new(
                        scrutinee, arms,
                    ))),
                    arm_rewrite || result_rewrite,
                ),
            (Err(arm_error), Ok((ty, origin, _))) => {
                discard_type_iteratively(ty);
                discard_origin_iteratively(origin);
                Err(arm_error)
            }
            (Ok((arms, _)), Err(result_error)) => {
                discard_match_arms(arms);
                Err(result_error)
            }
            (Err(arm_error), Err(_)) => Err(arm_error),
        }
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
        let (ty, origin, result_rewrite) = match admit_payloads(ty, origin, &mut self.type_work) {
            Ok(payloads) => payloads,
            Err(error) => {
                parameter.discard_metadata();
                return Err(error);
            }
        };
        if self.arena != Some(parameter.arena()) {
            parameter.discard_metadata();
            discard_admitted_payload(ty, origin);
            return Err(BuildError::ForeignBinder);
        }
        let binder_rewrite = self.inference_binders.contains(&parameter.id());
        self.push_admitted_tracking(
            ty,
            origin,
            PureExprKind::Value(PureValue::Function(FunctionNode::new(parameter, body))),
            binder_rewrite || result_rewrite,
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
        let (ty, origin, result_rewrite) = match admit_payloads(ty, origin, &mut self.type_work) {
            Ok(payloads) => payloads,
            Err(error) => {
                binder.discard_metadata();
                return Err(error);
            }
        };
        if self.arena != Some(binder.arena()) {
            binder.discard_metadata();
            discard_admitted_payload(ty, origin);
            return Err(BuildError::ForeignBinder);
        }
        let binder_rewrite = self.inference_binders.contains(&binder.id());
        self.push_admitted_tracking(
            ty,
            origin,
            PureExprKind::Computation(PureComputation::Bind(BindingNode::new(
                binder,
                initializer,
                body,
            ))),
            binder_rewrite || result_rewrite,
        )
    }

    /// Adds a simultaneous recursive binding group with unchecked invariants.
    ///
    /// Payload admission precedes binder-capability checks. The independent
    /// validator owns nonemptiness, function-or-guarded-data initializer,
    /// type, scope, and provenance invariants.
    ///
    /// # Errors
    ///
    /// Returns [`BuildError::ForeignBinder`] when any member binder was
    /// produced by another Core builder, after reporting any payload resource
    /// failure.
    pub fn recursive_binding(
        &mut self,
        members: Vec<(TypedBinder, NodeId)>,
        body: NodeId,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        let (ty, origin, result_rewrite) = match admit_payloads(ty, origin, &mut self.type_work) {
            Ok(payloads) => payloads,
            Err(error) => {
                discard_recursive_binding_inputs(members);
                return Err(error);
            }
        };
        if members
            .iter()
            .any(|(binder, _)| self.arena != Some(binder.arena()))
        {
            discard_recursive_binding_inputs(members);
            discard_admitted_payload(ty, origin);
            return Err(BuildError::ForeignBinder);
        }
        let binder_rewrite = members
            .iter()
            .any(|(binder, _)| self.inference_binders.contains(&binder.id()));
        let members = members
            .into_iter()
            .map(|(binder, initializer)| RecursiveBindingMember::new(binder, initializer))
            .collect();
        self.push_admitted_tracking(
            ty,
            origin,
            PureExprKind::Computation(PureComputation::RecursiveBind(RecursiveBindingNode::new(
                members, body,
            ))),
            binder_rewrite || result_rewrite,
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

    /// Adds an unchecked explicit type abstraction.
    pub fn type_abstraction(
        &mut self,
        parameters: Vec<crate::types::TypeVariableId>,
        body: NodeId,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        let parameter_admission = self
            .type_work
            .charge(parameters.len())
            .map_err(|()| BuildError::TypeWorkExceeded);
        let payloads = admit_payloads(ty, origin, &mut self.type_work);
        let (ty, origin, requires_type_rewrite) = match (parameter_admission, payloads) {
            (Err(error), Ok((ty, origin, _))) => {
                discard_admitted_payload(ty, origin);
                return Err(error);
            }
            (Err(error), Err(_)) | (Ok(()), Err(error)) => return Err(error),
            (Ok(()), Ok(payloads)) => payloads,
        };
        self.push_admitted_tracking(
            ty,
            origin,
            PureExprKind::Computation(PureComputation::TypeAbstraction(TypeAbstractionNode::new(
                parameters, body,
            ))),
            requires_type_rewrite,
        )
    }

    /// Adds an unchecked explicit type application.
    pub fn type_application(
        &mut self,
        function: NodeId,
        arguments: Vec<Type>,
        ty: Type,
        origin: Origin,
    ) -> Result<NodeId, BuildError> {
        let mut admitted_arguments = Vec::new();
        let mut first_error = None;
        let mut argument_rewrite = false;
        for argument in arguments {
            match admit_type_with_status(argument, &mut self.type_work, true) {
                Ok((argument, contains_inference)) if first_error.is_none() => {
                    argument_rewrite |= contains_inference;
                    admitted_arguments.push(argument);
                }
                Ok((argument, _)) => discard_type_iteratively(argument),
                Err(error) => {
                    first_error.get_or_insert(error);
                }
            }
        }
        let payloads = admit_payloads(ty, origin, &mut self.type_work);
        let (ty, origin, result_rewrite) = match (first_error, payloads) {
            (Some(error), Ok((ty, origin, _))) => {
                discard_type_vector_iteratively(&mut admitted_arguments);
                discard_admitted_payload(ty, origin);
                return Err(error);
            }
            (Some(error), Err(_)) => {
                discard_type_vector_iteratively(&mut admitted_arguments);
                return Err(error);
            }
            (None, Err(error)) => {
                discard_type_vector_iteratively(&mut admitted_arguments);
                return Err(error);
            }
            (None, Ok(payloads)) => payloads,
        };
        self.push_admitted_tracking(
            ty,
            origin,
            PureExprKind::Computation(PureComputation::TypeApplication(TypeApplicationNode::new(
                function,
                admitted_arguments,
            ))),
            argument_rewrite || result_rewrite,
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

    /// Records that an existing node successfully checked against an expected
    /// type whose source cause is optional.
    ///
    /// # Errors
    ///
    /// Returns [`BuildError::InvalidNodeId`] unless `node` belongs to this
    /// builder, or an origin resource error if the causal wrapper is too deep.
    pub(crate) fn record_type_check(
        &mut self,
        node: NodeId,
        expected_cause: Option<Span>,
    ) -> Result<(), BuildError> {
        let Some(arena) = self.arena else {
            return Err(BuildError::InvalidNodeId);
        };
        if node.arena() != arena {
            return Err(BuildError::InvalidNodeId);
        }
        let index = node.index()?;
        let stored = self.nodes.get(index).ok_or(BuildError::InvalidNodeId)?;
        let Some(current) = stored.origin.as_ref() else {
            return Err(BuildError::InvalidPayload);
        };
        let cause = match expected_cause {
            Some(span) if span.source() == current.primary_span().source() => Origin::Related {
                primary: Box::new(current.clone()),
                related: vec![span],
            },
            Some(_) | None => current.clone(),
        };
        let origin = admit_origin(Origin::Generated {
            cause: Box::new(cause),
            reason: GeneratedReason::TypeChecking,
        })?;
        replace_origin_iteratively(&mut self.nodes[index].origin, origin);
        Ok(())
    }

    /// Rewrites every stored type before unchecked Core leaves elaboration.
    ///
    /// The rewrite callback owns cumulative structural construction work. Core
    /// rechecks depth and cumulatively charges the quantifier identities added
    /// to rewritten storage.
    pub(crate) fn rewrite_types<F>(&mut self, mut rewrite: F) -> Result<(), BuildError>
    where
        F: FnMut(&Type) -> Result<Type, BuildError>,
    {
        let checkpoint = TypeRewriteCheckpoint(0);
        let rewritten_requires_type_rewrite = self.rewrite_types_from(checkpoint, &mut rewrite)?;
        self.requires_type_rewrite = rewritten_requires_type_rewrite;
        Ok(())
    }

    /// Captures the current end of the Core arena for a bounded type rewrite.
    pub(crate) fn type_rewrite_checkpoint(&self) -> TypeRewriteCheckpoint {
        TypeRewriteCheckpoint(self.nodes.len())
    }

    /// Rewrites type payloads only on nodes emitted after `checkpoint`.
    pub(crate) fn rewrite_types_since<F>(
        &mut self,
        checkpoint: TypeRewriteCheckpoint,
        mut rewrite: F,
    ) -> Result<(), BuildError>
    where
        F: FnMut(&Type) -> Result<Type, BuildError>,
    {
        let rewritten_requires_type_rewrite = self.rewrite_types_from(checkpoint, &mut rewrite)?;
        self.requires_type_rewrite |= rewritten_requires_type_rewrite;
        Ok(())
    }

    fn rewrite_types_from<F>(
        &mut self,
        checkpoint: TypeRewriteCheckpoint,
        rewrite: &mut F,
    ) -> Result<bool, BuildError>
    where
        F: FnMut(&Type) -> Result<Type, BuildError>,
    {
        let nodes = self
            .nodes
            .get_mut(checkpoint.0..)
            .ok_or(BuildError::InvalidNodeId)?;
        let rewrite_type_work = &mut self.rewrite_type_work;
        let mut rewritten_requires_type_rewrite = false;
        let mut rewrite_admitted = |ty: &Type| {
            let rewritten = rewrite(ty)?;
            let (rewritten, contains_inference) =
                admit_rewritten_type(rewritten, rewrite_type_work)?;
            rewritten_requires_type_rewrite |= contains_inference;
            Ok(rewritten)
        };
        for node in nodes {
            let rewritten = rewrite_admitted(&node.ty)?;
            replace_type_iteratively(&mut node.ty, rewritten);
            match &mut node.kind {
                PureExprKind::Value(PureValue::Function(function)) => {
                    function
                        .parameter_mut()
                        .rewrite_type(&mut rewrite_admitted)?;
                }
                PureExprKind::Computation(PureComputation::Bind(binding)) => {
                    binding.binder_mut().rewrite_type(&mut rewrite_admitted)?;
                }
                PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                    for member in group.members_mut() {
                        member.binder_mut().rewrite_type(&mut rewrite_admitted)?;
                    }
                }
                PureExprKind::Computation(PureComputation::Match(match_expression)) => {
                    for arm in match_expression.arms_mut() {
                        arm.pattern_mut().rewrite_types(&mut rewrite_admitted)?;
                    }
                }
                PureExprKind::Computation(PureComputation::TypeApplication(application)) => {
                    application.rewrite_types(&mut rewrite_admitted)?;
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
                    | PureComputation::TypeAbstraction(_),
                ) => {}
            }
        }
        Ok(rewritten_requires_type_rewrite)
    }

    /// Reports whether an admitted Core type still contains inference state.
    pub(crate) const fn requires_type_rewrite(&self) -> bool {
        self.requires_type_rewrite
    }

    /// Finishes unchecked construction at `root`.
    ///
    /// # Errors
    ///
    /// Returns [`BuildError::InvalidNodeId`] unless `root` belongs to this arena.
    pub fn finish(mut self, root: NodeId) -> Result<UnvalidatedProgram, BuildError> {
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
            registry: std::mem::take(&mut self.registry),
            arena,
            nodes: std::mem::take(&mut self.nodes),
            root,
        })
    }

    fn push(&mut self, ty: Type, origin: Origin, kind: PureExprKind) -> Result<NodeId, BuildError> {
        let (ty, origin, requires_type_rewrite) = admit_payloads(ty, origin, &mut self.type_work)?;
        self.push_admitted_tracking(ty, origin, kind, requires_type_rewrite)
    }

    fn push_admitted_tracking(
        &mut self,
        ty: Type,
        origin: Origin,
        kind: PureExprKind,
        requires_type_rewrite: bool,
    ) -> Result<NodeId, BuildError> {
        let node = self.push_admitted(ty, origin, kind)?;
        self.requires_type_rewrite |= requires_type_rewrite;
        Ok(node)
    }

    fn push_admitted(
        &mut self,
        ty: Type,
        origin: Origin,
        kind: PureExprKind,
    ) -> Result<NodeId, BuildError> {
        let index = match u32::try_from(self.nodes.len()) {
            Ok(index) => index,
            Err(_) => {
                discard_pending_node_payload(ty, origin, kind);
                return Err(BuildError::NodeIdExhausted);
            }
        };
        let arena = match self.ensure_arena() {
            Ok(arena) => arena,
            Err(error) => {
                discard_pending_node_payload(ty, origin, kind);
                return Err(error);
            }
        };
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

impl Drop for CoreBuilder {
    fn drop(&mut self) {
        for stored in self.nodes.drain(..) {
            discard_type_iteratively(stored.ty);
            if let Some(origin) = stored.origin {
                discard_origin_iteratively(origin);
            }
            discard_pure_expr_kind_metadata(stored.kind);
        }
    }
}

fn replace_origin_iteratively(slot: &mut Option<Origin>, replacement: Origin) {
    if let Some(displaced) = slot.replace(replacement) {
        discard_origin_iteratively(displaced);
    }
}

fn discard_admitted_payload(ty: Type, origin: Origin) {
    discard_type_iteratively(ty);
    discard_origin_iteratively(origin);
}

fn discard_type_vector_iteratively(types: &mut Vec<Type>) {
    for ty in types.drain(..) {
        discard_type_iteratively(ty);
    }
}

fn discard_recursive_binding_inputs(members: Vec<(TypedBinder, NodeId)>) {
    for (binder, _) in members {
        binder.discard_metadata();
    }
}

fn discard_pending_node_payload(ty: Type, origin: Origin, kind: PureExprKind) {
    discard_admitted_payload(ty, origin);
    discard_pure_expr_kind_metadata(kind);
}

fn discard_pure_expr_kind_metadata(kind: PureExprKind) {
    match kind {
        PureExprKind::Value(PureValue::Function(function)) => function.discard_metadata(),
        PureExprKind::Computation(PureComputation::Bind(binding)) => binding.discard_metadata(),
        PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
            group.discard_metadata();
        }
        PureExprKind::Computation(PureComputation::Match(match_node)) => {
            match_node.discard_metadata();
        }
        PureExprKind::Computation(PureComputation::TypeApplication(operation)) => {
            operation.discard_metadata();
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
            | PureComputation::TypeAbstraction(_),
        ) => {}
    }
}

enum PatternAdmissionTask {
    Visit(CorePattern, usize),
    VisitSequence(std::vec::IntoIter<CorePattern>, usize),
    FinishTuple {
        ty: Type,
        origin: Origin,
        count: usize,
    },
    FinishConstructor {
        ty: Type,
        origin: Origin,
        constructor: crate::types::ConstructorId,
        has_payload: bool,
    },
}

#[cfg(test)]
std::thread_local! {
    static PATTERN_ADMISSION_PENDING_PEAK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static MATCH_ARM_RETAINED_CAPACITY_PEAK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn record_pattern_admission_pending(pending: usize) {
    PATTERN_ADMISSION_PENDING_PEAK.with(|peak| peak.set(peak.get().max(pending)));
}

#[cfg(test)]
fn record_match_arm_retained_capacity(capacity: usize) {
    MATCH_ARM_RETAINED_CAPACITY_PEAK.with(|peak| peak.set(peak.get().max(capacity)));
}

enum PatternToken {
    Binder(Type, Origin, TypedBinder),
    Wildcard(Type, Origin),
    Boolean(Type, Origin, bool),
    Unit(Type, Origin),
    Tuple(Type, Origin, usize),
    Constructor(Type, Origin, crate::types::ConstructorId, bool),
}

fn admit_match_arms(
    arms: Vec<CoreMatchArm>,
    type_work: &mut TypeWorkBudget,
    inference_binders: &HashSet<BinderId>,
) -> Result<(Vec<CoreMatchArm>, bool), BuildError> {
    let mut admitted = Vec::new();
    let mut requires_type_rewrite = false;
    let mut remaining = arms.into_iter();
    while let Some(arm) = remaining.next() {
        let (pattern, body, origin) = arm.into_parts();
        let pattern = admit_pattern(pattern, type_work, inference_binders);
        let origin = admit_origin(origin);
        match (pattern, origin) {
            (Ok((pattern, pattern_rewrite)), Ok(origin)) => {
                requires_type_rewrite |= pattern_rewrite;
                admitted.push(CoreMatchArm::new(pattern, body, origin));
                #[cfg(test)]
                record_match_arm_retained_capacity(admitted.capacity());
            }
            (Err(error), Ok(origin)) => {
                discard_origin_iteratively(origin);
                discard_match_arms(admitted);
                discard_match_arm_remainder(remaining);
                return Err(error);
            }
            (Ok((pattern, _)), Err(error)) => {
                pattern.discard_iteratively();
                discard_match_arms(admitted);
                discard_match_arm_remainder(remaining);
                return Err(error);
            }
            (Err(pattern_error), Err(_)) => {
                discard_match_arms(admitted);
                discard_match_arm_remainder(remaining);
                return Err(pattern_error);
            }
        }
    }
    Ok((admitted, requires_type_rewrite))
}

fn admit_pattern(
    pattern: CorePattern,
    type_work: &mut TypeWorkBudget,
    inference_binders: &HashSet<BinderId>,
) -> Result<(CorePattern, bool), BuildError> {
    let mut work = vec![PatternAdmissionTask::Visit(pattern, 0)];
    let mut tokens = Vec::new();
    let mut requires_type_rewrite = false;
    #[cfg(test)]
    record_pattern_admission_pending(work.len());
    while let Some(task) = work.pop() {
        match task {
            PatternAdmissionTask::Visit(pattern, depth) => {
                if depth > CORE_PATTERN_DEPTH_LIMIT {
                    pattern.discard_iteratively();
                    discard_pattern_admission_work(work);
                    discard_pattern_tokens(tokens);
                    return Err(BuildError::PatternDepthExceeded);
                }
                let CorePattern { ty, origin, kind } = pattern;
                let (ty, origin, pattern_rewrite) = match admit_payloads(ty, origin, type_work) {
                    Ok(payloads) => payloads,
                    Err(error) => {
                        discard_pattern_kind(kind);
                        discard_pattern_admission_work(work);
                        discard_pattern_tokens(tokens);
                        return Err(error);
                    }
                };
                requires_type_rewrite |= pattern_rewrite;
                match kind {
                    CorePatternKind::Binder(binder) => {
                        requires_type_rewrite |= inference_binders.contains(&binder.id());
                        tokens.push(PatternToken::Binder(ty, origin, binder));
                    }
                    CorePatternKind::Wildcard => tokens.push(PatternToken::Wildcard(ty, origin)),
                    CorePatternKind::Boolean(value) => {
                        tokens.push(PatternToken::Boolean(ty, origin, value));
                    }
                    CorePatternKind::Unit => tokens.push(PatternToken::Unit(ty, origin)),
                    CorePatternKind::Tuple(elements) => {
                        let count = elements.len();
                        work.push(PatternAdmissionTask::FinishTuple { ty, origin, count });
                        work.push(PatternAdmissionTask::VisitSequence(
                            elements.into_vec().into_iter(),
                            depth.saturating_add(1),
                        ));
                    }
                    CorePatternKind::Constructor {
                        constructor,
                        payload,
                    } => {
                        let has_payload = payload.is_some();
                        work.push(PatternAdmissionTask::FinishConstructor {
                            ty,
                            origin,
                            constructor,
                            has_payload,
                        });
                        if let Some(payload) = payload {
                            work.push(PatternAdmissionTask::Visit(
                                *payload,
                                depth.saturating_add(1),
                            ));
                        }
                    }
                }
            }
            PatternAdmissionTask::VisitSequence(mut remaining, depth) => {
                if let Some(pattern) = remaining.next() {
                    work.push(PatternAdmissionTask::VisitSequence(remaining, depth));
                    work.push(PatternAdmissionTask::Visit(pattern, depth));
                }
            }
            PatternAdmissionTask::FinishTuple { ty, origin, count } => {
                tokens.push(PatternToken::Tuple(ty, origin, count));
            }
            PatternAdmissionTask::FinishConstructor {
                ty,
                origin,
                constructor,
                has_payload,
            } => tokens.push(PatternToken::Constructor(
                ty,
                origin,
                constructor,
                has_payload,
            )),
        }
        #[cfg(test)]
        record_pattern_admission_pending(work.len());
    }

    let mut rebuilt = Vec::new();
    let mut remaining_tokens = tokens.into_iter();
    while let Some(token) = remaining_tokens.next() {
        let pattern = match token {
            PatternToken::Binder(ty, origin, binder) => {
                CorePattern::new(ty, origin, CorePatternKind::Binder(binder))
            }
            PatternToken::Wildcard(ty, origin) => {
                CorePattern::new(ty, origin, CorePatternKind::Wildcard)
            }
            PatternToken::Boolean(ty, origin, value) => {
                CorePattern::new(ty, origin, CorePatternKind::Boolean(value))
            }
            PatternToken::Unit(ty, origin) => CorePattern::new(ty, origin, CorePatternKind::Unit),
            PatternToken::Tuple(ty, origin, count) => {
                if rebuilt.len() < count {
                    discard_type_iteratively(ty);
                    discard_origin_iteratively(origin);
                    discard_patterns(rebuilt);
                    discard_pattern_token_remainder(remaining_tokens);
                    return Err(BuildError::InvalidPayload);
                }
                let elements = rebuilt.split_off(rebuilt.len() - count);
                CorePattern::new(
                    ty,
                    origin,
                    CorePatternKind::Tuple(elements.into_boxed_slice()),
                )
            }
            PatternToken::Constructor(ty, origin, constructor, has_payload) => {
                let payload = if has_payload {
                    let Some(payload) = rebuilt.pop() else {
                        discard_type_iteratively(ty);
                        discard_origin_iteratively(origin);
                        discard_patterns(rebuilt);
                        discard_pattern_token_remainder(remaining_tokens);
                        return Err(BuildError::InvalidPayload);
                    };
                    Some(Box::new(payload))
                } else {
                    None
                };
                CorePattern::new(
                    ty,
                    origin,
                    CorePatternKind::Constructor {
                        constructor,
                        payload,
                    },
                )
            }
        };
        rebuilt.push(pattern);
    }
    let Some(result) = rebuilt.pop() else {
        return Err(BuildError::InvalidPayload);
    };
    if rebuilt.is_empty() {
        Ok((result, requires_type_rewrite))
    } else {
        result.discard_iteratively();
        discard_patterns(rebuilt);
        Err(BuildError::InvalidPayload)
    }
}

fn discard_patterns(patterns: Vec<CorePattern>) {
    for pattern in patterns {
        pattern.discard_iteratively();
    }
}

fn discard_pattern_token_remainder(tokens: impl Iterator<Item = PatternToken>) {
    discard_pattern_tokens(tokens);
}

fn discard_match_arm_remainder(arms: impl Iterator<Item = CoreMatchArm>) {
    for arm in arms {
        let (pattern, _, origin) = arm.into_parts();
        pattern.discard_iteratively();
        discard_origin_iteratively(origin);
    }
}

fn discard_match_arms(arms: Vec<CoreMatchArm>) {
    discard_match_arm_remainder(arms.into_iter());
}

fn discard_pattern_kind(kind: CorePatternKind) {
    match kind {
        CorePatternKind::Binder(binder) => binder.discard_metadata(),
        CorePatternKind::Tuple(elements) => {
            for pattern in elements.into_vec() {
                pattern.discard_iteratively();
            }
        }
        CorePatternKind::Constructor { payload, .. } => {
            if let Some(payload) = payload {
                payload.discard_iteratively();
            }
        }
        CorePatternKind::Wildcard | CorePatternKind::Boolean(_) | CorePatternKind::Unit => {}
    }
}

fn discard_pattern_admission_work(mut work: Vec<PatternAdmissionTask>) {
    while let Some(task) = work.pop() {
        match task {
            PatternAdmissionTask::Visit(pattern, _) => pattern.discard_iteratively(),
            PatternAdmissionTask::VisitSequence(remaining, _) => {
                for pattern in remaining {
                    pattern.discard_iteratively();
                }
            }
            PatternAdmissionTask::FinishTuple { ty, origin, .. }
            | PatternAdmissionTask::FinishConstructor { ty, origin, .. } => {
                discard_type_iteratively(ty);
                discard_origin_iteratively(origin);
            }
        }
    }
}

fn discard_pattern_tokens(tokens: impl IntoIterator<Item = PatternToken>) {
    for token in tokens {
        match token {
            PatternToken::Binder(ty, origin, binder) => {
                discard_type_iteratively(ty);
                discard_origin_iteratively(origin);
                binder.discard_metadata();
            }
            PatternToken::Wildcard(ty, origin)
            | PatternToken::Boolean(ty, origin, _)
            | PatternToken::Unit(ty, origin)
            | PatternToken::Tuple(ty, origin, _)
            | PatternToken::Constructor(ty, origin, _, _) => {
                discard_type_iteratively(ty);
                discard_origin_iteratively(origin);
            }
        }
    }
}

fn admit_payloads(
    ty: Type,
    origin: Origin,
    type_work: &mut TypeWorkBudget,
) -> Result<(Type, Origin, bool), BuildError> {
    let admitted_type = admit_type_with_status(ty, type_work, true);
    let admitted_origin = admit_origin(origin);
    match (admitted_type, admitted_origin) {
        (Ok((ty, contains_inference)), Ok(origin)) => Ok((ty, origin, contains_inference)),
        (Err(error), Ok(origin)) => {
            discard_origin_iteratively(origin);
            Err(error)
        }
        (Err(error), Err(_)) => Err(error),
        (Ok((ty, _)), Err(error)) => {
            discard_type_iteratively(ty);
            Err(error)
        }
    }
}

enum TypeAdmissionTask {
    Visit(Type, usize),
    VisitSequence(std::vec::IntoIter<Type>, usize),
    FinishFunction,
    FinishTuple(usize),
    FinishApplication,
    FinishForall(Box<[crate::types::TypeVariableId]>),
}

enum TypeToken {
    Int,
    Bool,
    Unit,
    Nominal(crate::types::NominalTypeId),
    Variable(crate::types::TypeVariableId),
    Inference(crate::types::InferenceVariableId),
    Application,
    Tuple(usize),
    Function,
    Forall(Box<[crate::types::TypeVariableId]>),
}

#[cfg(test)]
std::thread_local! {
    static TYPE_ADMISSION_PENDING_PEAK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn record_type_admission_pending(pending: usize) {
    TYPE_ADMISSION_PENDING_PEAK.with(|peak| peak.set(peak.get().max(pending)));
}

#[cfg(test)]
fn admit_type(ty: Type, type_work: &mut TypeWorkBudget) -> Result<Type, BuildError> {
    admit_type_with_status(ty, type_work, true).map(|(ty, _)| ty)
}

fn admit_rewritten_type(
    ty: Type,
    type_work: &mut TypeWorkBudget,
) -> Result<(Type, bool), BuildError> {
    admit_type_with_status(ty, type_work, false)
}

fn admit_type_with_status(
    ty: Type,
    type_work: &mut TypeWorkBudget,
    charge_structure: bool,
) -> Result<(Type, bool), BuildError> {
    let mut work = vec![TypeAdmissionTask::Visit(ty, 0)];
    let mut tokens = Vec::new();
    let mut exceeded = false;
    let mut contains_inference = false;
    #[cfg(test)]
    record_type_admission_pending(work.len());
    while let Some(task) = work.pop() {
        if charge_structure
            && matches!(&task, TypeAdmissionTask::Visit(_, _))
            && type_work.charge(1).is_err()
        {
            work.push(task);
            discard_type_admission_work(work);
            return Err(BuildError::TypeWorkExceeded);
        }
        match task {
            TypeAdmissionTask::Visit(Type::Int, _) => tokens.push(TypeToken::Int),
            TypeAdmissionTask::Visit(Type::Bool, _) => tokens.push(TypeToken::Bool),
            TypeAdmissionTask::Visit(Type::Unit, _) => tokens.push(TypeToken::Unit),
            TypeAdmissionTask::Visit(Type::Nominal(identity), _) => {
                tokens.push(TypeToken::Nominal(identity));
            }
            TypeAdmissionTask::Visit(Type::Variable(identity), _) => {
                tokens.push(TypeToken::Variable(identity));
            }
            TypeAdmissionTask::Visit(Type::Inference(identity), _) => {
                contains_inference = true;
                tokens.push(TypeToken::Inference(identity));
            }
            TypeAdmissionTask::Visit(Type::Application(function, argument), depth) => {
                let child_depth = depth.saturating_add(1);
                exceeded |= child_depth > CORE_PAYLOAD_DEPTH_LIMIT;
                work.push(TypeAdmissionTask::FinishApplication);
                work.push(TypeAdmissionTask::Visit(*argument, child_depth));
                // A source-level simultaneous nominal application is encoded as
                // a unary left spine. Its function links are representation
                // width, not additional source structural depth.
                work.push(TypeAdmissionTask::Visit(*function, depth));
            }
            TypeAdmissionTask::Visit(Type::Forall(parameters, body), depth) => {
                let child_depth = depth.saturating_add(1);
                exceeded |= child_depth > CORE_PAYLOAD_DEPTH_LIMIT;
                if type_work.charge(parameters.len()).is_err() {
                    work.push(TypeAdmissionTask::Visit(*body, child_depth));
                    discard_type_admission_work(work);
                    return Err(BuildError::TypeWorkExceeded);
                }
                work.push(TypeAdmissionTask::FinishForall(parameters));
                work.push(TypeAdmissionTask::Visit(*body, child_depth));
            }
            TypeAdmissionTask::Visit(Type::Tuple(elements), depth) => {
                let child_depth = depth.saturating_add(1);
                exceeded |= child_depth > CORE_PAYLOAD_DEPTH_LIMIT;
                let count = elements.len();
                work.push(TypeAdmissionTask::FinishTuple(count));
                work.push(TypeAdmissionTask::VisitSequence(
                    elements.into_vec().into_iter(),
                    child_depth,
                ));
            }
            TypeAdmissionTask::VisitSequence(mut remaining, depth) => {
                if let Some(ty) = remaining.next() {
                    work.push(TypeAdmissionTask::VisitSequence(remaining, depth));
                    work.push(TypeAdmissionTask::Visit(ty, depth));
                }
            }
            TypeAdmissionTask::Visit(Type::Function(domain, codomain), depth) => {
                let child_depth = depth.saturating_add(1);
                exceeded |= child_depth > CORE_PAYLOAD_DEPTH_LIMIT;
                work.push(TypeAdmissionTask::FinishFunction);
                work.push(TypeAdmissionTask::Visit(*codomain, child_depth));
                work.push(TypeAdmissionTask::Visit(*domain, child_depth));
            }
            TypeAdmissionTask::FinishFunction => tokens.push(TypeToken::Function),
            TypeAdmissionTask::FinishTuple(count) => tokens.push(TypeToken::Tuple(count)),
            TypeAdmissionTask::FinishApplication => tokens.push(TypeToken::Application),
            TypeAdmissionTask::FinishForall(parameters) => {
                tokens.push(TypeToken::Forall(parameters));
            }
        }
        #[cfg(test)]
        record_type_admission_pending(work.len());
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
            TypeToken::Nominal(identity) => rebuilt.push(Type::Nominal(identity)),
            TypeToken::Variable(identity) => rebuilt.push(Type::Variable(identity)),
            TypeToken::Inference(identity) => rebuilt.push(Type::Inference(identity)),
            TypeToken::Application => {
                let argument = rebuilt.pop().ok_or(BuildError::InvalidPayload)?;
                let function = rebuilt.pop().ok_or(BuildError::InvalidPayload)?;
                rebuilt.push(Type::Application(Box::new(function), Box::new(argument)));
            }
            TypeToken::Tuple(count) => {
                if rebuilt.len() < count {
                    return Err(BuildError::InvalidPayload);
                }
                let elements = rebuilt.split_off(rebuilt.len() - count);
                rebuilt.push(Type::Tuple(elements.into_boxed_slice()));
            }
            TypeToken::Function => {
                let Some(codomain) = rebuilt.pop() else {
                    return Err(BuildError::InvalidPayload);
                };
                let Some(domain) = rebuilt.pop() else {
                    return Err(BuildError::InvalidPayload);
                };
                rebuilt.push(Type::Function(Box::new(domain), Box::new(codomain)));
            }
            TypeToken::Forall(parameters) => {
                let body = rebuilt.pop().ok_or(BuildError::InvalidPayload)?;
                rebuilt.push(Type::Forall(parameters, Box::new(body)));
            }
        }
    }
    let Some(result) = rebuilt.pop() else {
        return Err(BuildError::InvalidPayload);
    };
    if !rebuilt.is_empty() {
        return Err(BuildError::InvalidPayload);
    }
    Ok((result, contains_inference))
}

fn discard_type_admission_work(mut work: Vec<TypeAdmissionTask>) {
    while let Some(task) = work.pop() {
        match task {
            TypeAdmissionTask::Visit(ty, depth) => match ty {
                Type::Tuple(elements) => {
                    work.push(TypeAdmissionTask::VisitSequence(
                        elements.into_vec().into_iter(),
                        depth,
                    ));
                }
                Type::Application(function, argument) => {
                    work.push(TypeAdmissionTask::Visit(*argument, depth));
                    work.push(TypeAdmissionTask::Visit(*function, depth));
                }
                Type::Function(domain, codomain) => {
                    work.push(TypeAdmissionTask::Visit(*codomain, depth));
                    work.push(TypeAdmissionTask::Visit(*domain, depth));
                }
                Type::Forall(_, body) => {
                    work.push(TypeAdmissionTask::Visit(*body, depth));
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            },
            TypeAdmissionTask::VisitSequence(mut remaining, depth) => {
                if let Some(ty) = remaining.next() {
                    work.push(TypeAdmissionTask::VisitSequence(remaining, depth));
                    work.push(TypeAdmissionTask::Visit(ty, depth));
                }
            }
            TypeAdmissionTask::FinishFunction
            | TypeAdmissionTask::FinishTuple(_)
            | TypeAdmissionTask::FinishApplication
            | TypeAdmissionTask::FinishForall(_) => {}
        }
    }
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
    use crate::{
        module::ModuleId,
        resolved::{ResolvedConstructor, ResolvedNominalType, ResolvedTypeVariable},
        source::{ByteRange, GeneratedReason, SourceFile},
        types::{ConstructorId, NominalTypeId, TypeVariableId},
    };

    fn resolved_id(local: u32) -> BinderId {
        BinderId::resolved(ModuleId::new(0), local)
    }

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

    fn application_type(depth: usize) -> Type {
        let mut ty = Type::Unit;
        for _ in 0..depth {
            ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
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

    #[test]
    fn unfinished_builder_discards_deep_payloads_on_a_small_stack() {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(128 * 1024)
                .spawn_scoped(scope, || {
                    let source = SourceFile::new("temporary-check.ash", "()")
                        .expect("test source should fit");
                    let origin = Origin::Source(
                        source
                            .span(ByteRange::new(0, 2).expect("ordered range"))
                            .expect("range should belong to source"),
                    );
                    let mut builder = CoreBuilder::new();
                    for _ in 0..32 {
                        builder
                            .unit(function_type(CORE_PAYLOAD_DEPTH_LIMIT), origin.clone())
                            .expect("boundary-depth payload should be admitted");
                    }
                })
                .expect("small-stack builder-drop thread should complete");
        });
    }

    #[test]
    fn replacing_an_origin_discards_the_displaced_deep_origin_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("replace-deep-core-origin".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("replace-origin.ash", "()")
                    .expect("the replacement fixture should fit");
                let mut slot = Some(generated_origin(&source, DEPTH));

                replace_origin_iteratively(&mut slot, generated_origin(&source, 0));

                assert_eq!(
                    slot.as_ref().map(Origin::primary_span).map(Span::source),
                    Some(source.id())
                );
            })
            .expect("the origin-replacement thread should start")
            .join()
            .expect("the displaced origin must be dismantled iteratively");
    }

    #[test]
    fn successful_core_metadata_rewrite_replaces_deep_types_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("successful-deep-core-rewrite".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("rewrite-core.ash", "()")
                    .expect("the rewrite fixture should fit");
                let origin = generated_origin(&source, 0);

                let mut node_builder = CoreBuilder::new();
                node_builder
                    .unit(application_type(DEPTH), origin.clone())
                    .expect("the deep node annotation should be admitted");
                node_builder
                    .rewrite_types(|_| Ok(Type::Unit))
                    .expect("the deep node annotation should rewrite");

                let mut binder_builder = CoreBuilder::new();
                let body = binder_builder
                    .unit(Type::Unit, origin.clone())
                    .expect("the function body should fit");
                let parameter = binder_builder
                    .binder(application_type(DEPTH), origin.clone())
                    .expect("the deep binder annotation should be admitted");
                binder_builder
                    .function(parameter, body, Type::Unit, origin.clone())
                    .expect("the unchecked function should fit");
                binder_builder
                    .rewrite_types(|_| Ok(Type::Unit))
                    .expect("the deep binder annotation should rewrite");

                let mut pattern_builder = CoreBuilder::new();
                let value = pattern_builder
                    .unit(Type::Unit, origin.clone())
                    .expect("the scrutinee should fit");
                pattern_builder
                    .match_expression(
                        value,
                        vec![CoreMatchArm::new(
                            CorePattern::new(
                                application_type(DEPTH),
                                origin.clone(),
                                CorePatternKind::Wildcard,
                            ),
                            value,
                            origin.clone(),
                        )],
                        Type::Unit,
                        origin.clone(),
                    )
                    .expect("the deep pattern annotation should be admitted");
                pattern_builder
                    .rewrite_types(|_| Ok(Type::Unit))
                    .expect("the deep pattern annotation should rewrite");

                let mut operation_builder = CoreBuilder::new();
                let function = operation_builder
                    .unit(Type::Unit, origin.clone())
                    .expect("the type-operation function should fit");
                operation_builder
                    .type_application(function, vec![application_type(DEPTH)], Type::Unit, origin)
                    .expect("the deep type argument should be admitted");
                operation_builder
                    .rewrite_types(|_| Ok(Type::Unit))
                    .expect("the deep type argument should rewrite");
            })
            .expect("the rewrite thread should start")
            .join()
            .expect("successful Core rewrites must dismantle old types iteratively");
    }

    #[test]
    fn unvalidated_program_discards_deep_payloads_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("unvalidated-deep-type-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    SourceFile::new("raw-core.ash", "()").expect("the raw Core fixture should fit");
                let origin = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();
                let root = builder
                    .unit(application_type(DEPTH), origin)
                    .expect("the deep raw annotation should be admitted");
                let unvalidated = builder.finish(root).expect("the raw Core root should fit");
                drop(unvalidated);
            })
            .expect("the raw Core thread should start")
            .join()
            .expect("raw Core teardown must dismantle stored types iteratively");
    }

    #[test]
    fn successful_public_binder_owners_drop_deep_types_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("successful-binder-owner-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    SourceFile::new("binder-owner.ash", "()").expect("the fixture should fit");
                let origin = generated_origin(&source, 0);

                let mut generated_builder = CoreBuilder::new();
                let generated = generated_builder
                    .binder(application_type(DEPTH), origin.clone())
                    .expect("the generated binder should be admitted");
                drop(generated);

                let resolved_id = resolved_id(0);
                let mut resolved_builder = CoreBuilder::new();
                resolved_builder
                    .reserve_resolved_binders([resolved_id])
                    .expect("the resolved binder should be reserved");
                let resolved = resolved_builder
                    .resolved_binder(resolved_id, application_type(DEPTH), origin)
                    .expect("the resolved binder should be admitted");
                drop(resolved);
            })
            .expect("the binder-owner thread should start")
            .join()
            .expect("successful public binder owners must dismantle their types iteratively");
    }

    #[test]
    fn public_match_arm_owner_drops_a_deep_pattern_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("public-match-arm-owner-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    SourceFile::new("match-arm-owner.ash", "()").expect("the fixture should fit");
                let origin = generated_origin(&source, 0);
                let arm = CoreMatchArm::new(
                    CorePattern::new(
                        application_type(DEPTH),
                        origin.clone(),
                        CorePatternKind::Wildcard,
                    ),
                    NodeId::new(ArenaId::new(0), 0),
                    origin,
                );
                drop(arm);
            })
            .expect("the match-arm owner thread should start")
            .join()
            .expect("a public match arm must dismantle its pattern iteratively");
    }

    #[test]
    fn public_core_pattern_has_an_iterative_consuming_disposal_path() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("public-pattern-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    SourceFile::new("pattern-owner.ash", "()").expect("the fixture should fit");
                CorePattern::new(
                    application_type(DEPTH),
                    generated_origin(&source, 0),
                    CorePatternKind::Wildcard,
                )
                .discard_iteratively();
            })
            .expect("the pattern-owner thread should start")
            .join()
            .expect("the documented Core pattern disposal path must fit a small stack");
    }

    #[test]
    fn public_typed_expression_disposes_type_application_arguments_iteratively() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("public-typed-expression-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("typed-expression-owner.ash", "()")
                    .expect("the fixture should fit");
                TypedExpr {
                    ty: Type::Unit,
                    origin: generated_origin(&source, 0),
                    kind: PureExprKind::Computation(PureComputation::TypeApplication(
                        TypeApplicationNode::new(
                            NodeId::new(ArenaId::new(0), 0),
                            vec![application_type(DEPTH)],
                        ),
                    )),
                }
                .discard_iteratively();
            })
            .expect("the typed-expression thread should start")
            .join()
            .expect("the public disposal path must dismantle Core type arguments iteratively");
    }

    #[test]
    fn canonical_application_core_admission_has_an_exact_cell_boundary() {
        let owner = NominalTypeId::new(ModuleId::new(0), 0);
        let application = || {
            Type::Application(
                Box::new(Type::Application(
                    Box::new(Type::Nominal(owner)),
                    Box::new(Type::Int),
                )),
                Box::new(Type::Bool),
            )
        };
        let mut exact = TypeWorkBudget::with_limit(5);
        let mut short = TypeWorkBudget::with_limit(4);

        let (admitted, exceeded) = admit_type_with_status(application(), &mut exact, true)
            .expect("the five canonical cells should fit exactly");
        assert!(!exceeded);
        assert_eq!(exact.used(), 5);
        discard_type_iteratively(admitted);
        assert_eq!(
            admit_type_with_status(application(), &mut short, true),
            Err(BuildError::TypeWorkExceeded),
        );
        assert_eq!(short.used(), 4);
    }

    #[test]
    fn validated_program_discards_a_wide_application_on_a_small_stack() {
        // Registry validation, canonical binder authentication, envelope
        // validation, and type-scope analysis consume 10W + 4 type-work
        // units for this fixture. Keep the application one cell below 32K so
        // the valid disposal witness remains inside the public ledger.
        const WIDTH: usize = 32_767;

        std::thread::Builder::new()
            .name("validated-wide-type-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("wide-core.ash", "x".repeat(WIDTH + 2))
                    .expect("the Core fixture should fit");
                let span = source
                    .span(
                        ByteRange::new(
                            0,
                            u32::try_from(WIDTH + 2).expect("the fixture length should fit"),
                        )
                        .expect("the range is ordered"),
                    )
                    .expect("the range belongs to the fixture");
                let origin = Origin::Source(span);
                let module = ModuleId::new(0);
                let owner = NominalTypeId::new(module, 0);
                let constructor = ConstructorId::new(owner, 0);
                let parameters = (0..WIDTH)
                    .map(|index| {
                        let start = u32::try_from(index + 1).expect("the fixture index should fit");
                        ResolvedTypeVariable {
                            id: TypeVariableId::resolved(
                                module,
                                u32::try_from(index).expect("the fixture index should fit"),
                            ),
                            spelling: format!("A{index}"),
                            kind: crate::types::Kind::Type,
                            origin: Origin::Source(
                                source
                                    .span(
                                        ByteRange::new(start, start + 1)
                                            .expect("the range is ordered"),
                                    )
                                    .expect("the range belongs to the fixture"),
                            ),
                        }
                    })
                    .collect::<Vec<_>>();
                let parameter_ids = parameters
                    .iter()
                    .map(|parameter| parameter.id)
                    .collect::<Vec<_>>();
                let registry = ResolvedRegistry::new(
                    vec![ResolvedNominalType {
                        id: owner,
                        spelling: "Wide".to_owned(),
                        constructors: vec![constructor].into_boxed_slice(),
                        origin: origin.clone(),
                    }],
                    vec![ResolvedConstructor {
                        id: constructor,
                        owner,
                        spelling: "Wide".to_owned(),
                        payload: None,
                        origin: Origin::Source(
                            source
                                .span(ByteRange::new(0, 1).expect("the range is ordered"))
                                .expect("the range belongs to the fixture"),
                        ),
                    }],
                )
                .with_type_parameters(vec![(owner, parameters)]);
                let mut result = Type::Nominal(owner);
                for parameter in &parameter_ids {
                    result =
                        Type::Application(Box::new(result), Box::new(Type::Variable(*parameter)));
                }
                let annotation = Type::Forall(parameter_ids.into_boxed_slice(), Box::new(result));
                let mut builder = CoreBuilder::with_registry(Arc::new(registry));
                let root = builder
                    .constructor(constructor, annotation, origin)
                    .expect("application-spine width must not become Core structural depth");
                let program = builder
                    .finish(root)
                    .expect("the Core fixture should finish");
                let validated = super::super::validate::validate(program, &[&source])
                    .expect("the saturated wide constructor scheme should validate");
                drop(validated);
            })
            .expect("the Core disposal thread should start")
            .join()
            .expect("validated Core should dispose canonical application spines iteratively");
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

    fn reset_type_admission_pending_peak() {
        TYPE_ADMISSION_PENDING_PEAK.with(|peak| peak.set(0));
    }

    fn type_admission_pending_peak() -> usize {
        TYPE_ADMISSION_PENDING_PEAK.with(std::cell::Cell::get)
    }

    fn reset_pattern_admission_peaks() {
        PATTERN_ADMISSION_PENDING_PEAK.with(|peak| peak.set(0));
        MATCH_ARM_RETAINED_CAPACITY_PEAK.with(|peak| peak.set(0));
    }

    fn pattern_admission_pending_peak() -> usize {
        PATTERN_ADMISSION_PENDING_PEAK.with(std::cell::Cell::get)
    }

    fn match_arm_retained_capacity_peak() -> usize {
        MATCH_ARM_RETAINED_CAPACITY_PEAK.with(std::cell::Cell::get)
    }

    fn nested_pattern(source: &SourceFile, depth: usize) -> CorePattern {
        let origin = generated_origin(source, 0);
        let mut pattern = CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard);
        for _ in 0..depth {
            pattern = CorePattern::new(
                Type::Unit,
                origin.clone(),
                CorePatternKind::Tuple(vec![pattern].into_boxed_slice()),
            );
        }
        pattern
    }

    #[test]
    fn pattern_payload_limit_rejects_deep_core_on_a_small_stack() {
        std::thread::Builder::new()
            .name("core-pattern-boundary".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("pattern.ash", "()").expect("test source");
                let origin = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();
                let value = builder.unit(Type::Unit, origin.clone()).expect("unit node");
                let before = builder.nodes.len();
                assert_eq!(
                    builder.match_expression(
                        value,
                        vec![CoreMatchArm::new(
                            nested_pattern(&source, 50_000),
                            value,
                            origin.clone(),
                        )],
                        Type::Unit,
                        origin.clone(),
                    ),
                    Err(BuildError::PatternDepthExceeded)
                );
                assert_eq!(builder.nodes.len(), before);

                builder
                    .match_expression(
                        value,
                        vec![CoreMatchArm::new(
                            nested_pattern(&source, CORE_PATTERN_DEPTH_LIMIT),
                            value,
                            origin.clone(),
                        )],
                        Type::Unit,
                        origin,
                    )
                    .expect("the exact pattern boundary is admitted");
            })
            .expect("pattern admission thread should start")
            .join()
            .expect("pattern admission should fit the small stack");
    }

    #[test]
    fn failed_match_arms_admit_and_dispose_deep_result_payloads_on_a_small_stack() {
        std::thread::Builder::new()
            .name("core-match-result-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("match-result.ash", "()").expect("test source");
                let shallow_origin = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();
                let value = builder
                    .unit(Type::Unit, shallow_origin.clone())
                    .expect("unit node");

                let error = builder
                    .match_expression(
                        value,
                        vec![CoreMatchArm::new(
                            nested_pattern(&source, CORE_PATTERN_DEPTH_LIMIT + 1),
                            value,
                            shallow_origin,
                        )],
                        function_type(5_000),
                        generated_origin(&source, 5_000),
                    )
                    .expect_err("the arm error retains precedence");
                assert_eq!(error, BuildError::PatternDepthExceeded);
            })
            .expect("match result disposal thread should start")
            .join()
            .expect("all failed match payloads must be disposed iteratively");
    }

    #[test]
    fn wide_pattern_admission_keeps_owned_pending_work_constant() {
        const WIDTH: usize = 100_000;
        const ALLOWANCE: usize = 64;
        let source = SourceFile::new("wide-pattern.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let element = CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard);
        let pattern = CorePattern::new(
            Type::Unit,
            origin,
            CorePatternKind::Tuple(vec![element; WIDTH].into_boxed_slice()),
        );
        let mut budget = TypeWorkBudget::default();
        budget
            .charge(crate::types::TYPE_WORK_LIMIT - ALLOWANCE)
            .expect("test setup leaves a small exact allowance");
        reset_pattern_admission_peaks();

        assert_eq!(
            admit_pattern(pattern, &mut budget, &HashSet::new()),
            Err(BuildError::TypeWorkExceeded)
        );
        assert!(pattern_admission_pending_peak() <= 3);
    }

    #[test]
    fn huge_match_arm_groups_retain_only_charged_admitted_arms() {
        const WIDTH: usize = 100_000;
        const ALLOWANCE: usize = 64;
        let source = SourceFile::new("wide-arms.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let arena = ArenaId::new(77);
        let body = NodeId::new(arena, 0);
        let arm = CoreMatchArm::new(
            CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard),
            body,
            origin,
        );
        let mut budget = TypeWorkBudget::default();
        budget
            .charge(crate::types::TYPE_WORK_LIMIT - ALLOWANCE)
            .expect("test setup leaves an exact arm allowance");
        reset_pattern_admission_peaks();

        assert_eq!(
            admit_match_arms(vec![arm; WIDTH], &mut budget, &HashSet::new()),
            Err(BuildError::TypeWorkExceeded)
        );
        assert!(match_arm_retained_capacity_peak() <= ALLOWANCE);
        assert!(pattern_admission_pending_peak() <= 1);
    }

    #[test]
    fn over_budget_type_admission_dismantles_the_remainder_on_a_small_stack() {
        std::thread::Builder::new()
            .name("core-type-work-boundary".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("type-work.ash", "()").expect("test source");
                let origin = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();

                assert_eq!(
                    builder.unit(function_type(crate::types::TYPE_WORK_LIMIT + 1), origin,),
                    Err(BuildError::TypeWorkExceeded)
                );
                assert!(builder.arena.is_none());
                assert!(builder.nodes.is_empty());
            })
            .expect("type-work admission thread should start")
            .join()
            .expect("over-budget type admission must fit the small stack");
    }

    #[test]
    fn type_application_dismantles_unvisited_arguments_after_resource_failure() {
        std::thread::Builder::new()
            .name("core-type-argument-boundary".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("type-arguments.ash", "()").expect("test source");
                let origin = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();
                let function = builder
                    .unit(Type::Unit, origin.clone())
                    .expect("function placeholder");
                builder
                    .type_work
                    .charge(crate::types::TYPE_WORK_LIMIT - 1)
                    .expect("test setup exhausts the type-work budget");
                let before = builder.nodes.len();

                assert_eq!(
                    builder.type_application(
                        function,
                        vec![Type::Int, function_type(crate::types::TYPE_WORK_LIMIT + 1),],
                        Type::Unit,
                        origin,
                    ),
                    Err(BuildError::TypeWorkExceeded)
                );
                assert_eq!(builder.nodes.len(), before);
            })
            .expect("type-argument admission thread should start")
            .join()
            .expect("rejected type arguments must fit the small stack");
    }

    #[test]
    fn type_application_dismantles_result_payload_after_argument_failure() {
        std::thread::Builder::new()
            .name("core-type-application-result-boundary".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("type-result.ash", "()").expect("test source");
                let origin = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();
                let function = builder
                    .unit(Type::Unit, origin.clone())
                    .expect("function placeholder");
                builder
                    .type_work
                    .charge(crate::types::TYPE_WORK_LIMIT - 1)
                    .expect("test setup exhausts the type-work budget");
                let before = builder.nodes.len();

                assert_eq!(
                    builder.type_application(
                        function,
                        vec![Type::Int],
                        function_type(crate::types::TYPE_WORK_LIMIT + 1),
                        origin,
                    ),
                    Err(BuildError::TypeWorkExceeded)
                );
                assert_eq!(builder.nodes.len(), before);
            })
            .expect("type-application result admission thread should start")
            .join()
            .expect("rejected type-application result must fit the small stack");
    }

    #[test]
    fn type_application_discards_an_admitted_deep_argument_before_a_later_rejection() {
        const DEPTH: usize = 32_768;
        const DEEP_CELLS: usize = DEPTH * 2 + 1;

        std::thread::Builder::new()
            .name("admitted-argument-before-rejection".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("argument-before-error.ash", "()")
                    .expect("the fixture should fit");
                let origin = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();
                let function = builder
                    .unit(Type::Unit, origin.clone())
                    .expect("the function placeholder should fit");
                builder
                    .type_work
                    .charge(
                        crate::types::TYPE_WORK_LIMIT
                            .saturating_sub(builder.type_work.used())
                            .saturating_sub(DEEP_CELLS),
                    )
                    .expect("the setup should leave exactly one deep argument");

                assert_eq!(
                    builder.type_application(
                        function,
                        vec![application_type(DEPTH), Type::Unit],
                        Type::Unit,
                        origin,
                    ),
                    Err(BuildError::TypeWorkExceeded)
                );
            })
            .expect("the admitted-argument thread should start")
            .join()
            .expect("an admitted argument must be dismantled iteratively after a later error");
    }

    #[test]
    fn type_application_discards_a_deep_argument_admitted_after_an_earlier_rejection() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("rejection-before-admitted-argument".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("error-before-argument.ash", "()")
                    .expect("the fixture should fit");
                let origin = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();
                let function = builder
                    .unit(Type::Unit, origin.clone())
                    .expect("the function placeholder should fit");

                assert_eq!(
                    builder.type_application(
                        function,
                        vec![
                            function_type(CORE_PAYLOAD_DEPTH_LIMIT + 1),
                            application_type(DEPTH),
                        ],
                        Type::Unit,
                        origin,
                    ),
                    Err(BuildError::TypeDepthExceeded)
                );
            })
            .expect("the rejected-then-admitted thread should start")
            .join()
            .expect("a later admitted argument must be dismantled iteratively");
    }

    #[test]
    fn type_application_discards_an_admitted_deep_result_after_argument_failure() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("argument-error-with-admitted-result".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("argument-error-result.ash", "()")
                    .expect("the fixture should fit");
                let origin = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();
                let function = builder
                    .unit(Type::Unit, origin.clone())
                    .expect("the function placeholder should fit");

                assert_eq!(
                    builder.type_application(
                        function,
                        vec![function_type(CORE_PAYLOAD_DEPTH_LIMIT + 1)],
                        application_type(DEPTH),
                        origin,
                    ),
                    Err(BuildError::TypeDepthExceeded)
                );
            })
            .expect("the admitted-result thread should start")
            .join()
            .expect("an admitted result must be dismantled iteratively after argument failure");
    }

    #[test]
    fn type_abstraction_discards_an_admitted_deep_result_after_parameter_failure() {
        const DEPTH: usize = 32_768;
        const DEEP_CELLS: usize = DEPTH * 2 + 1;

        std::thread::Builder::new()
            .name("parameter-error-with-admitted-result".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("parameter-error-result.ash", "()")
                    .expect("the fixture should fit");
                let origin = generated_origin(&source, 0);
                let mut builder = CoreBuilder::new();
                let body = builder
                    .unit(Type::Unit, origin.clone())
                    .expect("the abstraction body should fit");
                builder
                    .type_work
                    .charge(
                        crate::types::TYPE_WORK_LIMIT
                            .saturating_sub(builder.type_work.used())
                            .saturating_sub(DEEP_CELLS),
                    )
                    .expect("the setup should leave exactly one deep result");
                let parameters = (0..=DEEP_CELLS)
                    .map(|index| {
                        crate::types::TypeVariableId::new(
                            u32::try_from(index).expect("the parameter identity should fit"),
                        )
                    })
                    .collect();

                assert_eq!(
                    builder.type_abstraction(parameters, body, application_type(DEPTH), origin,),
                    Err(BuildError::TypeWorkExceeded)
                );
            })
            .expect("the parameter-failure thread should start")
            .join()
            .expect("an admitted abstraction result must be dismantled iteratively");
    }

    #[test]
    fn wide_type_admission_keeps_pending_fan_out_constant() {
        const WIDTH: usize = 4_096;
        let mut type_work = TypeWorkBudget::default();
        type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 2)
            .expect("test setup leaves two type-work cells");
        reset_type_admission_pending_peak();

        let error = admit_type(
            Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice()),
            &mut type_work,
        )
        .expect_err("wide input must exhaust the cumulative budget");

        assert_eq!(error, BuildError::TypeWorkExceeded);
        assert!(
            type_admission_pending_peak() <= 3,
            "wide fan-out retained {} pending tasks",
            type_admission_pending_peak()
        );
    }

    #[test]
    fn forall_quantifiers_consume_the_exact_admission_budget() {
        let mut type_work = TypeWorkBudget::default();
        type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 4)
            .expect("test setup leaves four type-work cells");
        let parameters = vec![
            crate::types::TypeVariableId::new(0),
            crate::types::TypeVariableId::new(1),
        ]
        .into_boxed_slice();

        admit_type(
            Type::Forall(parameters, Box::new(Type::Unit)),
            &mut type_work,
        )
        .expect("one forall cell, two quantifiers, and one body cell fit exactly");
        assert_eq!(
            admit_type(Type::Unit, &mut type_work),
            Err(BuildError::TypeWorkExceeded)
        );
    }

    #[test]
    fn type_abstraction_binders_consume_the_exact_builder_budget() {
        let source = SourceFile::new("type-abstraction.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let parameters = vec![
            crate::types::TypeVariableId::new(0),
            crate::types::TypeVariableId::new(1),
        ];
        let mut builder = CoreBuilder::new();
        let body = builder
            .unit(Type::Unit, origin.clone())
            .expect("small body");
        builder
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 4)
            .expect("test setup leaves three cells after the body");

        builder
            .type_abstraction(parameters, body, Type::Unit, origin.clone())
            .expect("two binders and one result type fit exactly");
        assert_eq!(
            builder.unit(Type::Unit, origin),
            Err(BuildError::TypeWorkExceeded)
        );
    }

    #[test]
    fn type_application_arguments_charge_quantifiers_at_the_exact_boundary() {
        let source = SourceFile::new("type-application.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let parameters = vec![
            crate::types::TypeVariableId::new(0),
            crate::types::TypeVariableId::new(1),
        ]
        .into_boxed_slice();
        let mut builder = CoreBuilder::new();
        let function = builder
            .unit(Type::Unit, origin.clone())
            .expect("small function placeholder");
        builder
            .type_work
            .charge(crate::types::TYPE_WORK_LIMIT - 6)
            .expect("test setup leaves five cells after the function");

        builder
            .type_application(
                function,
                vec![Type::Forall(parameters, Box::new(Type::Unit))],
                Type::Unit,
                origin.clone(),
            )
            .expect("the argument scheme and result fit exactly");
        assert_eq!(
            builder.unit(Type::Unit, origin),
            Err(BuildError::TypeWorkExceeded)
        );
    }

    #[test]
    fn rewritten_forall_quantifiers_cross_the_same_admission_boundary() {
        let source = SourceFile::new("rewrite.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let parameters = (0..=crate::types::TYPE_WORK_LIMIT)
            .map(|index| {
                crate::types::TypeVariableId::new(u32::try_from(index).expect("parameter identity"))
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let mut builder = CoreBuilder::new();
        builder.unit(Type::Unit, origin).expect("small stored node");
        let mut replacement = Some(Type::Forall(parameters, Box::new(Type::Unit)));

        let error = builder
            .rewrite_types(|_| Ok(replacement.take().expect("one stored type")))
            .expect_err("rewritten quantifiers must be admitted before storage");

        assert_eq!(error, BuildError::TypeWorkExceeded);
    }

    #[test]
    fn rewritten_type_application_arguments_charge_quantifiers() {
        let source = SourceFile::new("rewrite-argument.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let parameters = (0..=crate::types::TYPE_WORK_LIMIT)
            .map(|index| {
                crate::types::TypeVariableId::new(u32::try_from(index).expect("parameter identity"))
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let mut builder = CoreBuilder::new();
        let function = builder
            .unit(Type::Unit, origin.clone())
            .expect("small function placeholder");
        builder
            .type_application(function, vec![Type::Int], Type::Unit, origin)
            .expect("small type application");
        let mut replacement = Some(Type::Forall(parameters, Box::new(Type::Unit)));
        let mut visited = 0_usize;

        let error = builder
            .rewrite_types(|ty| {
                visited += 1;
                if visited == 3 {
                    Ok(replacement.take().expect("one application argument"))
                } else {
                    Ok(ty.clone())
                }
            })
            .expect_err("rewritten argument quantifiers must be admitted before storage");

        assert_eq!(error, BuildError::TypeWorkExceeded);
    }

    #[test]
    fn builder_tracks_inference_in_patterns_and_type_arguments_during_admission() {
        let source = SourceFile::new("rewrite-status.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let inference = crate::types::InferenceVariableId::new(999);
        let mut builder = CoreBuilder::new();
        let scrutinee = builder
            .unit(Type::Unit, origin.clone())
            .expect("small scrutinee");
        let body = builder
            .unit(Type::Unit, origin.clone())
            .expect("small arm body");
        assert!(!builder.requires_type_rewrite());

        let pattern = CorePattern::new(
            Type::Inference(inference),
            origin.clone(),
            CorePatternKind::Wildcard,
        );
        let matched = builder
            .match_expression(
                scrutinee,
                vec![CoreMatchArm::new(pattern, body, origin.clone())],
                Type::Unit,
                origin.clone(),
            )
            .expect("unchecked pattern admission should retain the type");
        assert!(builder.requires_type_rewrite());

        builder
            .rewrite_types(|ty| match ty {
                Type::Inference(_) => Ok(Type::Unit),
                _ => Ok(ty.clone()),
            })
            .expect("rewriting should remove the admitted inference type");
        assert!(!builder.requires_type_rewrite());

        builder
            .type_application(
                matched,
                vec![Type::Inference(inference)],
                Type::Unit,
                origin,
            )
            .expect("unchecked type argument admission should retain the type");
        assert!(builder.requires_type_rewrite());
    }

    #[test]
    fn storing_an_inference_binder_restores_rewrite_status_after_rewrite() {
        let source = SourceFile::new("binder-rewrite-status.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let mut builder = CoreBuilder::new();
        let binder = builder
            .binder(
                Type::Inference(crate::types::InferenceVariableId::new(999)),
                origin.clone(),
            )
            .expect("unchecked binder admission should retain the type");
        let body = builder
            .unit(Type::Unit, origin.clone())
            .expect("small function body");
        assert!(builder.requires_type_rewrite());

        builder
            .rewrite_types(|ty| Ok(ty.clone()))
            .expect("the stored body has no inference type");
        assert!(!builder.requires_type_rewrite());

        builder
            .function(
                binder,
                body,
                Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
                origin,
            )
            .expect("the binder belongs to this arena");
        assert!(builder.requires_type_rewrite());
    }

    #[test]
    fn quantifier_failures_dismantle_unadmitted_types_on_a_small_stack() {
        std::thread::Builder::new()
            .name("core-quantifier-boundary".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("quantifiers.ash", "()").expect("test source");
                let origin = generated_origin(&source, 0);
                let parameters = vec![
                    crate::types::TypeVariableId::new(0),
                    crate::types::TypeVariableId::new(1),
                ];
                let mut builder = CoreBuilder::new();
                let body = builder
                    .unit(Type::Unit, origin.clone())
                    .expect("small abstraction body");
                builder
                    .type_work
                    .charge(crate::types::TYPE_WORK_LIMIT - 2)
                    .expect("test setup leaves one type-work cell after the body");

                assert_eq!(
                    builder.type_abstraction(parameters, body, function_type(50_000), origin,),
                    Err(BuildError::TypeWorkExceeded)
                );
            })
            .expect("quantifier admission thread should start")
            .join()
            .expect("quantifier rejection must fit the small stack");
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
            .reserve_resolved_binders([resolved_id(0), resolved_id(1)])
            .expect("complete resolved namespace is reserved");
        assert_eq!(
            builder.resolved_binder(
                resolved_id(0),
                function_type(CORE_PAYLOAD_DEPTH_LIMIT + 1),
                origin.clone(),
            ),
            Err(BuildError::TypeDepthExceeded)
        );
        let resolved = builder
            .resolved_binder(resolved_id(0), Type::Unit, origin.clone())
            .expect("first resolved identity is admitted");
        let generated = builder
            .binder(Type::Unit, origin.clone())
            .expect("fresh generated identity");
        let second_resolved = builder
            .resolved_binder(resolved_id(1), Type::Unit, origin.clone())
            .expect("later reserved identity remains materializable");

        assert_ne!(resolved.id(), generated.id());
        assert_ne!(second_resolved.id(), generated.id());
        assert_eq!(generated.id(), BinderId::generated(0));
        assert_eq!(
            builder.resolved_binder(resolved_id(0), Type::Unit, origin),
            Err(BuildError::DuplicateResolvedBinder)
        );
    }

    #[test]
    fn sparse_high_reservation_keeps_low_generated_ids_available() {
        let source = SourceFile::new("binder.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let mut builder = CoreBuilder::new();
        builder
            .reserve_resolved_binders([resolved_id(u32::MAX - 1)])
            .expect("high resolved identity is reserved");

        let generated = builder
            .binder(Type::Unit, origin)
            .expect("low generated identity remains available");
        assert_eq!(generated.id(), BinderId::generated(0));
    }

    #[test]
    fn reservation_is_transactional_and_closes_after_allocation_starts() {
        let source = SourceFile::new("binder.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let mut builder = CoreBuilder::new();
        builder
            .reserve_resolved_binders([resolved_id(2)])
            .expect("first reservation");
        assert_eq!(
            builder.reserve_resolved_binders([resolved_id(3), resolved_id(3)]),
            Err(BuildError::DuplicateBinderReservation)
        );
        assert!(!builder.reserved_resolved.contains(&resolved_id(3)));

        builder
            .binder(Type::Unit, origin)
            .expect("generated allocation starts the binder phase");
        assert_eq!(
            builder.reserve_resolved_binders([resolved_id(4)]),
            Err(BuildError::BinderReservationPhaseStarted)
        );
        assert!(!builder.reserved_resolved.contains(&resolved_id(4)));
    }

    #[test]
    fn resolved_materialization_requires_reservation_and_is_unique() {
        let source = SourceFile::new("binder.ash", "()").expect("test source");
        let origin = generated_origin(&source, 0);
        let mut builder = CoreBuilder::new();
        assert_eq!(
            builder.resolved_binder(resolved_id(0), Type::Unit, origin.clone()),
            Err(BuildError::UnreservedResolvedBinder)
        );
        builder
            .reserve_resolved_binders([resolved_id(0)])
            .expect("resolved identity is reserved");
        builder
            .resolved_binder(resolved_id(0), Type::Unit, origin.clone())
            .expect("first materialization");
        assert_eq!(
            builder.resolved_binder(resolved_id(0), Type::Unit, origin),
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
        assert_eq!(last.id(), BinderId::generated(u32::MAX - 1));
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
        let id = resolved_id(7);
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
