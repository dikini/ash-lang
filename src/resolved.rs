//! Name-resolved, source-spanned syntax passed to typed elaboration.

use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
    hash::Hash,
    sync::Arc,
};

use crate::{
    integer::Integer,
    interface::{
        CheckedImplementation, CheckedInterface, CheckedRequirement, ConstrainedScheme,
        EvidenceSlot, ImplId, ImplMethodId, InterfaceId, MatchedNominalIdentities, MethodId,
        OverlapFailure, RequirementId, implementation_heads_overlap_structurally,
        implementation_prerequisite_terminates, same_type_with_constraint_budget,
        same_type_with_constraint_budget_observing_nominals,
    },
    kind::{KindEnvironments, KindFailure},
    module::ModuleId,
    source::{Origin, Span, discard_origin_iteratively},
    types::{
        ConstructorId, IterativeTypeOwner, Kind, NominalTypeId, Type, TypeVariableId,
        TypeWorkBudget, charge_kind_with_charge, charge_type_cells, clone_arrows_with_budget,
        clone_kind_with_budget, clone_type_with_budget, discard_type_iteratively,
        same_kind_with_charge,
    },
};

#[cfg(test)]
use crate::interface::EvidenceSelection;

/// Stable identity of one resolved or compiler-generated term binder.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BinderId {
    /// A source binder qualified by its defining canonical module.
    Resolved {
        /// Defining module identity.
        module: ModuleId,
        /// Source-order binder index within that module.
        local: u32,
    },
    /// A compiler-generated binder in the enclosing Core program.
    Generated(u32),
}

impl BinderId {
    /// Creates one compiler-generated binder identity.
    ///
    /// Retained as the compatibility spelling for Core fixture construction.
    pub(crate) const fn new(local: u32) -> Self {
        Self::generated(local)
    }

    pub(crate) const fn resolved(module: ModuleId, local: u32) -> Self {
        Self::Resolved { module, local }
    }

    pub(crate) const fn generated(local: u32) -> Self {
        Self::Generated(local)
    }

    /// Returns the defining module for a source binder.
    #[must_use]
    pub const fn module(self) -> Option<ModuleId> {
        match self {
            Self::Resolved { module, .. } => Some(module),
            Self::Generated(_) => None,
        }
    }

    /// Returns the module-local or generated-program-local index.
    #[must_use]
    pub const fn local(self) -> u32 {
        match self {
            Self::Resolved { local, .. } | Self::Generated(local) => local,
        }
    }
}

/// A resolved definition site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Binder {
    /// Stable identity assigned by the resolver.
    pub id: BinderId,
    /// Exact source spelling.
    pub spelling: String,
    /// Causal source provenance for the definition site.
    pub origin: Origin,
}

/// A resolved occurrence site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedOccurrence {
    /// Typed identity selected by lexical scope.
    pub term: ResolvedTermName,
    /// Exact source spelling at this occurrence.
    pub spelling: String,
    /// Causal source provenance for the occurrence site.
    pub origin: Origin,
    /// Exact direct import occurrence that introduced this term binding.
    pub(crate) import_span: Option<Span>,
    /// Atomic checked-goal and evidence positions owned by this exact occurrence.
    pub evidence: Box<[EvidenceSlot]>,
}

impl ResolvedOccurrence {
    /// Returns the ordinary binder selected by this occurrence, if it is not a method.
    #[must_use]
    pub const fn global_binder(&self) -> Option<BinderId> {
        match self.term {
            ResolvedTermName::Global(binder) => Some(binder),
            ResolvedTermName::Method(_) => None,
        }
    }

    /// Returns the direct import occurrence that introduced this binding.
    #[must_use]
    pub const fn import_span(&self) -> Option<Span> {
        self.import_span
    }
}

/// The tagged semantic identity of one resolved term occurrence.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ResolvedTermName {
    /// An ordinary global or lexical binder.
    Global(BinderId),
    /// An interface method requiring evidence during checking.
    Method(MethodId),
}

/// A repeated equation-head occurrence, which never owns evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedEquationHead {
    /// Stable identity of the ordinary or hidden binder being defined.
    pub binder: BinderId,
    /// Exact source spelling at the repeated head.
    pub spelling: String,
    /// Causal source provenance for the head occurrence.
    pub origin: Origin,
}

/// Cross-family declaration order with category-local indices.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResolvedDeclarationIndex {
    /// A nominal type declaration.
    Type(usize),
    /// An interface declaration.
    Interface(usize),
    /// An ordinary global definition.
    Global(usize),
    /// An implementation declaration.
    Implementation(usize),
}

/// One resolver-authenticated source edge to a direct dependency.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DirectDependencyRoute {
    target: ModuleId,
    import_span: Span,
}

impl DirectDependencyRoute {
    pub(crate) const fn new(target: ModuleId, import_span: Span) -> Self {
        Self {
            target,
            import_span,
        }
    }

    /// Returns the canonical identity reached by this direct edge.
    #[must_use]
    pub const fn target(self) -> ModuleId {
        self.target
    }

    /// Returns the exact source import occurrence that introduced this edge.
    #[must_use]
    pub const fn import_span(self) -> Span {
        self.import_span
    }
}

/// One declarations-only module after name resolution.
#[derive(Debug, Eq, PartialEq)]
pub struct ResolvedModule {
    module: ModuleId,
    registry: Arc<ResolvedRegistry>,
    imported: ImportedFacts,
    direct_dependencies: Box<[DirectDependencyRoute]>,
    declaration_order: Box<[ResolvedDeclarationIndex]>,
    interfaces: Box<[ResolvedInterfaceDeclaration]>,
    implementations: Box<[ResolvedImplementation]>,
    definitions: Box<[ResolvedDefinition]>,
    export_candidate: ResolvedExportCandidate,
    span: Span,
}

pub(crate) struct ResolvedModuleParts {
    pub module: ModuleId,
    pub registry: Arc<ResolvedRegistry>,
    pub imported: ImportedFacts,
    pub direct_dependencies: Vec<DirectDependencyRoute>,
    pub declaration_order: Vec<ResolvedDeclarationIndex>,
    pub interfaces: Vec<ResolvedInterfaceDeclaration>,
    pub implementations: Vec<ResolvedImplementation>,
    pub definitions: Vec<ResolvedDefinition>,
    pub export_candidate: ResolvedExportCandidate,
    pub span: Span,
}

impl ResolvedModule {
    pub(crate) fn new(mut parts: ResolvedModuleParts) -> Self {
        Self {
            module: parts.module,
            registry: std::mem::take(&mut parts.registry),
            imported: std::mem::take(&mut parts.imported),
            direct_dependencies: std::mem::take(&mut parts.direct_dependencies).into_boxed_slice(),
            declaration_order: std::mem::take(&mut parts.declaration_order).into_boxed_slice(),
            interfaces: std::mem::take(&mut parts.interfaces).into_boxed_slice(),
            implementations: std::mem::take(&mut parts.implementations).into_boxed_slice(),
            definitions: std::mem::take(&mut parts.definitions).into_boxed_slice(),
            export_candidate: std::mem::take(&mut parts.export_candidate),
            span: parts.span,
        }
    }

    /// Returns the defining canonical module identity.
    #[must_use]
    pub const fn module(&self) -> ModuleId {
        self.module
    }
    /// Returns the module's resolved local registry.
    #[must_use]
    pub fn registry(&self) -> &Arc<ResolvedRegistry> {
        &self.registry
    }

    /// Returns selected, body-free facts cloned from dependency summaries.
    #[must_use]
    pub const fn imported_facts(&self) -> &ImportedFacts {
        &self.imported
    }

    /// Returns the authenticated direct dependency edges in source order.
    #[must_use]
    pub const fn direct_dependencies(&self) -> &[DirectDependencyRoute] {
        &self.direct_dependencies
    }

    /// Returns the explicit cross-family declaration order.
    #[must_use]
    pub const fn declaration_order(&self) -> &[ResolvedDeclarationIndex] {
        &self.declaration_order
    }

    /// Returns local interface declarations in category-local source order.
    #[must_use]
    pub const fn interfaces(&self) -> &[ResolvedInterfaceDeclaration] {
        &self.interfaces
    }

    /// Returns local implementation declarations in category-local source order.
    #[must_use]
    pub const fn implementations(&self) -> &[ResolvedImplementation] {
        &self.implementations
    }

    /// Returns local definitions in source order.
    #[must_use]
    pub fn definitions(&self) -> &[ResolvedDefinition] {
        &self.definitions
    }

    fn take_interfaces(&mut self) -> Box<[ResolvedInterfaceDeclaration]> {
        std::mem::take(&mut self.interfaces)
    }

    /// Moves resolved globals across a successful checker-owned transition.
    pub(crate) fn take_definitions(&mut self) -> Box<[ResolvedDefinition]> {
        std::mem::take(&mut self.definitions)
    }

    /// Moves resolved implementation bodies across a successful checker-owned transition.
    pub(crate) fn take_implementations(&mut self) -> Box<[ResolvedImplementation]> {
        std::mem::take(&mut self.implementations)
    }

    /// Returns the unchecked set of local declarations eligible for export.
    #[must_use]
    pub const fn export_candidate(&self) -> &ResolvedExportCandidate {
        &self.export_candidate
    }

    /// Returns the complete accepted module span.
    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }

    #[cfg(test)]
    pub(crate) fn replace_local_constructor_payload_for_test(
        &mut self,
        id: ConstructorId,
        payload: Type,
    ) -> bool {
        let payload = IterativeTypeOwner::new(payload);
        let Some(registry) = Arc::get_mut(&mut self.registry) else {
            return false;
        };
        let Some(constructor) = registry
            .constructors
            .iter_mut()
            .find(|constructor| constructor.id == id)
        else {
            return false;
        };
        if let Some(displaced) = constructor.payload.replace(payload.into_inner()) {
            discard_type_iteratively(displaced);
        }
        true
    }
}

impl Drop for ResolvedModuleParts {
    fn drop(&mut self) {
        for interface in self.interfaces.drain(..) {
            discard_resolved_interface_iteratively(interface);
        }
        for definition in self.definitions.drain(..) {
            discard_resolved_definition_iteratively(definition);
        }
        for implementation in self.implementations.drain(..) {
            discard_resolved_implementation_iteratively(implementation);
        }
    }
}

impl Drop for ResolvedModule {
    fn drop(&mut self) {
        for interface in self.take_interfaces().into_vec() {
            discard_resolved_interface_iteratively(interface);
        }
        for definition in self.take_definitions().into_vec() {
            discard_resolved_definition_iteratively(definition);
        }
        for implementation in self.take_implementations().into_vec() {
            discard_resolved_implementation_iteratively(implementation);
        }
    }
}

/// One fully checked local global scheme retained for linking and exports.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedGlobalScheme {
    /// Stable binder identity.
    pub binder: BinderId,
    /// Source declaration spelling.
    pub spelling: String,
    /// Closed, inference-free constrained rank-1 scheme.
    pub scheme: ConstrainedScheme,
    /// Causal declaration provenance.
    pub origin: Origin,
}

/// One resolved global definition admitted by successful body checking.
///
/// The private source field prevents callers from presenting an unchecked
/// [`ResolvedDefinition`] at the checked-module boundary.
#[derive(Debug)]
pub struct CheckedDefinition {
    source: Option<ResolvedDefinition>,
}

impl CheckedDefinition {
    pub(crate) fn new(source: ResolvedDefinition) -> Self {
        Self {
            source: Some(source),
        }
    }

    /// Returns the checked definition family without granting mutation.
    #[must_use]
    pub fn kind(&self) -> &ResolvedDefinitionKind {
        &self
            .source
            .as_ref()
            .expect("a checked definition retains its source")
            .kind
    }

    /// Returns the complete checked definition span.
    #[must_use]
    pub fn span(&self) -> Span {
        self.source
            .as_ref()
            .expect("a checked definition retains its source")
            .span
    }
}

impl Drop for CheckedDefinition {
    fn drop(&mut self) {
        if let Some(source) = self.source.take() {
            discard_resolved_definition_iteratively(source);
        }
    }
}

/// One resolved implementation body admitted by successful body checking.
///
/// Body-free checked implementation facts remain separate because imports may
/// retain them without retaining this defining source body.
#[derive(Debug)]
pub struct CheckedImplementationBody {
    source: Option<ResolvedImplementation>,
}

impl CheckedImplementationBody {
    pub(crate) fn new(source: ResolvedImplementation) -> Self {
        Self {
            source: Some(source),
        }
    }

    /// Returns the stable identity of the checked implementation body.
    #[must_use]
    pub fn id(&self) -> ImplId {
        self.source
            .as_ref()
            .expect("a checked implementation body retains its source")
            .id
    }

    /// Returns the complete checked implementation span.
    #[must_use]
    pub fn span(&self) -> Span {
        self.source
            .as_ref()
            .expect("a checked implementation body retains its source")
            .span
    }

    /// Returns the checked source method groups without exposing an unchecked wrapper path.
    #[must_use]
    pub fn method_groups(&self) -> &[ResolvedImplementationMethodGroup] {
        &self
            .source
            .as_ref()
            .expect("a checked implementation body retains its source")
            .method_groups
    }

    pub(crate) fn source(&self) -> &ResolvedImplementation {
        self.source
            .as_ref()
            .expect("a checked implementation body retains its source")
    }
}

impl Drop for CheckedImplementationBody {
    fn drop(&mut self) {
        if let Some(source) = self.source.take() {
            discard_resolved_implementation_iteratively(source);
        }
    }
}

/// One authenticated module-to-dependency edge in an implementation route.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ImplementationRouteHop {
    /// Module whose import contains this edge.
    pub from: ModuleId,
    /// Canonical direct dependency selected by the import.
    pub to: ModuleId,
    /// Exact import declaration that authorizes the edge.
    pub import_span: Span,
}

/// Flat authorization route for one implementation fact.
///
/// Allocation-owning routes require an explicitly budgeted copy.
///
/// ```compile_fail
/// fn require_clone<T: Clone>() {}
/// require_clone::<ash::resolved::ImplementationAuthorization>();
/// ```
#[derive(Debug, Eq, PartialEq)]
pub struct ImplementationAuthorization {
    hops: Box<[ImplementationRouteHop]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ImplementationRouteRank {
    dependency_summary_order: usize,
    import_source_order: usize,
    selector_source_order: usize,
}

impl ImplementationRouteRank {
    pub(crate) const fn new(
        dependency_summary_order: usize,
        import_source_order: usize,
        selector_source_order: usize,
    ) -> Self {
        Self {
            dependency_summary_order,
            import_source_order,
            selector_source_order,
        }
    }
}

impl ImplementationAuthorization {
    pub(crate) fn local() -> Self {
        Self { hops: Box::new([]) }
    }

    pub(crate) fn from_hops(hops: Vec<ImplementationRouteHop>) -> Self {
        Self {
            hops: hops.into_boxed_slice(),
        }
    }

    pub(crate) fn prepend(
        from: ModuleId,
        to: ModuleId,
        import_span: Span,
        suffix: &Self,
        budget: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<Self, ()> {
        let capacity = suffix.hops.len().checked_add(1).ok_or(())?;
        budget.charge(capacity)?;
        let mut hops = Vec::new();
        hops.try_reserve_exact(capacity).map_err(|_| ())?;
        hops.push(ImplementationRouteHop {
            from,
            to,
            import_span,
        });
        hops.extend_from_slice(&suffix.hops);
        Ok(Self::from_hops(hops))
    }

    pub(crate) fn clone_with_budget(
        &self,
        budget: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<Self, ()> {
        budget.charge(self.hops.len())?;
        let mut hops = Vec::new();
        hops.try_reserve_exact(self.hops.len()).map_err(|_| ())?;
        hops.extend_from_slice(&self.hops);
        Ok(Self::from_hops(hops))
    }

    pub(crate) fn is_well_formed_for(
        &self,
        publisher: ModuleId,
        fact: &CheckedImplementationFact,
        budget: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<bool, ()> {
        let route_work = self.hops.len().checked_add(fact.methods.len()).ok_or(())?;
        budget.charge(route_work)?;
        if self.hops.is_empty() {
            return Ok(publisher == fact.id.module()
                && fact.methods.iter().all(|method| {
                    method.id.implementation() == fact.id
                        && method.binder.module() == Some(fact.id.module())
                }));
        }
        budget.charge(1)?;
        let mut visited = HashSet::new();
        visited
            .try_reserve(self.hops.len().checked_add(1).ok_or(())?)
            .map_err(|_| ())?;
        visited.insert(publisher);
        let mut expected_from = publisher;
        for hop in &self.hops {
            if hop.from != expected_from || hop.from == hop.to || !visited.insert(hop.to) {
                return Ok(false);
            }
            expected_from = hop.to;
        }
        Ok(expected_from == fact.id.module()
            && fact.methods.iter().all(|method| {
                method.id.implementation() == fact.id
                    && method.binder.module() == Some(fact.id.module())
            }))
    }

    pub(crate) fn candidate_precedes(
        &self,
        candidate_rank: ImplementationRouteRank,
        existing: &Self,
        existing_rank: ImplementationRouteRank,
        budget: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<bool, ()> {
        match self.hops.len().cmp(&existing.hops.len()) {
            Ordering::Less => return Ok(true),
            Ordering::Greater => return Ok(false),
            Ordering::Equal => {}
        }
        match candidate_rank.cmp(&existing_rank) {
            Ordering::Less => return Ok(true),
            Ordering::Greater => return Ok(false),
            Ordering::Equal => {}
        }
        Ok(compare_hop_sequences(&self.hops, &existing.hops, budget)? == Ordering::Less)
    }

    /// Returns the ordered route from the selecting module to the defining module.
    #[must_use]
    pub const fn hops(&self) -> &[ImplementationRouteHop] {
        &self.hops
    }

    /// Returns whether this is a local implementation route.
    #[must_use]
    pub const fn is_local(&self) -> bool {
        self.hops.is_empty()
    }
}

fn hop_key(hop: &ImplementationRouteHop) -> (ModuleId, ModuleId, u32, u32) {
    (
        hop.from,
        hop.to,
        hop.import_span.range().start(),
        hop.import_span.range().end(),
    )
}

fn compare_hop_sequences(
    left: &[ImplementationRouteHop],
    right: &[ImplementationRouteHop],
    budget: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<Ordering, ()> {
    for (left_hop, right_hop) in left.iter().zip(right) {
        budget.charge(1)?;
        match hop_key(left_hop).cmp(&hop_key(right_hop)) {
            Ordering::Equal => {}
            ordering => return Ok(ordering),
        }
    }
    Ok(left.len().cmp(&right.len()))
}

/// Compatibility view of how one implementation entered a checked module.
///
/// The full transitive route is available through
/// [`AvailableImplementation::authorization`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImplementationRoute {
    /// The implementation is declared by the checked module.
    Local,
    /// The implementation first arrived through this direct import occurrence.
    DirectImport {
        /// Canonical identity of the direct dependency that published the implementation.
        direct_dependency: ModuleId,
        /// Source import occurrence that first made the implementation available.
        available_at: Span,
    },
}

/// One implementation in deterministic effective-environment order.
///
/// The allocation-owning authorization route prevents implicit copies.
///
/// ```compile_fail
/// fn require_clone<T: Clone>() {}
/// require_clone::<ash::resolved::AvailableImplementation>();
/// ```
#[derive(Debug, Eq, PartialEq)]
pub struct AvailableImplementation {
    id: ImplId,
    authorization: ImplementationAuthorization,
}

/// One body-free public implementation authorization retained through linking.
///
/// The defining implementation body and method facts remain owned only by the
/// defining module group. Allocation-owning routes are moved into this record
/// and cannot be copied implicitly.
///
/// ```compile_fail
/// fn require_clone<T: Clone>() {}
/// require_clone::<ash::resolved::PublicImplementationAuthorization>();
/// ```
#[derive(Debug, Eq, PartialEq)]
pub struct PublicImplementationAuthorization {
    id: ImplId,
    authorization: ImplementationAuthorization,
}

impl PublicImplementationAuthorization {
    /// Returns the stable defining implementation identity.
    #[must_use]
    pub const fn id(&self) -> ImplId {
        self.id
    }

    /// Returns the complete route published by this module.
    #[must_use]
    pub const fn authorization(&self) -> &ImplementationAuthorization {
        &self.authorization
    }
}

impl AvailableImplementation {
    pub(crate) fn local(id: ImplId) -> Self {
        Self {
            id,
            authorization: ImplementationAuthorization::local(),
        }
    }

    pub(crate) const fn imported(id: ImplId, authorization: ImplementationAuthorization) -> Self {
        Self { id, authorization }
    }

    /// Returns the stable implementation identity.
    #[must_use]
    pub const fn id(&self) -> ImplId {
        self.id
    }

    /// Returns the complete flat authorization route by reference.
    #[must_use]
    pub const fn authorization(&self) -> &ImplementationAuthorization {
        &self.authorization
    }

    /// Returns the local or first-direct-import compatibility view.
    #[must_use]
    pub fn route(&self) -> ImplementationRoute {
        let Some(first) = self.authorization.hops.first() else {
            return ImplementationRoute::Local;
        };
        ImplementationRoute::DirectImport {
            direct_dependency: first.to,
            available_at: first.import_span,
        }
    }
}

/// One successfully checked declarations-only module.
#[derive(Debug)]
pub struct CheckedModule {
    module: ModuleId,
    registry: Arc<ResolvedRegistry>,
    direct_dependencies: Box<[DirectDependencyRoute]>,
    declaration_order: Box<[ResolvedDeclarationIndex]>,
    interfaces: Box<[ResolvedInterfaceDeclaration]>,
    implementations: Box<[CheckedImplementationBody]>,
    definitions: Box<[CheckedDefinition]>,
    available_implementations: Box<[AvailableImplementation]>,
    schemes: Vec<CheckedGlobalScheme>,
    checked_interfaces: Box<[CheckedInterface]>,
    checked_implementations: Box<[CheckedImplementation]>,
    interface_facts: Box<[CheckedInterfaceFact]>,
    implementation_facts: Box<[CheckedImplementationFact]>,
    exports: ExportSummary,
    span: Span,
}

pub(crate) struct CheckedModuleParts {
    pub definitions: Box<[CheckedDefinition]>,
    pub implementations: Box<[CheckedImplementationBody]>,
    pub available_implementations: Box<[AvailableImplementation]>,
    pub schemes: Vec<CheckedGlobalScheme>,
    pub checked_interfaces: Box<[CheckedInterface]>,
    pub checked_implementations: Box<[CheckedImplementation]>,
    pub interface_facts: Box<[CheckedInterfaceFact]>,
    pub implementation_facts: Box<[CheckedImplementationFact]>,
    pub exports: ExportSummary,
}

impl CheckedModule {
    pub(crate) fn new(mut resolved: ResolvedModule, parts: CheckedModuleParts) -> Self {
        assert!(
            resolved.definitions.is_empty() && resolved.implementations.is_empty(),
            "checked module construction requires checker-owned body wrappers"
        );
        Self {
            module: resolved.module,
            registry: Arc::clone(&resolved.registry),
            direct_dependencies: std::mem::take(&mut resolved.direct_dependencies),
            declaration_order: std::mem::take(&mut resolved.declaration_order),
            interfaces: std::mem::take(&mut resolved.interfaces),
            implementations: parts.implementations,
            definitions: parts.definitions,
            available_implementations: parts.available_implementations,
            schemes: parts.schemes,
            checked_interfaces: parts.checked_interfaces,
            checked_implementations: parts.checked_implementations,
            interface_facts: parts.interface_facts,
            implementation_facts: parts.implementation_facts,
            exports: parts.exports,
            span: resolved.span,
        }
    }

    /// Returns the stable defining module identity.
    #[must_use]
    pub const fn module(&self) -> ModuleId {
        self.module
    }

    /// Returns the module's full local registry for final linking.
    #[must_use]
    pub const fn registry(&self) -> &Arc<ResolvedRegistry> {
        &self.registry
    }

    /// Returns the resolver-authenticated direct dependency edges in source order.
    #[must_use]
    pub const fn direct_dependencies(&self) -> &[DirectDependencyRoute] {
        &self.direct_dependencies
    }

    /// Returns local definitions in source order.
    #[must_use]
    pub fn definitions(&self) -> &[CheckedDefinition] {
        &self.definitions
    }

    /// Returns local interfaces retained for interface checking.
    #[must_use]
    pub const fn interfaces(&self) -> &[ResolvedInterfaceDeclaration] {
        &self.interfaces
    }

    /// Returns local implementations retained for interface checking.
    #[must_use]
    pub const fn implementations(&self) -> &[CheckedImplementationBody] {
        &self.implementations
    }

    /// Returns the effective implementation environment in deterministic order.
    #[must_use]
    pub const fn available_implementations(&self) -> &[AvailableImplementation] {
        &self.available_implementations
    }

    /// Returns checked local schemes in definition order.
    #[must_use]
    pub fn schemes(&self) -> &[CheckedGlobalScheme] {
        &self.schemes
    }

    /// Returns checked local interface authentication records in source order.
    #[must_use]
    pub const fn checked_interfaces(&self) -> &[CheckedInterface] {
        &self.checked_interfaces
    }

    /// Returns checked local implementation facts in declaration order.
    #[must_use]
    pub const fn checked_implementations(&self) -> &[CheckedImplementation] {
        &self.checked_implementations
    }

    /// Returns checked local interface semantic facts in declaration order.
    #[must_use]
    pub const fn interface_facts(&self) -> &[CheckedInterfaceFact] {
        &self.interface_facts
    }

    /// Returns checked local implementation semantic facts in declaration order.
    #[must_use]
    pub const fn implementation_facts(&self) -> &[CheckedImplementationFact] {
        &self.implementation_facts
    }

    /// Returns the immutable body-free dependency summary.
    #[must_use]
    pub const fn exports(&self) -> &ExportSummary {
        &self.exports
    }

    /// Consumes the checked module and retains only its immutable body-free summary.
    #[must_use]
    pub fn into_exports(mut self) -> ExportSummary {
        let module = self.module;
        std::mem::replace(&mut self.exports, ExportSummary::empty(module))
    }

    /// Returns the complete source span.
    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }

    pub(crate) fn into_group(
        mut self,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<ResolvedModuleGroup, ()> {
        let public_implementations = self
            .exports
            .take_public_implementation_authorizations(constraint_work)?;
        Ok(ResolvedModuleGroup {
            module: self.module,
            direct_dependencies: std::mem::take(&mut self.direct_dependencies),
            declaration_order: std::mem::take(&mut self.declaration_order),
            interfaces: std::mem::take(&mut self.interfaces),
            implementations: std::mem::take(&mut self.implementations),
            definitions: std::mem::take(&mut self.definitions),
            available_implementations: std::mem::take(&mut self.available_implementations),
            public_implementations,
            schemes: std::mem::take(&mut self.schemes).into_boxed_slice(),
            checked_interfaces: std::mem::take(&mut self.checked_interfaces),
            checked_implementations: std::mem::take(&mut self.checked_implementations),
            interface_facts: std::mem::take(&mut self.interface_facts),
            implementation_facts: std::mem::take(&mut self.implementation_facts),
            span: self.span,
        })
    }
}

impl Drop for CheckedModule {
    fn drop(&mut self) {
        for interface in std::mem::take(&mut self.interfaces).into_vec() {
            discard_resolved_interface_iteratively(interface);
        }
        for checked in self.schemes.drain(..) {
            drop(checked.scheme);
            discard_origin_iteratively(checked.origin);
        }
    }
}

/// One checked module-local recursive group retained for final lowering.
#[derive(Debug)]
pub struct ResolvedModuleGroup {
    module: ModuleId,
    direct_dependencies: Box<[DirectDependencyRoute]>,
    declaration_order: Box<[ResolvedDeclarationIndex]>,
    interfaces: Box<[ResolvedInterfaceDeclaration]>,
    implementations: Box<[CheckedImplementationBody]>,
    definitions: Box<[CheckedDefinition]>,
    available_implementations: Box<[AvailableImplementation]>,
    public_implementations: Box<[PublicImplementationAuthorization]>,
    schemes: Box<[CheckedGlobalScheme]>,
    checked_interfaces: Box<[CheckedInterface]>,
    checked_implementations: Box<[CheckedImplementation]>,
    interface_facts: Box<[CheckedInterfaceFact]>,
    implementation_facts: Box<[CheckedImplementationFact]>,
    span: Span,
}

impl ResolvedModuleGroup {
    /// Returns the stable canonical module identity.
    #[must_use]
    pub const fn module(&self) -> ModuleId {
        self.module
    }

    /// Returns the resolver-authenticated direct dependency edges in source order.
    #[must_use]
    pub const fn direct_dependencies(&self) -> &[DirectDependencyRoute] {
        &self.direct_dependencies
    }

    /// Returns the cross-family declaration order within this module.
    #[must_use]
    pub const fn declaration_order(&self) -> &[ResolvedDeclarationIndex] {
        &self.declaration_order
    }

    /// Returns resolved local interfaces retained for checked lowering.
    #[must_use]
    pub const fn interfaces(&self) -> &[ResolvedInterfaceDeclaration] {
        &self.interfaces
    }

    /// Returns checked local implementation bodies in declaration order.
    #[must_use]
    pub const fn implementations(&self) -> &[CheckedImplementationBody] {
        &self.implementations
    }

    /// Returns checked local definitions in source order.
    #[must_use]
    pub const fn definitions(&self) -> &[CheckedDefinition] {
        &self.definitions
    }

    /// Returns the effective implementation environment in deterministic order.
    #[must_use]
    pub const fn available_implementations(&self) -> &[AvailableImplementation] {
        &self.available_implementations
    }

    /// Returns lightweight public implementation authorizations in summary order.
    #[must_use]
    pub const fn public_implementation_authorizations(
        &self,
    ) -> &[PublicImplementationAuthorization] {
        &self.public_implementations
    }

    /// Returns checked global schemes in definition order.
    #[must_use]
    pub const fn schemes(&self) -> &[CheckedGlobalScheme] {
        &self.schemes
    }

    /// Returns local interface authentication records in source order.
    #[must_use]
    pub const fn checked_interfaces(&self) -> &[CheckedInterface] {
        &self.checked_interfaces
    }

    /// Returns checked local implementations in declaration order.
    #[must_use]
    pub const fn checked_implementations(&self) -> &[CheckedImplementation] {
        &self.checked_implementations
    }

    /// Returns checked local interface semantic facts in declaration order.
    #[must_use]
    pub const fn interface_facts(&self) -> &[CheckedInterfaceFact] {
        &self.interface_facts
    }

    /// Returns checked local implementation semantic facts in declaration order.
    #[must_use]
    pub const fn implementation_facts(&self) -> &[CheckedImplementationFact] {
        &self.implementation_facts
    }

    /// Returns the complete defining source span.
    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }
}

impl Drop for ResolvedModuleGroup {
    fn drop(&mut self) {
        for interface in std::mem::take(&mut self.interfaces).into_vec() {
            discard_resolved_interface_iteratively(interface);
        }
        for checked in std::mem::take(&mut self.schemes).into_vec() {
            drop(checked.scheme);
            discard_origin_iteratively(checked.origin);
        }
    }
}

/// Dependency-ordered checked modules ready for one final Core lowering.
#[derive(Debug)]
pub struct ResolvedModuleProgram {
    registry: Arc<ResolvedRegistry>,
    groups: Box<[ResolvedModuleGroup]>,
    entry: ModuleId,
    result: ResolvedExpr,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum LinkedCarrierMutationForTest {
    NominalParameterKind(usize),
    ConstructorIdentity,
    ConstructorOrdinal,
    DefiningModule,
    GlobalRegistryKind,
    GlobalSourceParameterIdentity,
    GlobalSourceParameterSpelling,
    GlobalSourceParameterOrigin,
    GlobalSourceNameIdentity,
    GlobalSourceNameSpelling,
    GlobalSourceNameOrigin,
    GlobalSourceKind,
    GlobalCheckedKind,
    GlobalSourceType,
    InterfaceTokenIdentity,
    InterfaceTokenSourceIndex,
    InterfaceSourceParameterIdentity,
    InterfaceSourceParameterSpelling,
    InterfaceSourceMethodIdentity,
    InterfaceSourceMethodSpelling,
    InterfaceSourceMethodSpan,
    InterfaceSourceMethodLocalBinder,
    InterfaceRegistryKind,
    InterfaceFactParameterIdentity,
    InterfaceFactParameterSpelling,
    InterfaceFactParameterKind,
    InterfaceHiddenFactParameterKind,
    InterfaceFactParameterOrigin,
    InterfaceMethodType,
    InterfaceMethodOrigin,
    ImplementationRegistryKind,
    ImplementationSourceParameterIdentity,
    ImplementationSourceParameterSpelling,
    ImplementationSourceParameterOrigin,
    ImplementationSourceKind,
    ImplementationFactKind,
    ImplementationOpaqueFactKind,
    ImplementationTokenIdentity,
    ImplementationTokenInterface,
    ImplementationTokenSourceIndex,
    ImplementationTokenMethod,
    ImplementationPrerequisite,
    ImplementationMethodRequirement,
    ImplementationMethodIdentity,
    ImplementationMethodBinder,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum LinkedGlobalParameterRowMutationForTest {
    Owner,
    ParameterIdentity,
    ParameterOrder,
    RowOrder,
    OwnerPosition,
    SurplusOwnerPosition,
    MissingRow,
    ExtraRow,
    DuplicateOwner,
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) enum CoreGlobalParameterRowMutationForTest {
    EmptyFirstRow,
    ReplaceFirstOwner(BinderId),
    ReplaceFirstParameter(TypeVariableId),
    DuplicateFirstParameter,
    DuplicateAcrossRows,
    SwapFirstOwnerPositions,
    DuplicateFirstOwner {
        filler: BinderId,
    },
    RemoveLastRow,
    AppendRow {
        owner: BinderId,
        parameter: TypeVariableId,
    },
    RemoveCanonicalParameter(TypeVariableId),
    AddSurplusPosition(BinderId),
}

impl ResolvedModuleProgram {
    pub(crate) fn new(
        registry: Arc<ResolvedRegistry>,
        groups: Box<[ResolvedModuleGroup]>,
        entry: ModuleId,
        result: ResolvedExpr,
    ) -> Self {
        Self {
            registry,
            groups,
            entry,
            result,
        }
    }

    /// Returns the combined full defining registries.
    #[must_use]
    pub const fn registry(&self) -> &Arc<ResolvedRegistry> {
        &self.registry
    }

    /// Returns dependency-ordered checked module groups.
    #[must_use]
    pub const fn groups(&self) -> &[ResolvedModuleGroup] {
        &self.groups
    }

    /// Returns the stable entry module identity.
    #[must_use]
    pub const fn entry(&self) -> ModuleId {
        self.entry
    }

    /// Returns the generated entry result expression.
    #[must_use]
    pub const fn result(&self) -> &ResolvedExpr {
        &self.result
    }

    #[cfg(test)]
    pub(crate) fn corrupt_linked_global_parameter_rows_for_test(
        &mut self,
        mutation: LinkedGlobalParameterRowMutationForTest,
    ) -> bool {
        let empty_owner = self
            .groups
            .iter()
            .flat_map(|group| group.schemes.iter())
            .find(|scheme| scheme.scheme.type_parameters.is_empty())
            .map(|scheme| scheme.binder);
        let Some(registry) = Arc::get_mut(&mut self.registry) else {
            return false;
        };

        match mutation {
            LinkedGlobalParameterRowMutationForTest::Owner => {
                let Some(owner) = empty_owner else {
                    return false;
                };
                let Some(original_owner) =
                    registry.global_parameter_rows.first().map(|row| row.owner)
                else {
                    return false;
                };
                let Some(position) = registry
                    .global_parameter_positions
                    .get(&original_owner)
                    .copied()
                else {
                    return false;
                };
                if position != 0 || registry.global_parameter_positions.contains_key(&owner) {
                    return false;
                }
                let removed = registry.global_parameter_positions.remove(&original_owner);
                debug_assert_eq!(removed, Some(position));
                registry.global_parameter_rows[position].owner = owner;
                let displaced = registry.global_parameter_positions.insert(owner, position);
                debug_assert!(displaced.is_none());
            }
            LinkedGlobalParameterRowMutationForTest::ParameterIdentity => {
                let Some((row_index, replacement)) =
                    registry.global_parameter_rows.iter().enumerate().find_map(
                        |(row_index, row)| {
                            let replaced = *row.parameters.first()?;
                            let replaced_kind = &registry.type_variables.get(&replaced)?.kind;
                            registry
                                .global_parameter_rows
                                .iter()
                                .flat_map(|candidate| candidate.parameters.iter().copied())
                                .find(|candidate| {
                                    !row.parameters.contains(candidate)
                                        && registry
                                            .type_variables
                                            .get(candidate)
                                            .is_some_and(|variable| variable.kind == *replaced_kind)
                                })
                                .map(|replacement| (row_index, replacement))
                        },
                    )
                else {
                    return false;
                };
                registry.global_parameter_rows[row_index].parameters[0] = replacement;
            }
            LinkedGlobalParameterRowMutationForTest::ParameterOrder => {
                let Some(row_index) = registry.global_parameter_rows.iter().position(|row| {
                    let [first, second, ..] = row.parameters.as_ref() else {
                        return false;
                    };
                    registry
                        .type_variables
                        .get(first)
                        .zip(registry.type_variables.get(second))
                        .is_some_and(|(first, second)| first.kind == second.kind)
                }) else {
                    return false;
                };
                registry.global_parameter_rows[row_index]
                    .parameters
                    .swap(0, 1);
            }
            LinkedGlobalParameterRowMutationForTest::RowOrder => {
                let [first, second, ..] = registry.global_parameter_rows.as_ref() else {
                    return false;
                };
                let (first_owner, second_owner) = (first.owner, second.owner);
                let Some(first_position) = registry
                    .global_parameter_positions
                    .get(&first_owner)
                    .copied()
                else {
                    return false;
                };
                let Some(second_position) = registry
                    .global_parameter_positions
                    .get(&second_owner)
                    .copied()
                else {
                    return false;
                };
                if first_position != 0 || second_position != 1 {
                    return false;
                }
                registry
                    .global_parameter_rows
                    .swap(first_position, second_position);
                let displaced = registry
                    .global_parameter_positions
                    .insert(first_owner, second_position);
                debug_assert_eq!(displaced, Some(first_position));
                let displaced = registry
                    .global_parameter_positions
                    .insert(second_owner, first_position);
                debug_assert_eq!(displaced, Some(second_position));
            }
            LinkedGlobalParameterRowMutationForTest::OwnerPosition => {
                let [first, second, ..] = registry.global_parameter_rows.as_ref() else {
                    return false;
                };
                let (first_owner, second_owner) = (first.owner, second.owner);
                let Some(first_position) = registry
                    .global_parameter_positions
                    .get(&first_owner)
                    .copied()
                else {
                    return false;
                };
                let Some(second_position) = registry
                    .global_parameter_positions
                    .get(&second_owner)
                    .copied()
                else {
                    return false;
                };
                registry
                    .global_parameter_positions
                    .insert(first_owner, second_position);
                registry
                    .global_parameter_positions
                    .insert(second_owner, first_position);
            }
            LinkedGlobalParameterRowMutationForTest::SurplusOwnerPosition => {
                let Some(owner) = empty_owner else {
                    return false;
                };
                if registry.global_parameter_rows.is_empty()
                    || registry.global_parameter_positions.contains_key(&owner)
                {
                    return false;
                }
                registry.global_parameter_positions.insert(owner, 0);
            }
            LinkedGlobalParameterRowMutationForTest::MissingRow => {
                let mut rows = std::mem::take(&mut registry.global_parameter_rows).into_vec();
                let Some(removed) = rows.pop() else {
                    return false;
                };
                registry.global_parameter_positions.remove(&removed.owner);
                registry.global_parameter_rows = rows.into_boxed_slice();
            }
            LinkedGlobalParameterRowMutationForTest::ExtraRow => {
                let Some(owner) = empty_owner else {
                    return false;
                };
                let Some(parameter) = registry
                    .global_parameter_rows
                    .first()
                    .and_then(|row| row.parameters.first())
                    .copied()
                else {
                    return false;
                };
                let mut rows = std::mem::take(&mut registry.global_parameter_rows).into_vec();
                let position = rows.len();
                rows.push(ResolvedGlobalParameterRow {
                    owner,
                    parameters: vec![parameter].into_boxed_slice(),
                });
                registry.global_parameter_positions.insert(owner, position);
                registry.global_parameter_rows = rows.into_boxed_slice();
            }
            LinkedGlobalParameterRowMutationForTest::DuplicateOwner => {
                let [first, second, ..] = registry.global_parameter_rows.as_ref() else {
                    return false;
                };
                let (first_owner, second_owner) = (first.owner, second.owner);
                if first_owner == second_owner {
                    return false;
                }
                let Some(first_position) = registry
                    .global_parameter_positions
                    .get(&first_owner)
                    .copied()
                else {
                    return false;
                };
                let Some(second_position) = registry
                    .global_parameter_positions
                    .get(&second_owner)
                    .copied()
                else {
                    return false;
                };
                if first_position != 0 || second_position != 1 {
                    return false;
                }
                let removed = registry.global_parameter_positions.remove(&second_owner);
                debug_assert_eq!(removed, Some(second_position));
                registry.global_parameter_rows[second_position].owner = first_owner;
            }
        }
        true
    }

    #[cfg(test)]
    pub(crate) fn corrupt_linked_carrier_for_test(
        &mut self,
        module: ModuleId,
        mutation: LinkedCarrierMutationForTest,
    ) -> bool {
        fn wrap_origin(origin: &mut Origin) {
            let placeholder = Origin::Source(origin.primary_span());
            let cause = std::mem::replace(origin, placeholder);
            *origin = Origin::Generated {
                cause: Box::new(cause),
                reason: crate::source::GeneratedReason::ConstantFolding,
            };
        }

        let Some(group_index) = self.groups.iter().position(|group| group.module == module) else {
            return false;
        };
        match mutation {
            LinkedCarrierMutationForTest::NominalParameterKind(ordinal) => {
                let Some(registry) = Arc::get_mut(&mut self.registry) else {
                    return false;
                };
                let Some(owner) = registry.nominals.get(ordinal).map(|nominal| nominal.id) else {
                    return false;
                };
                let Some(parameter) = registry
                    .nominal_parameters
                    .get_mut(&owner)
                    .and_then(|parameters| parameters.first_mut())
                else {
                    return false;
                };
                drop(std::mem::replace(&mut parameter.kind, Kind::Type));
                true
            }
            LinkedCarrierMutationForTest::ConstructorIdentity => {
                let Some(registry) = Arc::get_mut(&mut self.registry) else {
                    return false;
                };
                let Some(constructor) = registry.constructors.first_mut() else {
                    return false;
                };
                constructor.id = ConstructorId::new(constructor.owner, u32::MAX);
                true
            }
            LinkedCarrierMutationForTest::ConstructorOrdinal => {
                let Some(registry) = Arc::get_mut(&mut self.registry) else {
                    return false;
                };
                let Some(nominal) = registry
                    .nominals
                    .iter_mut()
                    .find(|nominal| nominal.constructors.len() >= 2)
                else {
                    return false;
                };
                nominal.constructors.swap(0, 1);
                true
            }
            LinkedCarrierMutationForTest::DefiningModule => {
                self.groups[group_index].module = ModuleId::new(u32::MAX - 1);
                true
            }
            LinkedCarrierMutationForTest::GlobalRegistryKind
            | LinkedCarrierMutationForTest::GlobalSourceParameterIdentity
            | LinkedCarrierMutationForTest::GlobalSourceParameterSpelling
            | LinkedCarrierMutationForTest::GlobalSourceParameterOrigin
            | LinkedCarrierMutationForTest::GlobalSourceNameIdentity
            | LinkedCarrierMutationForTest::GlobalSourceNameSpelling
            | LinkedCarrierMutationForTest::GlobalSourceNameOrigin
            | LinkedCarrierMutationForTest::GlobalSourceKind
            | LinkedCarrierMutationForTest::GlobalCheckedKind
            | LinkedCarrierMutationForTest::GlobalSourceType => {
                let Some(definition_index) = self.groups[group_index]
                    .schemes
                    .iter()
                    .position(|scheme| scheme.spelling == "relay")
                else {
                    return false;
                };
                let Some(parameter) = self.groups[group_index].schemes[definition_index]
                    .scheme
                    .type_parameters
                    .first()
                    .map(|pair| pair.0)
                else {
                    return false;
                };
                match mutation {
                    LinkedCarrierMutationForTest::GlobalRegistryKind => {
                        let Some(registry) = Arc::get_mut(&mut self.registry) else {
                            return false;
                        };
                        let Some(parameter) = registry.type_variables.get_mut(&parameter) else {
                            return false;
                        };
                        drop(std::mem::replace(&mut parameter.kind, Kind::Type));
                    }
                    LinkedCarrierMutationForTest::GlobalCheckedKind => {
                        let parameter = &mut self.groups[group_index].schemes[definition_index]
                            .scheme
                            .type_parameters[0];
                        drop(std::mem::replace(&mut parameter.1, Kind::Type));
                    }
                    LinkedCarrierMutationForTest::GlobalSourceParameterIdentity
                    | LinkedCarrierMutationForTest::GlobalSourceParameterSpelling
                    | LinkedCarrierMutationForTest::GlobalSourceParameterOrigin
                    | LinkedCarrierMutationForTest::GlobalSourceNameIdentity
                    | LinkedCarrierMutationForTest::GlobalSourceNameSpelling
                    | LinkedCarrierMutationForTest::GlobalSourceNameOrigin
                    | LinkedCarrierMutationForTest::GlobalSourceKind
                    | LinkedCarrierMutationForTest::GlobalSourceType => {
                        let Some(source) = self.groups[group_index].definitions[definition_index]
                            .source
                            .as_mut()
                        else {
                            return false;
                        };
                        let ResolvedDefinitionKind::Equational(global) = &mut source.kind else {
                            return false;
                        };
                        match mutation {
                            LinkedCarrierMutationForTest::GlobalSourceParameterIdentity => {
                                let Some(parameter) = global.interface.type_parameters.first_mut()
                                else {
                                    return false;
                                };
                                parameter.id = TypeVariableId::resolved(module, u32::MAX);
                            }
                            LinkedCarrierMutationForTest::GlobalSourceParameterSpelling => {
                                let Some(parameter) = global.interface.type_parameters.first_mut()
                                else {
                                    return false;
                                };
                                parameter.spelling.push_str("-forged");
                            }
                            LinkedCarrierMutationForTest::GlobalSourceParameterOrigin => {
                                let Some(parameter) = global.interface.type_parameters.first_mut()
                                else {
                                    return false;
                                };
                                wrap_origin(&mut parameter.origin);
                            }
                            LinkedCarrierMutationForTest::GlobalSourceNameIdentity => {
                                global.interface.name.id = BinderId::resolved(module, u32::MAX);
                            }
                            LinkedCarrierMutationForTest::GlobalSourceNameSpelling => {
                                global.interface.name.spelling.push_str("-forged");
                            }
                            LinkedCarrierMutationForTest::GlobalSourceNameOrigin => {
                                wrap_origin(&mut global.interface.name.origin);
                            }
                            LinkedCarrierMutationForTest::GlobalSourceKind => {
                                let Some(parameter) = global.interface.type_parameters.first_mut()
                                else {
                                    return false;
                                };
                                drop(std::mem::replace(&mut parameter.kind, Kind::Type));
                            }
                            LinkedCarrierMutationForTest::GlobalSourceType => {
                                discard_type_iteratively(std::mem::replace(
                                    &mut global.interface.annotation.ty,
                                    Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                                ));
                            }
                            _ => unreachable!(),
                        }
                    }
                    _ => unreachable!(),
                }
                true
            }
            LinkedCarrierMutationForTest::InterfaceTokenIdentity
            | LinkedCarrierMutationForTest::InterfaceTokenSourceIndex
            | LinkedCarrierMutationForTest::InterfaceSourceParameterIdentity
            | LinkedCarrierMutationForTest::InterfaceSourceParameterSpelling
            | LinkedCarrierMutationForTest::InterfaceSourceMethodIdentity
            | LinkedCarrierMutationForTest::InterfaceSourceMethodSpelling
            | LinkedCarrierMutationForTest::InterfaceSourceMethodSpan
            | LinkedCarrierMutationForTest::InterfaceSourceMethodLocalBinder
            | LinkedCarrierMutationForTest::InterfaceRegistryKind
            | LinkedCarrierMutationForTest::InterfaceFactParameterIdentity
            | LinkedCarrierMutationForTest::InterfaceFactParameterSpelling
            | LinkedCarrierMutationForTest::InterfaceFactParameterKind
            | LinkedCarrierMutationForTest::InterfaceHiddenFactParameterKind
            | LinkedCarrierMutationForTest::InterfaceFactParameterOrigin
            | LinkedCarrierMutationForTest::InterfaceMethodType
            | LinkedCarrierMutationForTest::InterfaceMethodOrigin => {
                match mutation {
                    LinkedCarrierMutationForTest::InterfaceTokenIdentity => {
                        let Some(token) = self.groups[group_index].checked_interfaces.first_mut()
                        else {
                            return false;
                        };
                        token.id = InterfaceId::new(module, u32::MAX);
                    }
                    LinkedCarrierMutationForTest::InterfaceTokenSourceIndex => {
                        let Some(token) = self.groups[group_index].checked_interfaces.first_mut()
                        else {
                            return false;
                        };
                        token.source_index = usize::MAX;
                    }
                    LinkedCarrierMutationForTest::InterfaceSourceParameterIdentity => {
                        let Some(interface) = self.groups[group_index].interfaces.first_mut()
                        else {
                            return false;
                        };
                        interface.parameter.id = TypeVariableId::resolved(module, u32::MAX);
                    }
                    LinkedCarrierMutationForTest::InterfaceSourceParameterSpelling => {
                        let Some(interface) = self.groups[group_index].interfaces.first_mut()
                        else {
                            return false;
                        };
                        interface.parameter.spelling.push_str("-forged");
                    }
                    LinkedCarrierMutationForTest::InterfaceSourceMethodIdentity => {
                        let Some(interface) = self.groups[group_index].interfaces.first_mut()
                        else {
                            return false;
                        };
                        let Some(method) = interface.methods.first_mut() else {
                            return false;
                        };
                        method.id = MethodId::new(interface.id, u32::MAX);
                    }
                    LinkedCarrierMutationForTest::InterfaceSourceMethodSpelling => {
                        let Some(method) = self.groups[group_index]
                            .interfaces
                            .first_mut()
                            .and_then(|interface| interface.methods.first_mut())
                        else {
                            return false;
                        };
                        method.spelling.push_str("-forged");
                    }
                    LinkedCarrierMutationForTest::InterfaceSourceMethodSpan => {
                        let Some(interface) = self.groups[group_index].interfaces.first_mut()
                        else {
                            return false;
                        };
                        let replacement = interface.span;
                        let Some(method) = interface.methods.first_mut() else {
                            return false;
                        };
                        method.span = replacement;
                    }
                    LinkedCarrierMutationForTest::InterfaceSourceMethodLocalBinder => {
                        let Some(method) = self.groups[group_index]
                            .interfaces
                            .first_mut()
                            .and_then(|interface| interface.methods.first_mut())
                        else {
                            return false;
                        };
                        method.type_parameters = Box::new([ResolvedTypeVariable {
                            id: TypeVariableId::resolved(module, u32::MAX),
                            spelling: "Forged".to_owned(),
                            kind: Kind::Type,
                            origin: Origin::Source(method.span),
                        }]);
                    }
                    LinkedCarrierMutationForTest::InterfaceRegistryKind => {
                        let Some(parameter) = self.groups[group_index]
                            .interface_facts
                            .first()
                            .map(|fact| fact.parameter.id)
                        else {
                            return false;
                        };
                        let Some(registry) = Arc::get_mut(&mut self.registry) else {
                            return false;
                        };
                        let Some(parameter) = registry.type_variables.get_mut(&parameter) else {
                            return false;
                        };
                        drop(std::mem::replace(
                            &mut parameter.kind,
                            Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                        ));
                    }
                    LinkedCarrierMutationForTest::InterfaceFactParameterIdentity => {
                        let Some(fact) = self.groups[group_index].interface_facts.first_mut()
                        else {
                            return false;
                        };
                        fact.parameter.id = TypeVariableId::resolved(module, u32::MAX);
                    }
                    LinkedCarrierMutationForTest::InterfaceFactParameterSpelling => {
                        let Some(fact) = self.groups[group_index].interface_facts.first_mut()
                        else {
                            return false;
                        };
                        fact.parameter.spelling.push_str("-forged");
                    }
                    LinkedCarrierMutationForTest::InterfaceFactParameterKind => {
                        let Some(fact) = self.groups[group_index].interface_facts.first_mut()
                        else {
                            return false;
                        };
                        fact.parameter.kind =
                            Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
                    }
                    LinkedCarrierMutationForTest::InterfaceHiddenFactParameterKind => {
                        let Some(fact) = self.groups[group_index]
                            .interface_facts
                            .iter_mut()
                            .find(|fact| fact.spelling == "Witness")
                        else {
                            return false;
                        };
                        fact.parameter.kind =
                            Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
                    }
                    LinkedCarrierMutationForTest::InterfaceFactParameterOrigin => {
                        let Some(fact) = self.groups[group_index].interface_facts.first_mut()
                        else {
                            return false;
                        };
                        wrap_origin(&mut fact.parameter.origin);
                    }
                    LinkedCarrierMutationForTest::InterfaceMethodType => {
                        let Some(method) = self.groups[group_index]
                            .interface_facts
                            .first_mut()
                            .and_then(|fact| fact.methods.first_mut())
                        else {
                            return false;
                        };
                        discard_type_iteratively(std::mem::replace(
                            &mut method.value_type,
                            Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                        ));
                    }
                    LinkedCarrierMutationForTest::InterfaceMethodOrigin => {
                        let Some(method) = self.groups[group_index]
                            .interface_facts
                            .first_mut()
                            .and_then(|fact| fact.methods.first_mut())
                        else {
                            return false;
                        };
                        wrap_origin(&mut method.origin);
                    }
                    _ => unreachable!(),
                }
                true
            }
            LinkedCarrierMutationForTest::ImplementationRegistryKind
            | LinkedCarrierMutationForTest::ImplementationSourceParameterIdentity
            | LinkedCarrierMutationForTest::ImplementationSourceParameterSpelling
            | LinkedCarrierMutationForTest::ImplementationSourceParameterOrigin
            | LinkedCarrierMutationForTest::ImplementationSourceKind
            | LinkedCarrierMutationForTest::ImplementationFactKind
            | LinkedCarrierMutationForTest::ImplementationOpaqueFactKind
            | LinkedCarrierMutationForTest::ImplementationTokenIdentity
            | LinkedCarrierMutationForTest::ImplementationTokenInterface
            | LinkedCarrierMutationForTest::ImplementationTokenSourceIndex
            | LinkedCarrierMutationForTest::ImplementationTokenMethod
            | LinkedCarrierMutationForTest::ImplementationPrerequisite
            | LinkedCarrierMutationForTest::ImplementationMethodRequirement
            | LinkedCarrierMutationForTest::ImplementationMethodIdentity
            | LinkedCarrierMutationForTest::ImplementationMethodBinder => {
                let opaque = matches!(
                    mutation,
                    LinkedCarrierMutationForTest::ImplementationOpaqueFactKind
                );
                let Some(implementation_index) = self.groups[group_index]
                    .implementation_facts
                    .iter()
                    .position(|fact| {
                        fact.head_parameters
                            .first()
                            .is_some_and(|parameter| matches!(parameter.kind, Kind::Arrow(_, _)))
                            && (fact.prerequisites.is_empty() == opaque)
                    })
                else {
                    return false;
                };
                let parameter = self.groups[group_index].implementation_facts[implementation_index]
                    .head_parameters[0]
                    .id;
                match mutation {
                    LinkedCarrierMutationForTest::ImplementationRegistryKind => {
                        let Some(registry) = Arc::get_mut(&mut self.registry) else {
                            return false;
                        };
                        let Some(parameter) = registry.type_variables.get_mut(&parameter) else {
                            return false;
                        };
                        drop(std::mem::replace(&mut parameter.kind, Kind::Type));
                    }
                    LinkedCarrierMutationForTest::ImplementationSourceKind => {
                        let Some(source) = self.groups[group_index].implementations
                            [implementation_index]
                            .source
                            .as_mut()
                        else {
                            return false;
                        };
                        let Some(parameter) = source.head_parameters.first_mut() else {
                            return false;
                        };
                        drop(std::mem::replace(&mut parameter.kind, Kind::Type));
                    }
                    LinkedCarrierMutationForTest::ImplementationSourceParameterIdentity
                    | LinkedCarrierMutationForTest::ImplementationSourceParameterSpelling
                    | LinkedCarrierMutationForTest::ImplementationSourceParameterOrigin => {
                        let Some(source) = self.groups[group_index].implementations
                            [implementation_index]
                            .source
                            .as_mut()
                        else {
                            return false;
                        };
                        let Some(parameter) = source.head_parameters.first_mut() else {
                            return false;
                        };
                        match mutation {
                            LinkedCarrierMutationForTest::ImplementationSourceParameterIdentity => {
                                parameter.id = TypeVariableId::resolved(module, u32::MAX);
                            }
                            LinkedCarrierMutationForTest::ImplementationSourceParameterSpelling => {
                                parameter.spelling.push_str("-forged");
                            }
                            LinkedCarrierMutationForTest::ImplementationSourceParameterOrigin => {
                                wrap_origin(&mut parameter.origin);
                            }
                            _ => unreachable!(),
                        }
                    }
                    LinkedCarrierMutationForTest::ImplementationFactKind
                    | LinkedCarrierMutationForTest::ImplementationOpaqueFactKind => {
                        let parameter = &mut self.groups[group_index].implementation_facts
                            [implementation_index]
                            .head_parameters[0];
                        drop(std::mem::replace(&mut parameter.kind, Kind::Type));
                    }
                    LinkedCarrierMutationForTest::ImplementationTokenIdentity => {
                        self.groups[group_index].checked_implementations[implementation_index].id =
                            ImplId::new(module, u32::MAX);
                    }
                    LinkedCarrierMutationForTest::ImplementationTokenInterface => {
                        self.groups[group_index].checked_implementations[implementation_index]
                            .interface = InterfaceId::new(module, u32::MAX);
                    }
                    LinkedCarrierMutationForTest::ImplementationTokenSourceIndex => {
                        self.groups[group_index].checked_implementations[implementation_index]
                            .source_index = usize::MAX;
                    }
                    LinkedCarrierMutationForTest::ImplementationTokenMethod => {
                        let Some(method) = self.groups[group_index].checked_implementations
                            [implementation_index]
                            .methods
                            .first_mut()
                        else {
                            return false;
                        };
                        method.method = MethodId::new(method.method.interface(), u32::MAX);
                    }
                    LinkedCarrierMutationForTest::ImplementationPrerequisite => {
                        let Some(prerequisite) = self.groups[group_index].implementation_facts
                            [implementation_index]
                            .prerequisites
                            .first_mut()
                        else {
                            return false;
                        };
                        discard_type_iteratively(std::mem::replace(
                            &mut prerequisite.argument,
                            Type::Int,
                        ));
                    }
                    LinkedCarrierMutationForTest::ImplementationMethodRequirement => {
                        let Some(requirement) = self.groups[group_index].implementation_facts
                            [implementation_index]
                            .methods
                            .first_mut()
                            .and_then(|method| method.scheme.requirements.first_mut())
                        else {
                            return false;
                        };
                        discard_type_iteratively(std::mem::replace(
                            &mut requirement.argument,
                            Type::Int,
                        ));
                    }
                    LinkedCarrierMutationForTest::ImplementationMethodIdentity => {
                        let fact = &mut self.groups[group_index].implementation_facts
                            [implementation_index];
                        let Some(method) = fact.methods.first_mut() else {
                            return false;
                        };
                        method.id =
                            ImplMethodId::new(fact.id, MethodId::new(fact.interface, u32::MAX));
                    }
                    LinkedCarrierMutationForTest::ImplementationMethodBinder => {
                        let Some(method) = self.groups[group_index].implementation_facts
                            [implementation_index]
                            .methods
                            .first_mut()
                        else {
                            return false;
                        };
                        method.binder = BinderId::resolved(ModuleId::new(u32::MAX - 1), 0);
                    }
                    _ => unreachable!(),
                }
                true
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn replace_direct_equation_body_selection_for_test(
        &mut self,
        module: ModuleId,
        replacement: EvidenceSelection,
    ) -> bool {
        let Some(occurrence) = self
            .groups
            .iter_mut()
            .find(|group| group.module == module)
            .and_then(|group| group.definitions.first_mut())
            .and_then(|definition| definition.source.as_mut())
            .and_then(|definition| match &mut definition.kind {
                ResolvedDefinitionKind::Equational(global) => global.equations.first_mut(),
                ResolvedDefinitionKind::InlineOperational(_) => None,
            })
            .and_then(|equation| match &mut equation.body.kind {
                ResolvedExprKind::Occurrence(occurrence) => Some(occurrence),
                ResolvedExprKind::Integer(_)
                | ResolvedExprKind::Boolean(_)
                | ResolvedExprKind::Unit
                | ResolvedExprKind::Tuple(_)
                | ResolvedExprKind::Constructor(_)
                | ResolvedExprKind::Apply(_)
                | ResolvedExprKind::Add(_)
                | ResolvedExprKind::Multiply(_)
                | ResolvedExprKind::Equal(_)
                | ResolvedExprKind::Block(_)
                | ResolvedExprKind::Function(_)
                | ResolvedExprKind::Match(_) => None,
            })
        else {
            return false;
        };
        let Some(slot) = occurrence.evidence.first_mut() else {
            return false;
        };
        slot.replace_selection_for_test(replacement)
    }

    #[cfg(test)]
    pub(crate) fn replace_nth_direct_method_occurrence_arguments_for_test(
        &mut self,
        module: ModuleId,
        ordinal: usize,
        replacement: Box<[Type]>,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let mut seen = 0usize;
        for definition in &mut group.definitions {
            let Some(source) = definition.source.as_mut() else {
                continue;
            };
            let ResolvedDefinitionKind::Equational(global) = &mut source.kind else {
                continue;
            };
            for equation in &mut global.equations {
                let occurrence = match &mut equation.body.kind {
                    ResolvedExprKind::Occurrence(occurrence)
                        if matches!(occurrence.term, ResolvedTermName::Method(_)) =>
                    {
                        Some(occurrence)
                    }
                    ResolvedExprKind::Apply(application) => match &mut application.function.kind {
                        ResolvedExprKind::Occurrence(occurrence)
                            if matches!(occurrence.term, ResolvedTermName::Method(_)) =>
                        {
                            Some(occurrence)
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let Some(occurrence) = occurrence else {
                    continue;
                };
                if seen == ordinal {
                    let Some(slot) = occurrence.evidence.first_mut() else {
                        return false;
                    };
                    return slot.replace_method_arguments_for_test(replacement);
                }
                seen = match seen.checked_add(1) {
                    Some(next) => next,
                    None => return false,
                };
            }
        }
        false
    }

    #[cfg(test)]
    pub(crate) fn replace_nth_direct_method_occurrence_identity_for_test(
        &mut self,
        module: ModuleId,
        ordinal: usize,
        replacement: MethodId,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let mut seen = 0usize;
        for definition in &mut group.definitions {
            let Some(source) = definition.source.as_mut() else {
                continue;
            };
            let ResolvedDefinitionKind::Equational(global) = &mut source.kind else {
                continue;
            };
            for equation in &mut global.equations {
                let occurrence = match &mut equation.body.kind {
                    ResolvedExprKind::Occurrence(occurrence)
                        if matches!(occurrence.term, ResolvedTermName::Method(_)) =>
                    {
                        Some(occurrence)
                    }
                    ResolvedExprKind::Apply(application) => match &mut application.function.kind {
                        ResolvedExprKind::Occurrence(occurrence)
                            if matches!(occurrence.term, ResolvedTermName::Method(_)) =>
                        {
                            Some(occurrence)
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let Some(occurrence) = occurrence else {
                    continue;
                };
                if seen == ordinal {
                    occurrence.term = ResolvedTermName::Method(replacement);
                    return true;
                }
                seen = match seen.checked_add(1) {
                    Some(next) => next,
                    None => return false,
                };
            }
        }
        false
    }

    #[cfg(test)]
    pub(crate) fn replace_nth_direct_method_evidence_identity_for_test(
        &mut self,
        module: ModuleId,
        ordinal: usize,
        replacement: MethodId,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let mut seen = 0usize;
        for definition in &mut group.definitions {
            let Some(source) = definition.source.as_mut() else {
                continue;
            };
            let ResolvedDefinitionKind::Equational(global) = &mut source.kind else {
                continue;
            };
            for equation in &mut global.equations {
                let occurrence = match &mut equation.body.kind {
                    ResolvedExprKind::Occurrence(occurrence)
                        if matches!(occurrence.term, ResolvedTermName::Method(_)) =>
                    {
                        Some(occurrence)
                    }
                    ResolvedExprKind::Apply(application) => match &mut application.function.kind {
                        ResolvedExprKind::Occurrence(occurrence)
                            if matches!(occurrence.term, ResolvedTermName::Method(_)) =>
                        {
                            Some(occurrence)
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let Some(occurrence) = occurrence else {
                    continue;
                };
                if seen == ordinal {
                    let Some(slot) = occurrence.evidence.first_mut() else {
                        return false;
                    };
                    return slot.replace_checked_method_for_test(replacement);
                }
                seen = match seen.checked_add(1) {
                    Some(next) => next,
                    None => return false,
                };
            }
        }
        false
    }

    #[cfg(test)]
    pub(crate) fn replace_nth_direct_method_occurrence_selection_for_test(
        &mut self,
        module: ModuleId,
        ordinal: usize,
        replacement: EvidenceSelection,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let mut replacement = Some(replacement);
        let mut seen = 0usize;
        for definition in &mut group.definitions {
            let Some(source) = definition.source.as_mut() else {
                continue;
            };
            let ResolvedDefinitionKind::Equational(global) = &mut source.kind else {
                continue;
            };
            for equation in &mut global.equations {
                let occurrence = match &mut equation.body.kind {
                    ResolvedExprKind::Occurrence(occurrence)
                        if matches!(occurrence.term, ResolvedTermName::Method(_)) =>
                    {
                        Some(occurrence)
                    }
                    ResolvedExprKind::Apply(application) => match &mut application.function.kind {
                        ResolvedExprKind::Occurrence(occurrence)
                            if matches!(occurrence.term, ResolvedTermName::Method(_)) =>
                        {
                            Some(occurrence)
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let Some(occurrence) = occurrence else {
                    continue;
                };
                if seen == ordinal {
                    let Some(slot) = occurrence.evidence.first_mut() else {
                        return false;
                    };
                    return slot.replace_selection_for_test(
                        replacement
                            .take()
                            .expect("one replacement is consumed at most once"),
                    );
                }
                seen = match seen.checked_add(1) {
                    Some(next) => next,
                    None => return false,
                };
            }
        }
        false
    }

    #[cfg(test)]
    pub(crate) fn replace_nth_direct_method_occurrence_checked_type_for_test(
        &mut self,
        module: ModuleId,
        ordinal: usize,
        replacement: Type,
    ) -> bool {
        let replacement = IterativeTypeOwner::new(replacement);
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let mut seen = 0usize;
        for definition in &mut group.definitions {
            let Some(source) = definition.source.as_mut() else {
                continue;
            };
            let ResolvedDefinitionKind::Equational(global) = &mut source.kind else {
                continue;
            };
            for equation in &mut global.equations {
                let occurrence = match &mut equation.body.kind {
                    ResolvedExprKind::Occurrence(occurrence)
                        if matches!(occurrence.term, ResolvedTermName::Method(_)) =>
                    {
                        Some(occurrence)
                    }
                    ResolvedExprKind::Apply(application) => match &mut application.function.kind {
                        ResolvedExprKind::Occurrence(occurrence)
                            if matches!(occurrence.term, ResolvedTermName::Method(_)) =>
                        {
                            Some(occurrence)
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let Some(occurrence) = occurrence else {
                    continue;
                };
                if seen == ordinal {
                    let Some(slot) = occurrence.evidence.first_mut() else {
                        return false;
                    };
                    return slot.replace_checked_value_type_for_test(replacement.into_inner());
                }
                seen = match seen.checked_add(1) {
                    Some(next) => next,
                    None => return false,
                };
            }
        }
        false
    }

    #[cfg(test)]
    pub(crate) fn swap_first_implementation_method_scheme_parameters_for_test(
        &mut self,
        module: ModuleId,
    ) -> bool {
        let Some(parameters) = self
            .groups
            .iter_mut()
            .find(|group| group.module == module)
            .and_then(|group| group.implementation_facts.first_mut())
            .and_then(|implementation| implementation.methods.first_mut())
            .map(|method| &mut method.scheme.type_parameters)
        else {
            return false;
        };
        if parameters.len() < 2 {
            return false;
        }
        parameters.swap(0, 1);
        true
    }

    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) fn replace_available_route_for_test(
        &mut self,
        module: ModuleId,
        implementation: ImplId,
        route: ImplementationRoute,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let Some(available) = group
            .available_implementations
            .iter_mut()
            .find(|available| available.id == implementation)
        else {
            return false;
        };
        available.authorization = match route {
            ImplementationRoute::Local => ImplementationAuthorization::local(),
            ImplementationRoute::DirectImport {
                direct_dependency,
                available_at,
            } => ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                from: module,
                to: direct_dependency,
                import_span: available_at,
            }]),
        };
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_global_kind_boundary_for_test(
        &mut self,
        module: ModuleId,
        parameter_kinds: (ResolvedTypeVariable, Kind, Kind, Origin),
        value_types: (Type, Type),
    ) -> bool {
        let (canonical_parameter, checked_kind, source_kind, source_origin) = parameter_kinds;
        let parameter = canonical_parameter.id;
        let Some(group_index) = self.groups.iter().position(|group| group.module == module) else {
            return false;
        };
        let Some(checked_parameter_index) =
            self.groups[group_index]
                .schemes
                .first()
                .and_then(|checked| {
                    checked
                        .scheme
                        .type_parameters
                        .iter()
                        .position(|(candidate, _)| *candidate == parameter)
                })
        else {
            return false;
        };
        let Some(source_parameter_index) = self.groups[group_index]
            .definitions
            .first()
            .and_then(|definition| definition.source.as_ref())
            .and_then(|definition| match &definition.kind {
                ResolvedDefinitionKind::Equational(global) => global
                    .interface
                    .type_parameters
                    .iter()
                    .position(|candidate| candidate.id == parameter),
                ResolvedDefinitionKind::InlineOperational(_) => None,
            })
        else {
            return false;
        };
        let Some(registry) = Arc::get_mut(&mut self.registry) else {
            return false;
        };
        if !registry.type_variables.contains_key(&parameter) {
            return false;
        }
        registry.insert_type_variable(canonical_parameter);

        let checked = &mut self.groups[group_index].schemes[0].scheme;
        checked.type_parameters[checked_parameter_index].1 = checked_kind;
        discard_type_iteratively(std::mem::replace(&mut checked.value_type, value_types.0));

        let Some(definition) = self.groups[group_index].definitions[0].source.as_mut() else {
            return false;
        };
        let ResolvedDefinitionKind::Equational(global) = &mut definition.kind else {
            return false;
        };
        let source_parameter = &mut global.interface.type_parameters[source_parameter_index];
        source_parameter.kind = source_kind;
        discard_origin_iteratively(std::mem::replace(
            &mut source_parameter.origin,
            source_origin,
        ));
        discard_type_iteratively(std::mem::replace(
            &mut global.interface.annotation.ty,
            value_types.1,
        ));
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_checked_global_parameter_kind_for_test(
        &mut self,
        module: ModuleId,
        kind: Kind,
    ) -> bool {
        let Some(parameter) = self
            .groups
            .iter_mut()
            .find(|group| group.module == module)
            .and_then(|group| {
                group
                    .schemes
                    .iter_mut()
                    .find_map(|scheme| scheme.scheme.type_parameters.first_mut())
            })
        else {
            return false;
        };
        drop(std::mem::replace(&mut parameter.1, kind));
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_implementation_method_parameter_kind_for_test(
        &mut self,
        module: ModuleId,
        kind: Kind,
    ) -> bool {
        let Some(parameter) = self
            .groups
            .iter_mut()
            .find(|group| group.module == module)
            .and_then(|group| {
                group.implementation_facts.iter_mut().find_map(|fact| {
                    fact.methods
                        .iter_mut()
                        .find_map(|method| method.scheme.type_parameters.first_mut())
                })
            })
        else {
            return false;
        };
        drop(std::mem::replace(&mut parameter.1, kind));
        true
    }

    #[cfg(test)]
    pub(crate) fn erase_first_inline_global_binder_occurrence_for_test(
        &mut self,
        module: ModuleId,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let Some(index) = group.definitions.iter().position(|definition| {
            matches!(
                definition.kind(),
                ResolvedDefinitionKind::InlineOperational(_)
            )
        }) else {
            return false;
        };
        let Some(checked) = group.schemes.get_mut(index) else {
            return false;
        };
        discard_type_iteratively(std::mem::replace(
            &mut checked.scheme.value_type,
            Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
        ));
        let Some(definition) = group.definitions[index].source.as_mut() else {
            return false;
        };
        let ResolvedDefinitionKind::InlineOperational(global) = &mut definition.kind else {
            return false;
        };
        let Some(parameter) = global.header.parameters.first_mut() else {
            return false;
        };
        discard_type_iteratively(std::mem::replace(&mut parameter.annotation.ty, Type::Int));
        discard_type_iteratively(std::mem::replace(
            &mut global.header.result_type.ty,
            Type::Int,
        ));
        true
    }

    #[cfg(test)]
    pub(crate) fn corrupt_first_linked_implementation_parameter_spelling_for_test(
        &mut self,
    ) -> bool {
        let Some(identity) = self
            .groups
            .iter()
            .flat_map(|group| group.implementation_facts.iter())
            .find_map(|fact| fact.head_parameters.first().map(|parameter| parameter.id))
        else {
            return false;
        };
        let Some(registry) = Arc::get_mut(&mut self.registry) else {
            return false;
        };
        let Some(parameter) = registry.type_variables.get_mut(&identity) else {
            return false;
        };
        parameter.spelling.push_str("_forged");
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_linked_nominal_parameter_kind_for_test(
        &mut self,
        replacement: Kind,
    ) -> bool {
        let Some(registry) = Arc::get_mut(&mut self.registry) else {
            return false;
        };
        let Some(owner) = registry.nominals.first().map(|nominal| nominal.id) else {
            return false;
        };
        let Some(parameter) = registry
            .nominal_parameters
            .get_mut(&owner)
            .and_then(|parameters| parameters.first_mut())
        else {
            return false;
        };
        parameter.kind = replacement;
        true
    }

    #[cfg(test)]
    pub(crate) fn truncate_first_linked_constructor_family_for_test(&mut self) -> bool {
        let Some(registry) = Arc::get_mut(&mut self.registry) else {
            return false;
        };
        let Some(nominal) = registry
            .nominals
            .iter_mut()
            .find(|nominal| nominal.constructors.len() > 1)
        else {
            return false;
        };
        nominal.constructors = nominal.constructors[..nominal.constructors.len() - 1]
            .to_vec()
            .into_boxed_slice();
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_linked_constructor_payload_for_test(
        &mut self,
        replacement: Type,
    ) -> bool {
        let Some(registry) = Arc::get_mut(&mut self.registry) else {
            return false;
        };
        let Some(constructor) = registry
            .constructors
            .iter_mut()
            .find(|constructor| constructor.payload.is_some())
        else {
            return false;
        };
        if let Some(payload) = constructor.payload.replace(replacement) {
            discard_type_iteratively(payload);
        }
        true
    }

    #[cfg(test)]
    pub(crate) fn detach_first_linked_constructor_from_owner_for_test(&mut self) -> bool {
        let Some(registry) = Arc::get_mut(&mut self.registry) else {
            return false;
        };
        let Some(constructor) = registry.constructors.first_mut() else {
            return false;
        };
        constructor.owner = NominalTypeId::new(ModuleId::new(u32::MAX - 1), 0);
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_available_authorization_hops_for_test(
        &mut self,
        module: ModuleId,
        implementation: ImplId,
        hops: Vec<ImplementationRouteHop>,
    ) -> bool {
        let Some(available) = self
            .groups
            .iter_mut()
            .find(|group| group.module == module)
            .and_then(|group| {
                group
                    .available_implementations
                    .iter_mut()
                    .find(|available| available.id == implementation)
            })
        else {
            return false;
        };
        available.authorization = ImplementationAuthorization::from_hops(hops);
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_public_authorization_hops_for_test(
        &mut self,
        module: ModuleId,
        implementation: ImplId,
        hops: Vec<ImplementationRouteHop>,
    ) -> bool {
        let Some(authorization) = self
            .groups
            .iter_mut()
            .find(|group| group.module == module)
            .and_then(|group| {
                group
                    .public_implementations
                    .iter_mut()
                    .find(|authorization| authorization.id == implementation)
            })
        else {
            return false;
        };
        authorization.authorization = ImplementationAuthorization::from_hops(hops);
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_available_implementation_id_for_test(
        &mut self,
        module: ModuleId,
        implementation: ImplId,
        replacement: ImplId,
    ) -> bool {
        let Some(available) = self
            .groups
            .iter_mut()
            .find(|group| group.module == module)
            .and_then(|group| {
                group
                    .available_implementations
                    .iter_mut()
                    .find(|available| available.id == implementation)
            })
        else {
            return false;
        };
        available.id = replacement;
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_implementation_prerequisite_with_head_for_test(
        &mut self,
        implementation: ImplId,
        prerequisite_index: usize,
    ) -> bool {
        let Some(group) = self
            .groups
            .iter_mut()
            .find(|group| group.module == implementation.module())
        else {
            return false;
        };
        let Some(implementation_index) = group
            .implementation_facts
            .iter()
            .position(|fact| fact.id == implementation)
        else {
            return false;
        };
        let argument = group.implementation_facts[implementation_index]
            .argument
            .clone();
        let Some(source) = group
            .implementations
            .get_mut(implementation_index)
            .and_then(|body| body.source.as_mut())
        else {
            return false;
        };
        let Some(source_prerequisite) = source.prerequisites.get_mut(prerequisite_index) else {
            return false;
        };
        let Some(fact) = group.implementation_facts.get_mut(implementation_index) else {
            return false;
        };
        let Some(fact_prerequisite) = fact.prerequisites.get_mut(prerequisite_index) else {
            return false;
        };
        if fact
            .methods
            .iter()
            .any(|method| method.scheme.requirements.get(prerequisite_index).is_none())
        {
            return false;
        }

        discard_type_iteratively(std::mem::replace(
            &mut source_prerequisite.argument.ty,
            argument.clone(),
        ));
        discard_type_iteratively(std::mem::replace(
            &mut fact_prerequisite.argument,
            argument.clone(),
        ));
        for method in &mut fact.methods {
            let requirement = method
                .scheme
                .requirements
                .get_mut(prerequisite_index)
                .expect("the complete implementation method scheme was checked above");
            discard_type_iteratively(std::mem::replace(
                &mut requirement.argument,
                argument.clone(),
            ));
        }
        discard_type_iteratively(argument);
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_implementation_method_binder_for_test(
        &mut self,
        module: ModuleId,
        binder: BinderId,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let Some(method) = group
            .implementation_facts
            .first_mut()
            .and_then(|implementation| implementation.methods.first_mut())
        else {
            return false;
        };
        method.binder = binder;
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_interface_fact_id_for_test(
        &mut self,
        module: ModuleId,
        id: InterfaceId,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let Some(interface) = group.interface_facts.first_mut() else {
            return false;
        };
        interface.id = id;
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_interface_method_id_for_test(
        &mut self,
        module: ModuleId,
        id: MethodId,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let Some(method) = group
            .interface_facts
            .first_mut()
            .and_then(|interface| interface.methods.first_mut())
        else {
            return false;
        };
        method.id = id;
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_interface_method_type_pair_for_test(
        &mut self,
        module: ModuleId,
        replacement: Type,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let Some(fact_method) = group
            .interface_facts
            .first_mut()
            .and_then(|interface| interface.methods.first_mut())
        else {
            return false;
        };
        let mut type_work = TypeWorkBudget::unbounded();
        let source_replacement = clone_type_with_budget(&replacement, &mut type_work)
            .expect("an in-memory linked test Type clone should fit");
        discard_type_iteratively(std::mem::replace(&mut fact_method.value_type, replacement));
        let Some(source_method) = group
            .interfaces
            .first_mut()
            .and_then(|interface| interface.methods.first_mut())
        else {
            discard_type_iteratively(source_replacement);
            return false;
        };
        discard_type_iteratively(std::mem::replace(
            &mut source_method.annotation.ty,
            source_replacement,
        ));
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_implementation_fact_id_for_test(
        &mut self,
        module: ModuleId,
        id: ImplId,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let Some(implementation) = group.implementation_facts.first_mut() else {
            return false;
        };
        implementation.id = id;
        true
    }

    #[cfg(test)]
    pub(crate) fn reuse_first_implementation_method_binder_for_test(
        &mut self,
        module: ModuleId,
    ) -> bool {
        let Some(group) = self.groups.iter_mut().find(|group| group.module == module) else {
            return false;
        };
        let Some(methods) = group
            .implementation_facts
            .first_mut()
            .map(|implementation| implementation.methods.as_mut())
        else {
            return false;
        };
        let [first, second, ..] = methods else {
            return false;
        };
        second.binder = first.binder;
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_implementation_argument_for_test(
        &mut self,
        module: ModuleId,
        argument: Type,
    ) -> bool {
        let Some(fact) = self
            .groups
            .iter_mut()
            .find(|group| group.module == module)
            .and_then(|group| group.implementation_facts.first_mut())
        else {
            return false;
        };
        discard_type_iteratively(std::mem::replace(&mut fact.argument, argument));
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_implementation_method_type_for_test(
        &mut self,
        module: ModuleId,
        value_type: Type,
    ) -> bool {
        let Some(method) = self
            .groups
            .iter_mut()
            .find(|group| group.module == module)
            .and_then(|group| group.implementation_facts.first_mut())
            .and_then(|fact| fact.methods.first_mut())
        else {
            return false;
        };
        discard_type_iteratively(std::mem::replace(&mut method.scheme.value_type, value_type));
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_implementation_method_origin_for_test(
        &mut self,
        module: ModuleId,
        origin: Origin,
    ) -> bool {
        let Some(method) = self
            .groups
            .iter_mut()
            .find(|group| group.module == module)
            .and_then(|group| group.implementation_facts.first_mut())
            .and_then(|fact| fact.methods.first_mut())
        else {
            return false;
        };
        discard_origin_iteratively(std::mem::replace(&mut method.origin, origin));
        true
    }
}

impl Drop for ResolvedModuleProgram {
    fn drop(&mut self) {
        let placeholder = ResolvedExpr {
            kind: ResolvedExprKind::Unit,
            span: self.result.span,
        };
        let result = std::mem::replace(&mut self.result, placeholder);
        discard_resolved_body_work(vec![result], Vec::new());
    }
}

/// Body-free dependency facts retained by one resolved module.
#[derive(Debug, Default, Eq, PartialEq)]
pub struct ImportedFacts {
    globals: HashMap<BinderId, ImportedGlobalScheme>,
    global_order: Vec<BinderId>,
    nominals: HashMap<NominalTypeId, ImportedNominalFact>,
    nominal_order: Vec<NominalTypeId>,
    constructors: HashMap<ConstructorId, ImportedConstructorFact>,
    interfaces: Vec<ImportedInterfaceFact>,
    interface_positions: HashMap<InterfaceId, usize>,
    implementations: Vec<ImportedImplementationFact>,
    implementation_positions: HashMap<ImplId, usize>,
    public_implementation_order: Vec<ImplId>,
}

impl ImportedFacts {
    /// Looks up one imported checked global by semantic identity.
    #[must_use]
    pub fn global(&self, id: BinderId) -> Option<&ImportedGlobalScheme> {
        self.globals.get(&id)
    }

    /// Looks up one imported nominal fact by semantic identity.
    #[must_use]
    pub fn nominal(&self, id: NominalTypeId) -> Option<&ImportedNominalFact> {
        self.nominals.get(&id)
    }

    /// Looks up one imported transparent constructor by semantic identity.
    #[must_use]
    pub fn constructor(&self, id: ConstructorId) -> Option<&ImportedConstructorFact> {
        self.constructors.get(&id)
    }

    /// Looks up one imported checked interface by semantic identity.
    #[must_use]
    pub fn interface(&self, id: InterfaceId) -> Option<&CheckedInterfaceFact> {
        Some(
            &self
                .interfaces
                .get(*self.interface_positions.get(&id)?)?
                .fact,
        )
    }

    /// Looks up one selected public implementation by semantic identity.
    #[must_use]
    pub fn implementation(&self, id: ImplId) -> Option<&CheckedImplementationFact> {
        Some(
            &self
                .implementations
                .get(*self.implementation_positions.get(&id)?)?
                .fact,
        )
    }

    pub(crate) fn implementation_import(&self, id: ImplId) -> Option<&ImportedImplementationFact> {
        self.implementations
            .get(*self.implementation_positions.get(&id)?)
    }

    pub(crate) fn globals(&self) -> impl Iterator<Item = &ImportedGlobalScheme> {
        self.global_order
            .iter()
            .filter_map(|identity| self.globals.get(identity))
    }

    pub(crate) fn interface_imports(&self) -> impl Iterator<Item = &ImportedInterfaceFact> {
        self.interfaces.iter()
    }

    pub(crate) fn nominals(&self) -> impl Iterator<Item = &ImportedNominalFact> {
        self.nominal_order
            .iter()
            .filter_map(|identity| self.nominals.get(identity))
    }

    pub(crate) fn implementations(&self) -> impl Iterator<Item = &ImportedImplementationFact> {
        self.implementations.iter()
    }

    pub(crate) fn insert_global(
        &mut self,
        fact: ImportedGlobalScheme,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        if !self.globals.contains_key(&fact.binder) {
            if budget.charge(1).is_err()
                || self.global_order.try_reserve(1).is_err()
                || self.globals.try_reserve(1).is_err()
            {
                discard_imported_global(fact);
                return Err(());
            }
            self.global_order.push(fact.binder);
        }
        if let Some(displaced) = self.globals.insert(fact.binder, fact) {
            discard_imported_global(displaced);
        }
        Ok(())
    }

    pub(crate) fn prepare_nominal_merge(
        &mut self,
        candidate: ImportedNominalFactRef<'_>,
        type_work: &mut TypeWorkBudget,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<PreparedImportedNominalMerge, ImportedNominalMergeFailure> {
        let validated = self.validate_nominal_merge(candidate, constraint_work)?;
        let prepared = self.materialize_nominal_merge(validated, type_work)?;
        self.reserve_prepared_nominal_merges(std::slice::from_ref(&prepared))?;
        Ok(prepared)
    }

    pub(crate) fn validate_nominal_merge<'candidate>(
        &self,
        candidate: ImportedNominalFactRef<'candidate>,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<ValidatedImportedNominalMerge<'candidate>, ImportedNominalMergeFailure> {
        let validated = self.validate_nominal_merge_shape(candidate, constraint_work)?;
        self.validate_nominal_merge_metadata(&validated, constraint_work)?;
        Ok(validated)
    }

    pub(crate) fn validate_nominal_merge_shape<'candidate>(
        &self,
        candidate: ImportedNominalFactRef<'candidate>,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<ValidatedImportedNominalMerge<'candidate>, ImportedNominalMergeFailure> {
        let family_work = candidate
            .constructors
            .len()
            .checked_add(1)
            .ok_or(ImportedNominalMergeFailure::ConstraintResource)?;
        constraint_work
            .charge(family_work)
            .map_err(|()| ImportedNominalMergeFailure::ConstraintResource)?;
        if candidate.parameter_count != candidate.parameters.len()
            || candidate.constructor_count == 0
            || match candidate.access {
                ImportedTypeAccess::Transparent => {
                    candidate.constructors.len() != candidate.constructor_count
                }
                ImportedTypeAccess::Opaque | ImportedTypeAccess::Hidden => {
                    !candidate.constructors.is_empty()
                }
            }
        {
            return Err(ImportedNominalMergeFailure::Conflict);
        }
        let existing = self.nominals.get(&candidate.id);
        for (ordinal, constructor) in candidate.constructors.iter().enumerate() {
            if constructor.owner() != candidate.id
                || usize::try_from(constructor.constructor()) != Ok(ordinal)
                || existing.is_some_and(|existing| {
                    !existing.constructors.is_empty()
                        && existing.constructors.get(ordinal) != Some(constructor)
                })
            {
                return Err(ImportedNominalMergeFailure::Conflict);
            }
        }
        let Some(existing) = existing else {
            return Ok(ValidatedImportedNominalMerge {
                candidate,
                action: ValidatedImportedNominalAction::Insert,
            });
        };
        if existing.parameter_count != candidate.parameter_count
            || existing.constructor_count != candidate.constructor_count
            || existing.parameters.len() != candidate.parameters.len()
            || existing.display_is_private != candidate.display_is_private
        {
            return Err(ImportedNominalMergeFailure::Conflict);
        }
        let promotes_access = candidate.access.rank() > existing.access.rank();
        let fills_display = existing.display_spelling.is_none()
            && candidate.display_spelling.is_some()
            && !promotes_access;
        Ok(ValidatedImportedNominalMerge {
            candidate,
            action: if promotes_access || fills_display {
                ValidatedImportedNominalAction::Update { promotes_access }
            } else {
                ValidatedImportedNominalAction::Noop
            },
        })
    }

    pub(crate) fn validate_nominal_merge_metadata(
        &self,
        validated: &ValidatedImportedNominalMerge<'_>,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<(), ImportedNominalMergeFailure> {
        if matches!(validated.action, ValidatedImportedNominalAction::Insert) {
            return Ok(());
        }
        let candidate = validated.candidate;
        let existing = self
            .nominals
            .get(&candidate.id)
            .ok_or(ImportedNominalMergeFailure::Conflict)?;
        let parameters_match = same_summary_resolved_type_variables_with_constraint_budget(
            &existing.parameters,
            candidate.parameters,
            constraint_work,
        )
        .map_err(|failure| match failure {
            ResolvedBuildFailure::ConstraintResource => {
                ImportedNominalMergeFailure::ConstraintResource
            }
            ResolvedBuildFailure::TypeResource | ResolvedBuildFailure::InvalidState => {
                ImportedNominalMergeFailure::Conflict
            }
        })?;
        if !parameters_match {
            return Err(ImportedNominalMergeFailure::Conflict);
        }
        let origins_match =
            same_origin_with_constraint_budget(&existing.origin, candidate.origin, constraint_work)
                .map_err(|failure| match failure {
                    ResolvedBuildFailure::ConstraintResource => {
                        ImportedNominalMergeFailure::ConstraintResource
                    }
                    ResolvedBuildFailure::TypeResource | ResolvedBuildFailure::InvalidState => {
                        ImportedNominalMergeFailure::Conflict
                    }
                })?;
        let defining_display_conflict = existing.display_is_private
            && existing.display_spelling.as_deref() != candidate.display_spelling;
        if !origins_match || defining_display_conflict {
            return Err(ImportedNominalMergeFailure::Conflict);
        }
        Ok(())
    }

    pub(crate) fn materialize_nominal_merge(
        &mut self,
        validated: ValidatedImportedNominalMerge<'_>,
        type_work: &mut TypeWorkBudget,
    ) -> Result<PreparedImportedNominalMerge, ImportedNominalMergeFailure> {
        let candidate = validated.candidate;
        match validated.action {
            ValidatedImportedNominalAction::Insert => {
                let family_work = candidate
                    .constructors
                    .len()
                    .checked_add(1)
                    .ok_or(ImportedNominalMergeFailure::TypeResource)?;
                let retention_work = candidate.parameters.iter().try_fold(
                    family_work
                        .checked_add(1)
                        .ok_or(ImportedNominalMergeFailure::TypeResource)?,
                    |work, parameter| {
                        work.checked_add(
                            retained_type_variable_work(parameter)
                                .map_err(|_| ImportedNominalMergeFailure::TypeResource)?,
                        )
                        .ok_or(ImportedNominalMergeFailure::TypeResource)
                    },
                )?;
                type_work
                    .charge(retention_work)
                    .map_err(|()| ImportedNominalMergeFailure::TypeResource)?;
                let mut constructors = Vec::new();
                constructors
                    .try_reserve_exact(candidate.constructors.len())
                    .map_err(|_| ImportedNominalMergeFailure::TypeResource)?;
                constructors.extend_from_slice(candidate.constructors);
                let mut parameters = ResolvedTypeVariableBuffer(Vec::new());
                parameters
                    .try_reserve(candidate.parameters.len())
                    .map_err(|_| ImportedNominalMergeFailure::TypeResource)?;
                for parameter in candidate.parameters {
                    parameters.push(
                        clone_type_variable_after_combined_precharge(parameter)
                            .map_err(|_| ImportedNominalMergeFailure::TypeResource)?,
                    );
                }
                let display_spelling = candidate
                    .display_spelling
                    .map(try_clone_string)
                    .transpose()
                    .map_err(|_| ImportedNominalMergeFailure::TypeResource)?;
                Ok(PreparedImportedNominalMerge {
                    action: Some(PreparedImportedNominalAction::Insert(ImportedNominalFact {
                        id: candidate.id,
                        parameter_count: candidate.parameter_count,
                        constructor_count: candidate.constructor_count,
                        parameters: parameters.into_boxed_slice(),
                        constructors: constructors.into_boxed_slice(),
                        access: candidate.access,
                        display_spelling,
                        display_is_private: candidate.display_is_private,
                        origin: candidate.origin.clone(),
                    })),
                })
            }
            ValidatedImportedNominalAction::Noop => Ok(PreparedImportedNominalMerge {
                action: Some(PreparedImportedNominalAction::Noop),
            }),
            ValidatedImportedNominalAction::Update { promotes_access } => {
                let retained_family = if promotes_access {
                    candidate.constructors
                } else {
                    &[]
                };
                type_work
                    .charge(retained_family.len())
                    .map_err(|()| ImportedNominalMergeFailure::TypeResource)?;
                let mut constructors = Vec::new();
                constructors
                    .try_reserve_exact(retained_family.len())
                    .map_err(|_| ImportedNominalMergeFailure::TypeResource)?;
                constructors.extend_from_slice(retained_family);
                Ok(PreparedImportedNominalMerge {
                    action: Some(PreparedImportedNominalAction::Update {
                        id: candidate.id,
                        access: promotes_access.then_some(candidate.access),
                        constructors: (promotes_access && !candidate.constructors.is_empty())
                            .then(|| constructors.into_boxed_slice()),
                        display_spelling: candidate
                            .display_spelling
                            .map(try_clone_string)
                            .transpose()
                            .map_err(|_| ImportedNominalMergeFailure::TypeResource)?,
                    }),
                })
            }
        }
    }

    pub(crate) fn materialize_nominal_merge_after_precharge(
        &mut self,
        validated: ValidatedImportedNominalMerge<'_>,
    ) -> Result<PreparedImportedNominalMerge, ImportedNominalMergeFailure> {
        self.materialize_nominal_merge(validated, &mut TypeWorkBudget::unbounded())
    }

    pub(crate) fn reserve_prepared_nominal_merges(
        &mut self,
        prepared: &[PreparedImportedNominalMerge],
    ) -> Result<(), ImportedNominalMergeFailure> {
        let insert_count = prepared.iter().try_fold(0_usize, |count, prepared| {
            count
                .checked_add(usize::from(matches!(
                    &prepared.action,
                    Some(PreparedImportedNominalAction::Insert(_))
                )))
                .ok_or(ImportedNominalMergeFailure::TypeResource)
        })?;
        self.nominal_order
            .try_reserve(insert_count)
            .map_err(|_| ImportedNominalMergeFailure::TypeResource)?;
        self.nominals
            .try_reserve(insert_count)
            .map_err(|_| ImportedNominalMergeFailure::TypeResource)
    }

    pub(crate) fn commit_nominal_merge(
        &mut self,
        mut prepared: PreparedImportedNominalMerge,
    ) -> Result<(), ImportedNominalMergeFailure> {
        let action = prepared
            .action
            .take()
            .ok_or(ImportedNominalMergeFailure::Conflict)?;
        match action {
            PreparedImportedNominalAction::Noop => Ok(()),
            PreparedImportedNominalAction::Insert(fact) => {
                if self.nominals.contains_key(&fact.id) {
                    discard_imported_nominal(fact);
                    return Err(ImportedNominalMergeFailure::Conflict);
                }
                self.nominal_order.push(fact.id);
                if let Some(displaced) = self.nominals.insert(fact.id, fact) {
                    discard_imported_nominal(displaced);
                    return Err(ImportedNominalMergeFailure::Conflict);
                }
                Ok(())
            }
            PreparedImportedNominalAction::Update {
                id,
                access,
                constructors,
                display_spelling,
            } => {
                let existing = self
                    .nominals
                    .get_mut(&id)
                    .ok_or(ImportedNominalMergeFailure::Conflict)?;
                if let Some(access) = access {
                    existing.access = access;
                }
                if let Some(constructors) = constructors {
                    existing.constructors = constructors;
                }
                if display_spelling.is_some() {
                    existing.display_spelling = display_spelling;
                }
                Ok(())
            }
        }
    }

    pub(crate) fn commit_prepared_nominal_merges(
        &mut self,
        prepared: &mut Vec<PreparedImportedNominalMerge>,
    ) {
        for mut prepared in prepared.drain(..) {
            let action = prepared
                .action
                .take()
                .expect("a validated nominal action remains staged until commit");
            match action {
                PreparedImportedNominalAction::Noop => {}
                PreparedImportedNominalAction::Insert(fact) => {
                    debug_assert!(!self.nominals.contains_key(&fact.id));
                    self.nominal_order.push(fact.id);
                    let displaced = self.nominals.insert(fact.id, fact);
                    debug_assert!(displaced.is_none());
                    if let Some(displaced) = displaced {
                        discard_imported_nominal(displaced);
                    }
                }
                PreparedImportedNominalAction::Update {
                    id,
                    access,
                    constructors,
                    display_spelling,
                } => {
                    let existing = self
                        .nominals
                        .get_mut(&id)
                        .expect("a validated nominal update retains its destination");
                    if let Some(access) = access {
                        existing.access = access;
                    }
                    if let Some(constructors) = constructors {
                        existing.constructors = constructors;
                    }
                    if display_spelling.is_some() {
                        existing.display_spelling = display_spelling;
                    }
                }
            }
        }
    }

    pub(crate) fn reserve_constructor_inserts(&mut self, count: usize) -> Result<(), ()> {
        self.constructors.try_reserve(count).map_err(|_| ())
    }

    pub(crate) fn commit_constructor_inserts(
        &mut self,
        constructors: impl IntoIterator<Item = ImportedConstructorFact>,
    ) {
        for constructor in constructors {
            debug_assert!(!self.constructors.contains_key(&constructor.id));
            let displaced = self.constructors.insert(constructor.id, constructor);
            debug_assert!(displaced.is_none());
            if let Some(displaced) = displaced {
                displaced.discard_iteratively();
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn merge_nominal(
        &mut self,
        fact: ImportedNominalFact,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ImportedNominalMergeFailure> {
        let mut constraint_work =
            crate::interface::InterfaceConstraintBudget::with_limit(usize::MAX);
        let prepared = self.prepare_nominal_merge(
            ImportedNominalFactRef {
                id: fact.id,
                parameter_count: fact.parameter_count,
                constructor_count: fact.constructor_count,
                parameters: &fact.parameters,
                constructors: &fact.constructors,
                access: fact.access,
                display_spelling: fact.display_spelling.as_deref(),
                display_is_private: fact.display_is_private,
                origin: &fact.origin,
            },
            budget,
            &mut constraint_work,
        );
        discard_imported_nominal(fact);
        self.commit_nominal_merge(prepared?)
    }

    #[cfg(test)]
    pub(crate) fn insert_constructor(
        &mut self,
        fact: ImportedConstructorFact,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        if !self.constructors.contains_key(&fact.id)
            && (budget.charge(1).is_err() || self.constructors.try_reserve(1).is_err())
        {
            fact.discard_iteratively();
            return Err(());
        }
        if let Some(displaced) = self.constructors.insert(fact.id, fact) {
            displaced.discard_iteratively();
        }
        Ok(())
    }

    pub(crate) fn insert_interface(
        &mut self,
        fact: CheckedInterfaceFact,
        direct_dependency: ModuleId,
        available_at: Span,
        publicly_available: bool,
    ) {
        let position = self.interfaces.len();
        self.interface_positions.insert(fact.id, position);
        self.interfaces.push(ImportedInterfaceFact {
            fact,
            direct_dependency,
            available_at,
            publicly_available,
        });
    }

    pub(crate) fn merge_interface_route(
        &mut self,
        id: InterfaceId,
        direct_dependency: ModuleId,
        available_at: Span,
        publicly_available: bool,
    ) {
        let Some(imported) = self
            .interface_positions
            .get(&id)
            .and_then(|position| self.interfaces.get_mut(*position))
        else {
            return;
        };
        if !publicly_available || imported.publicly_available {
            return;
        }
        imported.direct_dependency = direct_dependency;
        imported.available_at = available_at;
        imported.publicly_available = true;
    }

    pub(crate) fn reserve_interface(&mut self) -> Result<(), ()> {
        self.interfaces.try_reserve(1).map_err(|_| ())?;
        self.interface_positions.try_reserve(1).map_err(|_| ())
    }

    pub(crate) fn insert_implementation(
        &mut self,
        fact: CheckedImplementationFact,
        authorization: ImplementationAuthorization,
        public_authorization: Option<ImplementationAuthorization>,
    ) {
        let position = self.implementations.len();
        self.implementation_positions.insert(fact.id, position);
        self.implementations.push(ImportedImplementationFact {
            fact,
            authorization,
            public_authorization,
        });
    }

    pub(crate) fn reserve_implementation(&mut self) -> Result<(), ()> {
        self.implementations.try_reserve(1).map_err(|_| ())?;
        self.implementation_positions.try_reserve(1).map_err(|_| ())
    }

    pub(crate) fn reserve_public_implementation(&mut self) -> Result<(), ()> {
        self.public_implementation_order
            .try_reserve(1)
            .map_err(|_| ())
    }

    pub(crate) fn mark_implementation_public(&mut self, id: ImplId) -> Result<(), ()> {
        if !self.implementation_positions.contains_key(&id) {
            return Err(());
        }
        self.public_implementation_order.push(id);
        Ok(())
    }

    pub(crate) fn commit_existing_implementation_routes(
        &mut self,
        id: ImplId,
        authorization: Option<ImplementationAuthorization>,
        public_authorization: Option<ImplementationAuthorization>,
        mark_public: bool,
    ) -> Result<(), ()> {
        let position = *self.implementation_positions.get(&id).ok_or(())?;
        let imported = self.implementations.get_mut(position).ok_or(())?;
        if let Some(authorization) = authorization {
            imported.authorization = authorization;
        }
        if let Some(public_authorization) = public_authorization {
            imported.public_authorization = Some(public_authorization);
        }
        if mark_public {
            self.public_implementation_order.push(id);
        }
        Ok(())
    }

    pub(crate) fn public_implementation_ids(&self) -> &[ImplId] {
        &self.public_implementation_order
    }
}

fn imported_nominal_family_is_valid(fact: &ImportedNominalFact) -> bool {
    if fact.constructor_count == 0 {
        return false;
    }
    match fact.access {
        ImportedTypeAccess::Transparent => {
            fact.constructors.len() == fact.constructor_count
                && fact
                    .constructors
                    .iter()
                    .enumerate()
                    .all(|(index, constructor)| {
                        constructor.owner() == fact.id
                            && usize::try_from(constructor.constructor()) == Ok(index)
                    })
        }
        ImportedTypeAccess::Opaque | ImportedTypeAccess::Hidden => fact.constructors.is_empty(),
    }
}

impl Drop for ImportedFacts {
    fn drop(&mut self) {
        for (_, fact) in self.globals.drain() {
            drop(fact.scheme);
            discard_origin_iteratively(fact.origin);
        }
        self.global_order.clear();
        for (_, fact) in self.nominals.drain() {
            for parameter in fact.parameters.into_vec() {
                discard_origin_iteratively(parameter.origin);
            }
            discard_origin_iteratively(fact.origin);
        }
        self.nominal_order.clear();
        for (_, fact) in self.constructors.drain() {
            drop(fact.scheme);
            if let Some(payload) = fact.payload {
                discard_type_iteratively(payload);
            }
            discard_origin_iteratively(fact.origin);
        }
        for imported in self.interfaces.drain(..) {
            drop(imported.fact);
        }
        self.interface_positions.clear();
        for imported in self.implementations.drain(..) {
            drop(imported.fact);
        }
        self.implementation_positions.clear();
        self.public_implementation_order.clear();
    }
}

fn discard_imported_global(fact: ImportedGlobalScheme) {
    let ImportedGlobalScheme { scheme, origin, .. } = fact;
    drop(scheme);
    discard_origin_iteratively(origin);
}

fn discard_imported_nominal(fact: ImportedNominalFact) {
    for parameter in fact.parameters.into_vec() {
        discard_origin_iteratively(parameter.origin);
    }
    discard_origin_iteratively(fact.origin);
}

/// One body-free checked interface fact keyed by stable semantic identity.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedInterfaceFact {
    /// Stable defining interface identity.
    pub id: InterfaceId,
    /// Exact defining source spelling.
    pub spelling: String,
    /// The interface's single parameter with its defining identity.
    pub parameter: ResolvedTypeVariable,
    /// Checked methods in semantic declaration order.
    pub methods: Box<[CheckedInterfaceMethodFact]>,
    /// Canonical method-binder rows minted from defining source authority.
    method_binder_authorities: Box<[MethodBinderAuthority]>,
    /// Causal declaration provenance.
    pub origin: Origin,
    /// Complete declaration span.
    pub span: Span,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct ImportedInterfaceFact {
    pub(crate) fact: CheckedInterfaceFact,
    pub(crate) direct_dependency: ModuleId,
    pub(crate) available_at: Span,
    pub(crate) publicly_available: bool,
}

impl CheckedInterfaceFact {
    /// Looks up one checked method within its owning interface.
    #[must_use]
    pub fn method(&self, id: MethodId) -> Option<&CheckedInterfaceMethodFact> {
        self.methods.iter().find(|method| method.id == id)
    }

    pub(crate) fn with_resolved_method_binder_authority(
        source: &ResolvedInterfaceDeclaration,
        parameter: ResolvedTypeVariable,
        methods: Box<[CheckedInterfaceMethodFact]>,
        type_work: &mut TypeWorkBudget,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        let method_binder_authorities =
            clone_resolved_method_binder_authorities(&source.methods, type_work, constraint_work)?
                .into_boxed_slice();
        Ok(Self {
            id: source.id,
            spelling: source.spelling.clone(),
            parameter,
            methods,
            method_binder_authorities,
            origin: source.origin.clone(),
            span: source.span,
        })
    }

    pub(crate) fn with_cloned_method_binder_authority(
        source: &Self,
        parameter: ResolvedTypeVariable,
        methods: Box<[CheckedInterfaceMethodFact]>,
        type_work: &mut TypeWorkBudget,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        let method_binder_authorities = clone_method_binder_authority_rows(
            &source.method_binder_authorities,
            type_work,
            constraint_work,
        )?
        .into_boxed_slice();
        Ok(Self {
            id: source.id,
            spelling: source.spelling.clone(),
            parameter,
            methods,
            method_binder_authorities,
            origin: source.origin.clone(),
            span: source.span,
        })
    }

    #[cfg(test)]
    pub(crate) fn without_methods_for_test(
        id: InterfaceId,
        spelling: String,
        parameter: ResolvedTypeVariable,
        origin: Origin,
        span: Span,
    ) -> Self {
        Self {
            id,
            spelling,
            parameter,
            methods: Box::new([]),
            method_binder_authorities: Box::new([]),
            origin,
            span,
        }
    }
}

impl Drop for CheckedInterfaceFact {
    fn drop(&mut self) {
        discard_origin_iteratively(std::mem::replace(
            &mut self.parameter.origin,
            Origin::Source(self.span),
        ));
        for method in std::mem::take(&mut self.methods).into_vec() {
            drop(method);
        }
        for authority in std::mem::take(&mut self.method_binder_authorities).into_vec() {
            drop(authority);
        }
        discard_origin_iteratively(std::mem::replace(
            &mut self.origin,
            Origin::Source(self.span),
        ));
    }
}

/// One checked method signature nested under an interface fact.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedInterfaceMethodFact {
    /// Stable method identity.
    pub id: MethodId,
    /// Exact defining source spelling.
    pub spelling: String,
    /// Ordered canonical method-local type binders retained separately from the value type.
    pub(crate) type_parameters: Box<[ResolvedTypeVariable]>,
    /// Checked source value type before evidence lowering.
    pub(crate) value_type: Type,
    /// Causal method provenance.
    pub origin: Origin,
    /// Complete method-signature span.
    pub span: Span,
}

impl Drop for CheckedInterfaceMethodFact {
    fn drop(&mut self) {
        for parameter in std::mem::take(&mut self.type_parameters).into_vec() {
            discard_resolved_type_variable(parameter);
        }
        discard_type_iteratively(std::mem::replace(&mut self.value_type, Type::Unit));
        discard_origin_iteratively(std::mem::replace(
            &mut self.origin,
            Origin::Source(self.span),
        ));
    }
}

impl CheckedInterfaceMethodFact {
    /// Borrows the ordered canonical method-local binder records.
    #[must_use]
    pub const fn type_parameters(&self) -> &[ResolvedTypeVariable] {
        &self.type_parameters
    }

    /// Borrows the checked source value type before evidence lowering.
    #[must_use]
    pub const fn value_type(&self) -> &Type {
        &self.value_type
    }
}

/// One body-free checked implementation fact available for selection and overlap checks.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedImplementationFact {
    /// Stable anonymous implementation identity.
    pub id: ImplId,
    /// Stable implemented interface identity.
    pub interface: InterfaceId,
    /// Ordered rigid head parameters with defining identities.
    pub head_parameters: Box<[ResolvedTypeVariable]>,
    /// Checked implementation head argument.
    pub(crate) argument: Type,
    /// Ordered checked prerequisites.
    pub prerequisites: Box<[CheckedRequirement]>,
    /// Method mappings in interface declaration order.
    pub methods: Box<[CheckedImplementationMethodFact]>,
    /// Causal implementation provenance.
    pub origin: Origin,
    /// Complete implementation span.
    pub span: Span,
}

/// One checked implementation selected through an authenticated import route.
#[derive(Debug, Eq, PartialEq)]
pub struct ImportedImplementationFact {
    /// Defining implementation fact retained without a body.
    pub fact: CheckedImplementationFact,
    pub(crate) authorization: ImplementationAuthorization,
    pub(crate) public_authorization: Option<ImplementationAuthorization>,
}

impl CheckedImplementationFact {
    /// Borrows the checked implementation head argument.
    #[must_use]
    pub const fn argument(&self) -> &Type {
        &self.argument
    }
}

impl ImportedImplementationFact {
    /// Returns the canonical effective-availability route.
    #[must_use]
    pub const fn authorization(&self) -> &ImplementationAuthorization {
        &self.authorization
    }

    /// Returns the canonical public route, when a public selector authorized one.
    #[must_use]
    pub const fn public_authorization(&self) -> Option<&ImplementationAuthorization> {
        self.public_authorization.as_ref()
    }
}

impl Drop for CheckedImplementationFact {
    fn drop(&mut self) {
        for parameter in std::mem::take(&mut self.head_parameters).into_vec() {
            discard_origin_iteratively(parameter.origin);
        }
        discard_type_iteratively(std::mem::replace(&mut self.argument, Type::Unit));
        for prerequisite in std::mem::take(&mut self.prerequisites).into_vec() {
            drop(prerequisite);
        }
        for method in std::mem::take(&mut self.methods).into_vec() {
            drop(method);
        }
        discard_origin_iteratively(std::mem::replace(
            &mut self.origin,
            Origin::Source(self.span),
        ));
    }
}

/// One checked implementation-method identity-to-binder relation.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedImplementationMethodFact {
    /// Stable implementation-method identity.
    pub id: ImplMethodId,
    /// Stable interface method supplied by the body.
    pub method: MethodId,
    /// Hidden module-qualified implementation-method binder.
    pub binder: BinderId,
    /// Checked conceptual scheme after rigid implementation-head substitution.
    pub scheme: ConstrainedScheme,
    /// Number of leading scheme parameters owned by the implementation head.
    pub(crate) head_type_parameter_count: usize,
    /// Causal method-body provenance.
    pub origin: Origin,
    /// Complete implementation-method group span.
    pub span: Span,
}

impl Drop for CheckedImplementationMethodFact {
    fn drop(&mut self) {
        drop(std::mem::replace(
            &mut self.scheme,
            ConstrainedScheme {
                type_parameters: Box::new([]),
                requirements: Box::new([]),
                value_type: Type::Unit,
            },
        ));
        discard_origin_iteratively(std::mem::replace(
            &mut self.origin,
            Origin::Source(self.span),
        ));
    }
}

impl CheckedImplementationMethodFact {
    /// Returns the boundary between head parameters and method-local parameters.
    #[must_use]
    pub const fn head_type_parameter_count(&self) -> usize {
        self.head_type_parameter_count
    }
}

fn clone_checked_requirement(
    requirement: &CheckedRequirement,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<CheckedRequirement, ResolvedBuildFailure> {
    constraint_work
        .charge_type(&requirement.argument)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    Ok(CheckedRequirement {
        id: requirement.id,
        interface: requirement.interface,
        argument: clone_type_with_budget(&requirement.argument, type_work)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?,
        origin: requirement.origin.clone(),
        span: requirement.span,
    })
}

fn clone_checked_interface_fact(
    fact: &CheckedInterfaceFact,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<CheckedInterfaceFact, ResolvedBuildFailure> {
    authenticate_method_binder_authority(fact, None, constraint_work)?;
    constraint_work
        .charge(fact.methods.len().saturating_add(1))
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    let mut methods = Vec::new();
    methods
        .try_reserve(fact.methods.len())
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    for method in &fact.methods {
        constraint_work
            .charge_type(&method.value_type)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let value_type = IterativeTypeOwner::new(
            clone_type_with_budget(&method.value_type, type_work)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?,
        );
        let type_parameters =
            clone_resolved_type_variable_buffer_with_budget(&method.type_parameters, type_work)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        methods.push(CheckedInterfaceMethodFact {
            id: method.id,
            spelling: method.spelling.clone(),
            type_parameters: type_parameters.into_vec().into_boxed_slice(),
            value_type: value_type.into_inner(),
            origin: method.origin.clone(),
            span: method.span,
        });
    }
    CheckedInterfaceFact::with_cloned_method_binder_authority(
        fact,
        clone_resolved_type_variable_with_budget(&fact.parameter, type_work)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?,
        methods.into_boxed_slice(),
        type_work,
        constraint_work,
    )
}

fn clone_checked_implementation_fact(
    fact: &CheckedImplementationFact,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<CheckedImplementationFact, ResolvedBuildFailure> {
    constraint_work
        .charge(
            fact.head_parameters
                .len()
                .saturating_add(fact.prerequisites.len())
                .saturating_add(fact.methods.len())
                .saturating_add(1),
        )
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    constraint_work
        .charge_type(&fact.argument)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;

    let mut head_parameters = ResolvedTypeVariableBuffer(Vec::new());
    head_parameters
        .try_reserve(fact.head_parameters.len())
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    for parameter in &fact.head_parameters {
        head_parameters.push(
            clone_resolved_type_variable_with_budget(parameter, type_work)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?,
        );
    }

    let mut prerequisites = Vec::new();
    prerequisites
        .try_reserve(fact.prerequisites.len())
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    for prerequisite in &fact.prerequisites {
        prerequisites.push(clone_checked_requirement(
            prerequisite,
            type_work,
            constraint_work,
        )?);
    }

    let mut methods = Vec::new();
    methods
        .try_reserve(fact.methods.len())
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    for method in &fact.methods {
        constraint_work
            .charge(
                method
                    .scheme
                    .type_parameters
                    .len()
                    .saturating_add(method.scheme.requirements.len())
                    .saturating_add(1),
            )
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge_type(&method.scheme.value_type)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        for requirement in &method.scheme.requirements {
            constraint_work
                .charge_type(&requirement.argument)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        }
        methods.push(CheckedImplementationMethodFact {
            id: method.id,
            method: method.method,
            binder: method.binder,
            scheme: method
                .scheme
                .clone_with_budget(type_work)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?,
            head_type_parameter_count: method.head_type_parameter_count,
            origin: method.origin.clone(),
            span: method.span,
        });
    }

    let argument = IterativeTypeOwner::new(
        clone_type_with_budget(&fact.argument, type_work)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?,
    );
    Ok(CheckedImplementationFact {
        id: fact.id,
        interface: fact.interface,
        head_parameters: head_parameters.into_boxed_slice(),
        argument: argument.into_inner(),
        prerequisites: prerequisites.into_boxed_slice(),
        methods: methods.into_boxed_slice(),
        origin: fact.origin.clone(),
        span: fact.span,
    })
}

/// One imported checked global scheme.
#[derive(Debug, Eq, PartialEq)]
pub struct ImportedGlobalScheme {
    /// Stable defining binder identity.
    pub binder: BinderId,
    /// Fully zonked closed constrained rank-1 scheme.
    pub scheme: ConstrainedScheme,
    /// Causal declaration provenance.
    pub origin: Origin,
}

/// One checked implementation published with its complete authorization route.
#[derive(Debug, Eq, PartialEq)]
pub struct AuthorizedImplementationFact {
    fact: CheckedImplementationFact,
    authorization: ImplementationAuthorization,
}

impl AuthorizedImplementationFact {
    #[cfg(test)]
    pub(crate) fn local_for_test(fact: CheckedImplementationFact) -> Self {
        Self {
            fact,
            authorization: ImplementationAuthorization::local(),
        }
    }

    /// Returns the original checked implementation fact.
    #[must_use]
    pub const fn fact(&self) -> &CheckedImplementationFact {
        &self.fact
    }

    /// Returns the route from the publishing summary to the defining module.
    #[must_use]
    pub const fn authorization(&self) -> &ImplementationAuthorization {
        &self.authorization
    }
}

/// One imported nominal access fact.
#[derive(Debug, Eq, PartialEq)]
pub struct ImportedNominalFact {
    /// Stable defining nominal identity.
    pub id: NominalTypeId,
    /// Number of declared parameters.
    pub parameter_count: usize,
    /// Defining constructor-family cardinality, retained independently of access.
    pub(crate) constructor_count: usize,
    /// Ordered declaration parameters, preserving defining identities.
    pub parameters: Box<[ResolvedTypeVariable]>,
    /// Complete constructor family when access is transparent.
    pub constructors: Box<[ConstructorId]>,
    /// Importer access mode.
    pub access: ImportedTypeAccess,
    /// Display-only declaration spelling; never a resolver binding.
    pub display_spelling: Option<String>,
    /// Whether the displayed declaration spelling is private at its definition.
    pub display_is_private: bool,
    /// Causal declaration provenance.
    pub origin: Origin,
}

impl ImportedNominalFact {
    /// Renders a diagnostic-only name without creating a resolver binding.
    #[must_use]
    pub fn display_name(&self, module_label: &str) -> String {
        match (self.display_is_private, self.display_spelling.as_deref()) {
            (true, Some(spelling)) => {
                format!("{module_label}.<private {spelling}>")
            }
            (_, Some(spelling)) => format!("{module_label}.{spelling}"),
            _ => Type::Nominal(self.id).to_string(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ImportedNominalMergeFailure {
    Conflict,
    TypeResource,
    ConstraintResource,
}

#[derive(Clone, Copy)]
enum ValidatedImportedNominalAction {
    Noop,
    Insert,
    Update { promotes_access: bool },
}

pub(crate) struct ValidatedImportedNominalMerge<'candidate> {
    candidate: ImportedNominalFactRef<'candidate>,
    action: ValidatedImportedNominalAction,
}

impl ValidatedImportedNominalMerge<'_> {
    pub(crate) fn requires_commit(&self) -> bool {
        !matches!(self.action, ValidatedImportedNominalAction::Noop)
    }

    pub(crate) fn retention_type_work(&self) -> Result<usize, ImportedNominalMergeFailure> {
        match self.action {
            ValidatedImportedNominalAction::Noop => Ok(0),
            ValidatedImportedNominalAction::Update { promotes_access } => Ok(if promotes_access {
                self.candidate.constructors.len()
            } else {
                0
            }),
            ValidatedImportedNominalAction::Insert => self.candidate.parameters.iter().try_fold(
                self.candidate
                    .constructors
                    .len()
                    .checked_add(2)
                    .ok_or(ImportedNominalMergeFailure::TypeResource)?,
                |work, parameter| {
                    work.checked_add(
                        retained_type_variable_work(parameter)
                            .map_err(|_| ImportedNominalMergeFailure::TypeResource)?,
                    )
                    .ok_or(ImportedNominalMergeFailure::TypeResource)
                },
            ),
        }
    }
}

enum PreparedImportedNominalAction {
    Noop,
    Insert(ImportedNominalFact),
    Update {
        id: NominalTypeId,
        access: Option<ImportedTypeAccess>,
        constructors: Option<Box<[ConstructorId]>>,
        display_spelling: Option<String>,
    },
}

pub(crate) struct PreparedImportedNominalMerge {
    action: Option<PreparedImportedNominalAction>,
}

impl Drop for PreparedImportedNominalMerge {
    fn drop(&mut self) {
        if let Some(PreparedImportedNominalAction::Insert(fact)) = self.action.take() {
            discard_imported_nominal(fact);
        }
    }
}

/// One imported transparent constructor fact.
#[derive(Debug, Eq, PartialEq)]
pub struct ImportedConstructorFact {
    /// Stable defining constructor identity.
    pub id: ConstructorId,
    /// Defining source spelling retained for coverage diagnostics.
    pub spelling: String,
    /// Optional semantic payload type.
    pub payload: Option<Type>,
    /// Canonical checked rank-1 constructor scheme retained from its defining summary.
    pub scheme: ConstrainedScheme,
    /// Causal declaration provenance.
    pub origin: Origin,
}

impl ImportedConstructorFact {
    /// Consumes a standalone imported constructor fact and dismantles its
    /// optional payload without recursive type drop.
    pub fn discard_iteratively(self) {
        drop(self.scheme);
        if let Some(payload) = self.payload {
            discard_type_iteratively(payload);
        }
        discard_origin_iteratively(self.origin);
    }
}

/// Public local declarations and checked imported names staged by resolution.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResolvedExportCandidate {
    terms: HashMap<String, CandidateGlobal>,
    term_order: Vec<String>,
    nominals: HashMap<String, CandidateNominal>,
    nominal_order: Vec<String>,
    constructors: HashMap<String, CandidateConstructor>,
    constructor_order: Vec<String>,
    interfaces: HashMap<String, CandidateInterface>,
    interface_order: Vec<String>,
    methods: HashMap<String, CandidateMethod>,
    method_order: Vec<String>,
    hidden_nominals: HashMap<NominalTypeId, CandidateHiddenNominal>,
    hidden_nominal_order: Vec<NominalTypeId>,
    withheld: HashMap<String, WithheldExports>,
    withheld_order: Vec<WithheldOrderEntry>,
}

impl ResolvedExportCandidate {
    /// Looks up one public local term candidate.
    #[must_use]
    pub fn term(&self, spelling: &str) -> Option<&CandidateGlobal> {
        self.terms.get(spelling)
    }

    /// Looks up one public opaque or transparent nominal candidate.
    #[must_use]
    pub fn nominal(&self, spelling: &str) -> Option<&CandidateNominal> {
        self.nominals.get(spelling)
    }

    /// Looks up one constructor of a public transparent nominal candidate.
    #[must_use]
    pub fn constructor(&self, spelling: &str) -> Option<&CandidateConstructor> {
        self.constructors.get(spelling)
    }

    /// Looks up one public interface-name candidate.
    #[must_use]
    pub fn interface(&self, spelling: &str) -> Option<&CandidateInterface> {
        self.interfaces.get(spelling)
    }

    /// Looks up one public method-name candidate.
    #[must_use]
    pub fn method(&self, spelling: &str) -> Option<&CandidateMethod> {
        self.methods.get(spelling)
    }

    /// Looks up one private nominal retained only for checked public schemes.
    #[must_use]
    pub fn hidden_nominal(&self, id: NominalTypeId) -> Option<&CandidateHiddenNominal> {
        self.hidden_nominals.get(&id)
    }

    /// Reports whether one source spelling is withheld because it is private.
    #[must_use]
    pub fn is_private(&self, spelling: &str) -> bool {
        self.withheld.get(spelling).is_some_and(|withheld| {
            withheld
                .iter()
                .any(|withheld| withheld.kind == WithheldExportKind::Private)
        })
    }

    /// Reports whether a constructor spelling is withheld by opacity.
    #[must_use]
    pub fn is_opaque_constructor(&self, spelling: &str) -> bool {
        self.withheld
            .get(spelling)
            .and_then(|withheld| withheld.get(WithheldNamespace::Constructor))
            .is_some_and(|withheld| withheld.kind == WithheldExportKind::OpaqueConstructor)
    }

    pub(crate) fn try_insert_term(
        &mut self,
        spelling: String,
        candidate: CandidateGlobal,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        try_insert_ordered(
            &mut self.terms,
            &mut self.term_order,
            spelling,
            candidate,
            budget,
            |candidate: CandidateGlobal| discard_origin_iteratively(candidate.origin),
        )
    }

    pub(crate) fn try_insert_nominal(
        &mut self,
        spelling: String,
        candidate: CandidateNominal,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        try_insert_ordered(
            &mut self.nominals,
            &mut self.nominal_order,
            spelling,
            candidate,
            budget,
            |candidate: CandidateNominal| discard_origin_iteratively(candidate.origin),
        )
    }

    pub(crate) fn try_insert_constructor(
        &mut self,
        spelling: String,
        candidate: CandidateConstructor,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        try_insert_ordered(
            &mut self.constructors,
            &mut self.constructor_order,
            spelling,
            candidate,
            budget,
            |candidate: CandidateConstructor| discard_origin_iteratively(candidate.origin),
        )
    }

    pub(crate) fn try_insert_interface(
        &mut self,
        spelling: String,
        candidate: CandidateInterface,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        try_insert_ordered(
            &mut self.interfaces,
            &mut self.interface_order,
            spelling,
            candidate,
            budget,
            |_candidate: CandidateInterface| {},
        )
    }

    pub(crate) fn try_insert_method(
        &mut self,
        spelling: String,
        candidate: CandidateMethod,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        try_insert_ordered(
            &mut self.methods,
            &mut self.method_order,
            spelling,
            candidate,
            budget,
            |_candidate: CandidateMethod| {},
        )
    }

    pub(crate) fn try_insert_hidden_nominal(
        &mut self,
        candidate: CandidateHiddenNominal,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        if let Some(existing) = self.hidden_nominals.get_mut(&candidate.id) {
            let displaced = std::mem::replace(existing, candidate);
            discard_origin_iteratively(displaced.origin);
            return Ok(());
        }
        budget.charge(2)?;
        self.hidden_nominals.try_reserve(1).map_err(|_| ())?;
        self.hidden_nominal_order.try_reserve(1).map_err(|_| ())?;
        let identity = candidate.id;
        if let Some(displaced) = self.hidden_nominals.insert(identity, candidate) {
            discard_origin_iteratively(displaced.origin);
        } else {
            self.hidden_nominal_order.push(identity);
        }
        Ok(())
    }

    pub(crate) fn try_insert_withheld(
        &mut self,
        namespace: WithheldNamespace,
        spelling: String,
        withheld: WithheldExport,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ()> {
        let owner = withheld.owner;
        if let Some(existing) = self.withheld.get_mut(&spelling)
            && let Some(existing) = existing.get_exact_mut(namespace, owner)
        {
            let displaced = std::mem::replace(existing, withheld);
            discard_withheld_export(displaced);
            return Ok(());
        }
        let retained_work = if namespace == WithheldNamespace::Constructor {
            3
        } else {
            2
        };
        budget.charge(retained_work)?;
        let spelling_exists = self.withheld.contains_key(&spelling);
        if !spelling_exists {
            self.withheld.try_reserve(1).map_err(|_| ())?;
        }
        self.withheld_order.try_reserve(1).map_err(|_| ())?;
        if spelling_exists {
            self.withheld
                .get_mut(&spelling)
                .expect("the retained withheld spelling should remain present")
                .try_reserve(namespace, 1)?;
        } else {
            let mut entries = WithheldExports::default();
            entries.try_reserve(namespace, 1)?;
            if let Some(displaced) = self.withheld.insert(spelling.clone(), entries) {
                discard_withheld_exports(displaced);
            }
        }
        let constructor_index = self
            .withheld
            .get_mut(&spelling)
            .expect("the reserved withheld spelling should be present")
            .insert_new(namespace, withheld);
        self.withheld_order.push(WithheldOrderEntry {
            spelling,
            namespace,
            owner,
            constructor_index,
        });
        Ok(())
    }
}

fn try_insert_ordered<K, V>(
    entries: &mut HashMap<K, V>,
    order: &mut Vec<K>,
    key: K,
    value: V,
    budget: &mut TypeWorkBudget,
    mut discard: impl FnMut(V),
) -> Result<(), ()>
where
    K: Clone + Eq + Hash,
{
    if let Some(existing) = entries.get_mut(&key) {
        discard(std::mem::replace(existing, value));
        return Ok(());
    }
    budget.charge(2)?;
    entries.try_reserve(1).map_err(|_| ())?;
    order.try_reserve(1).map_err(|_| ())?;
    order.push(key.clone());
    if let Some(displaced) = entries.insert(key, value) {
        discard(displaced);
    }
    Ok(())
}

fn discard_withheld_export(withheld: WithheldExport) {
    if let Some(origin) = withheld.origin {
        discard_origin_iteratively(origin);
    }
}

fn discard_withheld_exports(withheld: WithheldExports) {
    for withheld in withheld.into_values() {
        discard_withheld_export(withheld);
    }
}

impl Drop for ResolvedExportCandidate {
    fn drop(&mut self) {
        for (_, candidate) in self.terms.drain() {
            discard_origin_iteratively(candidate.origin);
        }
        self.term_order.clear();
        for (_, candidate) in self.nominals.drain() {
            discard_origin_iteratively(candidate.origin);
        }
        self.nominal_order.clear();
        for (_, candidate) in self.constructors.drain() {
            discard_origin_iteratively(candidate.origin);
        }
        self.constructor_order.clear();
        self.interfaces.clear();
        self.interface_order.clear();
        self.methods.clear();
        self.method_order.clear();
        for (_, candidate) in self.hidden_nominals.drain() {
            discard_origin_iteratively(candidate.origin);
        }
        self.hidden_nominal_order.clear();
        for (_, withheld) in self.withheld.drain() {
            discard_withheld_exports(withheld);
        }
        self.withheld_order.clear();
    }
}

/// One local or imported public global selected by resolution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateGlobal {
    /// Stable defining binder identity.
    pub binder: BinderId,
    pub(crate) source: CandidateFactSource,
    /// Declaration provenance.
    pub origin: Origin,
}

/// One local or imported public nominal selected by resolution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateNominal {
    /// Stable nominal identity.
    pub id: NominalTypeId,
    /// Opaque or transparent importer access.
    pub access: ExportedTypeAccess,
    pub(crate) source: CandidateFactSource,
    /// Declaration provenance.
    pub origin: Origin,
}

/// One local or imported constructor of a public transparent nominal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateConstructor {
    /// Stable constructor identity.
    pub id: ConstructorId,
    pub(crate) source: CandidateFactSource,
    /// Declaration provenance.
    pub origin: Origin,
}

/// One checked interface identity selected for publication under a source spelling.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CandidateInterface {
    /// Stable defining interface identity.
    pub id: InterfaceId,
    pub(crate) source: CandidateFactSource,
}

/// One checked method identity selected for publication under a source spelling.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CandidateMethod {
    /// Stable defining method identity.
    pub id: MethodId,
    pub(crate) source: CandidateFactSource,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CandidateFactSource {
    Local,
    Imported,
}

/// One private nominal identity available for checked public schemes only.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateHiddenNominal {
    /// Stable nominal identity.
    pub id: NominalTypeId,
    /// Number of declared parameters.
    pub parameter_count: usize,
    /// Display-only declaration spelling.
    pub spelling: String,
    /// Declaration provenance.
    pub origin: Origin,
}

/// Why one dependency spelling is withheld from source resolution.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum WithheldExportKind {
    /// The declaration is private to its defining module.
    Private,
    /// The constructor belongs to a public opaque nominal.
    OpaqueConstructor,
}

/// Namespace containing one withheld source spelling.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum WithheldNamespace {
    Term,
    Nominal,
    Constructor,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct WithheldOrderEntry {
    spelling: String,
    namespace: WithheldNamespace,
    owner: Option<NominalTypeId>,
    constructor_index: Option<usize>,
}

/// Diagnostic-only metadata for a withheld dependency spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct WithheldExport {
    pub(crate) kind: WithheldExportKind,
    pub(crate) owner: Option<NominalTypeId>,
    pub(crate) origin: Option<Origin>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct WithheldExports {
    term: Option<WithheldExport>,
    nominal: Option<WithheldExport>,
    constructor: Vec<WithheldExport>,
    constructor_positions: HashMap<Option<NominalTypeId>, usize>,
}

impl WithheldExports {
    fn len(&self) -> Option<usize> {
        self.constructor
            .len()
            .checked_add(usize::from(self.term.is_some()))
            .and_then(|count| count.checked_add(usize::from(self.nominal.is_some())))
    }

    fn get(&self, namespace: WithheldNamespace) -> Option<&WithheldExport> {
        match namespace {
            WithheldNamespace::Term => self.term.as_ref(),
            WithheldNamespace::Nominal => self.nominal.as_ref(),
            WithheldNamespace::Constructor => self.constructor.first(),
        }
    }

    fn get_exact_mut(
        &mut self,
        namespace: WithheldNamespace,
        owner: Option<NominalTypeId>,
    ) -> Option<&mut WithheldExport> {
        match namespace {
            WithheldNamespace::Term => self
                .term
                .as_mut()
                .filter(|withheld| withheld.owner == owner),
            WithheldNamespace::Nominal => self
                .nominal
                .as_mut()
                .filter(|withheld| withheld.owner == owner),
            WithheldNamespace::Constructor => {
                let position = *self.constructor_positions.get(&owner)?;
                self.constructor
                    .get_mut(position)
                    .filter(|withheld| withheld.owner == owner)
            }
        }
    }

    fn get_exact(
        &self,
        namespace: WithheldNamespace,
        owner: Option<NominalTypeId>,
    ) -> Option<&WithheldExport> {
        match namespace {
            WithheldNamespace::Term => self
                .term
                .as_ref()
                .filter(|withheld| withheld.owner == owner),
            WithheldNamespace::Nominal => self
                .nominal
                .as_ref()
                .filter(|withheld| withheld.owner == owner),
            WithheldNamespace::Constructor => {
                let position = *self.constructor_positions.get(&owner)?;
                self.constructor
                    .get(position)
                    .filter(|withheld| withheld.owner == owner)
            }
        }
    }

    fn get_ordered(&self, entry: &WithheldOrderEntry) -> Option<&WithheldExport> {
        if entry.namespace != WithheldNamespace::Constructor {
            if entry.constructor_index.is_some() {
                return None;
            }
            return self.get_exact(entry.namespace, entry.owner);
        }
        let position = entry.constructor_index?;
        let withheld = self.constructor.get(position)?;
        (withheld.owner == entry.owner
            && self.constructor_positions.get(&entry.owner) == Some(&position))
        .then_some(withheld)
    }

    fn try_reserve(&mut self, namespace: WithheldNamespace, additional: usize) -> Result<(), ()> {
        if namespace == WithheldNamespace::Constructor {
            self.constructor.try_reserve(additional).map_err(|_| ())?;
            self.constructor_positions
                .try_reserve(additional)
                .map_err(|_| ())?;
        }
        Ok(())
    }

    fn insert_new(
        &mut self,
        namespace: WithheldNamespace,
        withheld: WithheldExport,
    ) -> Option<usize> {
        match namespace {
            WithheldNamespace::Term => {
                debug_assert!(self.term.is_none());
                self.term = Some(withheld);
                None
            }
            WithheldNamespace::Nominal => {
                debug_assert!(self.nominal.is_none());
                self.nominal = Some(withheld);
                None
            }
            WithheldNamespace::Constructor => {
                let position = self.constructor.len();
                let replaced = self.constructor_positions.insert(withheld.owner, position);
                debug_assert!(replaced.is_none());
                self.constructor.push(withheld);
                Some(position)
            }
        }
    }

    fn iter(&self) -> impl Iterator<Item = &WithheldExport> {
        self.term
            .iter()
            .chain(self.nominal.iter())
            .chain(self.constructor.iter())
    }

    fn into_values(self) -> impl Iterator<Item = WithheldExport> {
        let Self {
            term,
            nominal,
            constructor,
            constructor_positions,
        } = self;
        drop(constructor_positions);
        term.into_iter().chain(nominal).chain(constructor)
    }
}

/// Source access for one exported nominal type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExportedTypeAccess {
    /// The nominal name is available, but its constructors are not.
    Opaque,
    /// The nominal name and complete constructor set are available.
    Transparent,
}

/// Source access retained with one imported nominal identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImportedTypeAccess {
    /// The identity is usable through schemes but has no source name.
    Hidden,
    /// The nominal has a source name but no constructor access.
    Opaque,
    /// The nominal and selected transparent constructors are accessible.
    Transparent,
}

impl From<ExportedTypeAccess> for ImportedTypeAccess {
    fn from(access: ExportedTypeAccess) -> Self {
        match access {
            ExportedTypeAccess::Opaque => Self::Opaque,
            ExportedTypeAccess::Transparent => Self::Transparent,
        }
    }
}

impl ImportedTypeAccess {
    const fn rank(self) -> u8 {
        match self {
            Self::Hidden => 0,
            Self::Opaque => 1,
            Self::Transparent => 2,
        }
    }
}

/// One checked public global in an immutable export summary.
#[derive(Debug, Eq, PartialEq)]
pub struct ExportedGlobal {
    /// Stable binder identity from the defining module.
    pub binder: BinderId,
    /// Fully zonked closed constrained rank-1 scheme.
    pub scheme: ConstrainedScheme,
    /// Causal declaration provenance.
    pub origin: Origin,
}

/// One public nominal in an immutable export summary.
#[derive(Debug, Eq, PartialEq)]
pub struct ExportedType {
    /// Stable nominal identity from the defining module.
    pub id: NominalTypeId,
    /// Number of declared parameters.
    pub parameter_count: usize,
    /// Defining constructor-family cardinality, retained independently of access.
    pub(crate) constructor_count: usize,
    /// Ordered declaration parameters, preserving defining identities.
    pub parameters: Box<[ResolvedTypeVariable]>,
    /// Complete constructor family for transparent access.
    pub constructors: Box<[ConstructorId]>,
    /// Opaque or transparent importer access.
    pub access: ExportedTypeAccess,
    /// Causal declaration provenance.
    pub origin: Origin,
}

/// One transparent constructor in an immutable export summary.
#[derive(Debug, Eq, PartialEq)]
pub struct ExportedConstructor {
    /// Stable constructor identity from the defining module.
    pub id: ConstructorId,
    /// Defining source spelling.
    pub spelling: String,
    /// Optional semantic payload type.
    pub payload: Option<Type>,
    /// Canonical checked rank-1 constructor scheme.
    pub scheme: ConstrainedScheme,
    /// Causal declaration provenance.
    pub origin: Origin,
}

impl ExportedConstructor {
    /// Consumes a standalone exported constructor and dismantles its optional
    /// payload without recursive type drop.
    pub fn discard_iteratively(self) {
        drop(self.scheme);
        if let Some(payload) = self.payload {
            discard_type_iteratively(payload);
        }
        discard_origin_iteratively(self.origin);
    }
}

fn canonical_constructor_scheme(
    owner: NominalTypeId,
    parameters: &[ResolvedTypeVariable],
    payload: Option<&Type>,
    type_work: &mut TypeWorkBudget,
) -> Result<ConstrainedScheme, ()> {
    let payload = payload
        .map(|payload| clone_type_with_budget(payload, type_work).map(IterativeTypeOwner::new))
        .transpose()?;

    type_work.charge(parameters.len())?;
    let mut type_parameters = Vec::new();
    type_parameters
        .try_reserve_exact(parameters.len())
        .map_err(|_| ())?;
    for parameter in parameters {
        type_parameters.push((
            parameter.id,
            clone_kind_with_budget(&parameter.kind, type_work)?,
        ));
    }

    let result_nodes = parameters
        .len()
        .checked_mul(2)
        .and_then(|nodes| nodes.checked_add(1))
        .ok_or(())?;
    type_work.charge(result_nodes)?;
    let mut result = Type::Nominal(owner);
    for parameter in parameters {
        result = Type::Application(Box::new(result), Box::new(Type::Variable(parameter.id)));
    }
    let result = IterativeTypeOwner::new(result);

    let value_type = if let Some(payload) = payload {
        type_work.charge(1)?;
        Type::Function(
            Box::new(payload.into_inner()),
            Box::new(result.into_inner()),
        )
    } else {
        result.into_inner()
    };
    Ok(ConstrainedScheme {
        type_parameters: type_parameters.into_boxed_slice(),
        requirements: Box::new([]),
        value_type,
    })
}

/// Private canonical method-binder authority retained with one checked interface.
#[derive(Debug, Eq, PartialEq)]
struct MethodBinderAuthority {
    method: MethodId,
    parameters: Box<[ResolvedTypeVariable]>,
}

impl Drop for MethodBinderAuthority {
    fn drop(&mut self) {
        for parameter in std::mem::take(&mut self.parameters).into_vec() {
            discard_resolved_type_variable(parameter);
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct ExportSummary {
    module: ModuleId,
    terms: HashMap<String, ExportedGlobal>,
    term_order: Vec<String>,
    nominals: HashMap<String, ExportedType>,
    nominal_order: Vec<String>,
    nominal_names_by_id: HashMap<NominalTypeId, String>,
    constructors: HashMap<String, ExportedConstructor>,
    constructor_order: Vec<String>,
    constructor_names_by_id: HashMap<ConstructorId, String>,
    hidden_constructors: HashMap<ConstructorId, ExportedConstructor>,
    hidden_constructor_order: Vec<ConstructorId>,
    interface_names: HashMap<String, InterfaceId>,
    interface_name_order: Vec<String>,
    method_names: HashMap<String, MethodId>,
    method_name_order: Vec<String>,
    interfaces: Vec<CheckedInterfaceFact>,
    interface_positions: HashMap<InterfaceId, usize>,
    hidden_interfaces: Vec<CheckedInterfaceFact>,
    implementations: Vec<AuthorizedImplementationFact>,
    implementation_positions: HashMap<ImplId, usize>,
    hidden_nominals: HashMap<NominalTypeId, ExportedHiddenType>,
    hidden_nominal_order: Vec<NominalTypeId>,
    withheld: HashMap<String, WithheldExports>,
    withheld_order: Vec<WithheldOrderEntry>,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum SummaryOrderForTest {
    Term,
    Nominal,
    Constructor,
    InterfaceName,
    MethodName,
    HiddenNominal,
    HiddenConstructor,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum SummaryDuplicateFactForTest {
    Global,
    GlobalValueType,
    GlobalRequirementOrigin,
    GlobalRequirementSpan,
    Nominal,
    NominalParameterOrigin,
    Constructor,
    ConstructorOrigin,
    Interface,
    InterfaceOrigin,
    InterfaceSpan,
    InterfaceParameterOrigin,
    InterfaceMethodSpan,
    InterfaceWithoutImplementationType,
    Implementation,
    ImplementationOrigin,
    ImplementationSpan,
    ImplementationHeadParameterOrigin,
    ImplementationHeadArgument,
    ImplementationPrerequisiteOrigin,
    ImplementationPrerequisiteSpan,
    ImplementationPrerequisiteType,
    ImplementationMethodSpan,
    OpaqueNominalKindClosure,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum SummaryWithheldMutationForTest {
    TermKind,
    TermOwner,
    NominalKind,
    NominalOwner,
    ConstructorOwner,
    ConstructorPosition,
    MapOnly,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum SummaryCarrierMutationForTest {
    PublicNominalKind,
    PublicNominalParameterIdentity,
    PublicNominalParameterOwner,
    PublicNominalParameterOrder,
    PublicConstructorFamilyOrdinal,
    PublicConstructorFamilyOwner,
    PublicConstructorResultOwner,
    HiddenNominalKind,
    HiddenNominalParameterIdentity,
    HiddenNominalParameterOwner,
    HiddenNominalParameterOrder,
    HiddenNominalAccess,
    PublicConstructorPayload,
    PublicConstructorPayloadDomainKind,
    HiddenConstructorPayload,
    HiddenConstructorPayloadDomainKind,
    PublicConstructorSchemeKind,
    PublicConstructorSchemeParameterIdentity,
    HiddenConstructorSchemeKind,
    HiddenConstructorSchemeParameterIdentity,
    HiddenConstructorResultOwner,
    PublicInterfaceKind,
    PublicInterfaceParameterIdentity,
    PublicInterfaceParameterOwner,
    HiddenInterfaceKind,
    HiddenInterfaceParameterIdentity,
    HiddenInterfaceParameterOwner,
    HiddenInterfaceIdentity,
    PublicInterfaceMethodType,
    PublicInterfaceMethodNonFunction,
    PublicInterfaceEmptyMethods,
    HiddenInterfaceMethodType,
    HiddenInterfaceMethodIdentity,
    HiddenInterfaceMethodOwner,
    PublicInterfaceMethodFreeBinder,
    HiddenInterfaceMethodFreeBinder,
    PublicInterfaceMethodKind,
    HiddenInterfaceMethodKind,
    InterfaceIdentity,
    MethodIdentity,
    MethodOrdinal,
    InterfaceNameTarget,
    MethodNameTarget,
    GlobalParameterIdentity,
    GlobalParameterOrder,
    GlobalUnusedParameter,
    GlobalRequirementIdentity,
    GlobalRequirementInterface,
    GlobalRequirementArgumentKind,
    GlobalParameterOwner,
    GlobalParameterKind,
    ImplementationHeadKind,
    ImplementationHeadIdentity,
    ImplementationHeadOrder,
    ImplementationHeadOwner,
    ImplementationArgument,
    ImplementationSemanticHead,
    ImplementationInterfaceIdentity,
    ImplementationPrerequisiteIdentity,
    ImplementationPrerequisiteOrder,
    ImplementationPrerequisiteDuplicate,
    ImplementationPrerequisiteKind,
    ImplementationPrerequisiteInterface,
    ImplementationPrerequisiteArgument,
    ImplementationPrerequisiteOriginMirror,
    ImplementationPrerequisiteSpanMirror,
    ImplementationMethodRequirementIdentity,
    ImplementationMethodSchemeParameterIdentity,
    ImplementationMethodSchemeParameterKind,
    ImplementationMethodIdentity,
    ImplementationMethodMapping,
    ImplementationMethodBinder,
    ImplementationAuthorization,
    ImplementationOverlap,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum SummaryConstructorFusionMutationForTest {
    UnboundPayloadVariable,
    RegisteredForeignPayloadVariable,
    InferencePayload,
    OuterForallPayload,
    NestedForallPayload,
    UnexpectedRequirement,
    ResultSpineTooShort,
    ResultSpineExtra,
    ResultArgumentSwap,
    ResultArgumentDuplicate,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum SummaryHiddenDiamondMutationForTest {
    NominalOrigin,
    NominalParameterOrigin,
    ConstructorOrigin,
    InterfaceOrigin,
    InterfaceParameterOrigin,
    InterfaceMethodOrigin,
    InterfaceMethodSpan,
    InterfaceMethodType,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ResolvedBuildFailure {
    InvalidState,
    TypeResource,
    ConstraintResource,
}

fn reserve_summary_implementation_storage(
    implementations: &mut Vec<AuthorizedImplementationFact>,
    positions: &mut HashMap<ImplId, usize>,
    retained_count: usize,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    let storage_work = retained_count
        .checked_mul(2)
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    constraint_work
        .charge(storage_work)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    implementations
        .try_reserve_exact(retained_count)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    positions
        .try_reserve(retained_count)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)
}

/// One hidden nominal fact retained by identity without a source name binding.
#[derive(Debug, Eq, PartialEq)]
pub struct ExportedHiddenType {
    /// Stable nominal identity from the defining module.
    pub id: NominalTypeId,
    /// Number of declared parameters.
    pub parameter_count: usize,
    /// Defining constructor-family cardinality, retained independently of access.
    pub(crate) constructor_count: usize,
    /// Ordered declaration parameters, preserving defining identities.
    pub parameters: Box<[ResolvedTypeVariable]>,
    /// Complete constructor family retained without source spellings.
    pub constructors: Box<[ConstructorId]>,
    /// Access metadata retained for a name-re-exported constructor family.
    pub access: ImportedTypeAccess,
    /// Display-only declaration spelling.
    pub spelling: String,
    /// Whether the displayed declaration spelling is private at its definition.
    pub display_is_private: bool,
    /// Causal declaration provenance.
    pub origin: Origin,
}

fn authenticate_identity_order<K: Copy + Eq + Hash, V>(
    facts: &HashMap<K, V>,
    order: &[K],
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    constraint_work
        .charge(order.len())
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    if facts.len() != order.len() {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    let mut seen = HashSet::new();
    seen.try_reserve(order.len())
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    for identity in order {
        if !seen.insert(*identity) || !facts.contains_key(identity) {
            return Err(ResolvedBuildFailure::InvalidState);
        }
    }
    Ok(())
}

fn map_summary_kind_failure(failure: KindFailure) -> ResolvedBuildFailure {
    match failure {
        KindFailure::Resource(_) => ResolvedBuildFailure::TypeResource,
        KindFailure::Internal(_) | KindFailure::Source(_) => ResolvedBuildFailure::InvalidState,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SummaryBinderOwner {
    Nominal(NominalTypeId),
    Interface(InterfaceId),
    Method(MethodId),
    Global(BinderId),
    Implementation(ImplId),
}

fn register_summary_parameter<'a>(
    identity: TypeVariableId,
    kind: &'a Kind,
    owner: SummaryBinderOwner,
    origin: Span,
    canonical: &mut HashMap<TypeVariableId, (&'a Kind, Span, SummaryBinderOwner)>,
    environments: &mut KindEnvironments<'a>,
    type_work: &mut TypeWorkBudget,
) -> Result<(), ResolvedBuildFailure> {
    type_work
        .charge(1)
        .map_err(|()| ResolvedBuildFailure::TypeResource)?;
    let expected_module = match owner {
        SummaryBinderOwner::Nominal(identity) => identity.module(),
        SummaryBinderOwner::Interface(identity) => identity.module(),
        SummaryBinderOwner::Method(identity) => identity.interface().module(),
        SummaryBinderOwner::Global(identity) => identity
            .module()
            .ok_or(ResolvedBuildFailure::InvalidState)?,
        SummaryBinderOwner::Implementation(identity) => identity.module(),
    };
    if identity.module() != Some(expected_module) {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    if let Some((existing, _, existing_owner)) = canonical.get(&identity) {
        if *existing_owner != owner
            || !same_kind_with_charge(existing, kind, || type_work.charge(1))
                .map_err(|()| ResolvedBuildFailure::TypeResource)?
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        return Ok(());
    }
    canonical
        .try_reserve(1)
        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
    environments
        .insert_declared(identity, kind, origin, type_work)
        .map_err(map_summary_kind_failure)?;
    canonical.insert(identity, (kind, origin, owner));
    Ok(())
}

fn register_summary_parameters<'a>(
    parameters: &'a [ResolvedTypeVariable],
    owner: SummaryBinderOwner,
    canonical: &mut HashMap<TypeVariableId, (&'a Kind, Span, SummaryBinderOwner)>,
    environments: &mut KindEnvironments<'a>,
    type_work: &mut TypeWorkBudget,
) -> Result<(), ResolvedBuildFailure> {
    let mut previous = None;
    for parameter in parameters {
        if previous.is_some_and(|previous| parameter.id.local() <= previous) {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        previous = Some(parameter.id.local());
        register_summary_parameter(
            parameter.id,
            &parameter.kind,
            owner,
            parameter.origin.primary_span(),
            canonical,
            environments,
            type_work,
        )?;
    }
    Ok(())
}

fn register_summary_scheme_parameters<'a>(
    parameters: &'a [(TypeVariableId, Kind)],
    owner: SummaryBinderOwner,
    origin: Span,
    canonical: &mut HashMap<TypeVariableId, (&'a Kind, Span, SummaryBinderOwner)>,
    environments: &mut KindEnvironments<'a>,
    type_work: &mut TypeWorkBudget,
) -> Result<(), ResolvedBuildFailure> {
    let mut previous = None;
    for (identity, kind) in parameters {
        if previous.is_some_and(|previous| identity.local() <= previous) {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        previous = Some(identity.local());
        register_summary_parameter(
            *identity,
            kind,
            owner,
            origin,
            canonical,
            environments,
            type_work,
        )?;
    }
    Ok(())
}

fn authenticate_summary_type_variables(
    root: &Type,
    parameters: impl ExactSizeIterator<Item = TypeVariableId>,
    type_work: &mut TypeWorkBudget,
) -> Result<(), ResolvedBuildFailure> {
    let parameter_count = parameters.len();
    type_work
        .charge(parameter_count)
        .map_err(|()| ResolvedBuildFailure::TypeResource)?;
    let mut allowed = HashSet::new();
    allowed
        .try_reserve(parameter_count)
        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
    allowed.extend(parameters);

    type_work
        .charge(1)
        .map_err(|()| ResolvedBuildFailure::TypeResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
    pending.push(root);
    while let Some(ty) = pending.pop() {
        type_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        match ty {
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) => {}
            Type::Variable(identity) if allowed.contains(identity) => {}
            Type::Variable(_) | Type::Inference(_) | Type::Forall(_, _) => {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            Type::Tuple(elements) => {
                type_work
                    .charge(elements.len())
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                pending.extend(elements.iter().rev());
            }
            Type::Application(function, argument) | Type::Function(function, argument) => {
                type_work
                    .charge(2)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                pending.push(argument);
                pending.push(function);
            }
        }
    }
    Ok(())
}

fn collect_summary_constraint_variables(
    root: &Type,
    output: &mut HashSet<TypeVariableId>,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    pending.push(root);
    while let Some(ty) = pending.pop() {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        match ty {
            Type::Variable(identity) => {
                constraint_work
                    .charge(1)
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                output
                    .try_reserve(1)
                    .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
                output.insert(*identity);
            }
            Type::Tuple(elements) => {
                constraint_work
                    .charge(elements.len())
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
                pending.extend(elements.iter().rev());
            }
            Type::Application(function, argument) | Type::Function(function, argument) => {
                constraint_work
                    .charge(2)
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
                pending.push(argument);
                pending.push(function);
            }
            Type::Forall(_, _) | Type::Inference(_) => {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) => {}
        }
    }
    Ok(())
}

fn summary_parameter_id_set(
    parameters: impl ExactSizeIterator<Item = TypeVariableId>,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<HashSet<TypeVariableId>, ResolvedBuildFailure> {
    let parameter_count = parameters.len();
    constraint_work
        .charge(parameter_count)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    let mut identities = HashSet::new();
    identities
        .try_reserve(parameter_count)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    for identity in parameters {
        if !identities.insert(identity) {
            return Err(ResolvedBuildFailure::InvalidState);
        }
    }
    Ok(identities)
}

fn authenticate_exact_global_scheme_binders(
    scheme: &ConstrainedScheme,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    let parameters = summary_parameter_id_set(
        scheme.type_parameters.iter().map(|(identity, _)| *identity),
        constraint_work,
    )?;
    let mut value_variables = HashSet::new();
    collect_summary_constraint_variables(
        scheme.value_type(),
        &mut value_variables,
        constraint_work,
    )?;
    if value_variables != parameters {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    for requirement in &scheme.requirements {
        let mut requirement_variables = HashSet::new();
        collect_summary_constraint_variables(
            requirement.argument(),
            &mut requirement_variables,
            constraint_work,
        )?;
        constraint_work
            .charge(requirement_variables.len())
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if requirement_variables
            .iter()
            .any(|identity| !value_variables.contains(identity))
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
    }
    Ok(())
}

fn authenticate_exact_implementation_binders(
    fact: &CheckedImplementationFact,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    let parameters = summary_parameter_id_set(
        fact.head_parameters.iter().map(|parameter| parameter.id),
        constraint_work,
    )?;
    let mut head_variables = HashSet::new();
    collect_summary_constraint_variables(fact.argument(), &mut head_variables, constraint_work)?;
    if head_variables != parameters {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    for prerequisite in &fact.prerequisites {
        let mut prerequisite_variables = HashSet::new();
        collect_summary_constraint_variables(
            prerequisite.argument(),
            &mut prerequisite_variables,
            constraint_work,
        )?;
        constraint_work
            .charge(prerequisite_variables.len())
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if prerequisite_variables
            .iter()
            .any(|identity| !head_variables.contains(identity))
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
    }
    Ok(())
}

fn authenticate_scheme_parameter_mirror(
    scheme: &ConstrainedScheme,
    parameters: &[ResolvedTypeVariable],
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    if scheme.type_parameters.len() != parameters.len() {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    for ((identity, kind), parameter) in scheme.type_parameters.iter().zip(parameters) {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if *identity != parameter.id
            || !same_kind_with_constraint_budget(kind, &parameter.kind, constraint_work)?
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
    }
    Ok(())
}

fn authenticate_implementation_method_parameter_mirror(
    method: &CheckedImplementationMethodFact,
    head_parameters: &[ResolvedTypeVariable],
    method_parameters: &[ResolvedTypeVariable],
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    let expected_count = head_parameters
        .len()
        .checked_add(method_parameters.len())
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    if method.head_type_parameter_count != head_parameters.len()
        || method.scheme.type_parameters.len() != expected_count
    {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    let (scheme_head, scheme_method) = method
        .scheme
        .type_parameters
        .split_at(method.head_type_parameter_count);
    for ((identity, kind), parameter) in scheme_head.iter().zip(head_parameters) {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if *identity != parameter.id
            || !same_kind_with_constraint_budget(kind, &parameter.kind, constraint_work)?
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
    }
    for ((identity, kind), parameter) in scheme_method.iter().zip(method_parameters) {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if *identity != parameter.id
            || !same_kind_with_constraint_budget(kind, &parameter.kind, constraint_work)?
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
    }
    Ok(())
}

fn same_kind_with_constraint_budget(
    left: &Kind,
    right: &Kind,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    pending.push((left, right));
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (Kind::Type, Kind::Type) => {}
            (
                Kind::Arrow(left_domain, left_codomain),
                Kind::Arrow(right_domain, right_codomain),
            ) => {
                constraint_work
                    .charge(2)
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
                pending.push((left_codomain, right_codomain));
                pending.push((left_domain, right_domain));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn same_origin_with_constraint_budget(
    mut left: &Origin,
    mut right: &Origin,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    loop {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        match (left, right) {
            (Origin::Source(left), Origin::Source(right)) => return Ok(left == right),
            (
                Origin::Generated {
                    cause: left_cause,
                    reason: left_reason,
                },
                Origin::Generated {
                    cause: right_cause,
                    reason: right_reason,
                },
            ) if left_reason == right_reason => {
                left = left_cause;
                right = right_cause;
            }
            (
                Origin::Related {
                    primary: left_primary,
                    related: left_related,
                },
                Origin::Related {
                    primary: right_primary,
                    related: right_related,
                },
            ) if left_related.len() == right_related.len() => {
                constraint_work
                    .charge(left_related.len())
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                if left_related != right_related {
                    return Ok(false);
                }
                left = left_primary;
                right = right_primary;
            }
            _ => return Ok(false),
        }
    }
}

fn same_summary_resolved_type_variables_with_constraint_budget(
    left: &[ResolvedTypeVariable],
    right: &[ResolvedTypeVariable],
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if left.id != right.id
            || left.spelling != right.spelling
            || !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)?
            || !same_kind_with_constraint_budget(&left.kind, &right.kind, constraint_work)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn same_checker_type_variable_after_base_charge(
    left: &ResolvedTypeVariable,
    right: &ResolvedTypeVariable,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    if left.id != right.id || left.spelling != right.spelling {
        return Ok(false);
    }
    if !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)? {
        return Ok(false);
    }
    same_kind_with_constraint_budget(&left.kind, &right.kind, constraint_work)
}

fn same_constrained_schemes_with_constraint_budget(
    left: &ConstrainedScheme,
    right: &ConstrainedScheme,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    if left.type_parameters.len() != right.type_parameters.len()
        || left.requirements.len() != right.requirements.len()
    {
        return Ok(false);
    }
    for ((left_identity, left_kind), (right_identity, right_kind)) in left
        .type_parameters
        .iter()
        .zip(right.type_parameters.iter())
    {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if left_identity != right_identity
            || !same_kind_with_constraint_budget(left_kind, right_kind, constraint_work)?
        {
            return Ok(false);
        }
    }
    for (left, right) in left.requirements.iter().zip(right.requirements.iter()) {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if left.id != right.id
            || left.interface != right.interface
            || left.span != right.span
            || !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)?
            || !same_type_with_constraint_budget(left.argument(), right.argument(), constraint_work)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
        {
            return Ok(false);
        }
    }
    same_type_with_constraint_budget(left.value_type(), right.value_type(), constraint_work)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)
}

fn same_constrained_schemes_with_constraint_budget_observing_nominals(
    left: &ConstrainedScheme,
    right: &ConstrainedScheme,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    nominal_identities: &mut MatchedNominalIdentities,
) -> Result<bool, ResolvedBuildFailure> {
    if left.type_parameters.len() != right.type_parameters.len()
        || left.requirements.len() != right.requirements.len()
    {
        return Ok(false);
    }
    for ((left_identity, left_kind), (right_identity, right_kind)) in left
        .type_parameters
        .iter()
        .zip(right.type_parameters.iter())
    {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if left_identity != right_identity
            || !same_kind_with_constraint_budget(left_kind, right_kind, constraint_work)?
        {
            return Ok(false);
        }
    }
    for (left, right) in left.requirements.iter().zip(right.requirements.iter()) {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if left.id != right.id
            || left.interface != right.interface
            || left.span != right.span
            || !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)?
            || !same_type_with_constraint_budget_observing_nominals(
                left.argument(),
                right.argument(),
                constraint_work,
                nominal_identities,
            )
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
        {
            return Ok(false);
        }
    }
    same_type_with_constraint_budget_observing_nominals(
        left.value_type(),
        right.value_type(),
        constraint_work,
        nominal_identities,
    )
    .map_err(|()| ResolvedBuildFailure::ConstraintResource)
}

#[cfg(test)]
pub(crate) fn same_imported_global_fact_with_budget(
    left: &ImportedGlobalScheme,
    right: &ExportedGlobal,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    same_imported_global_fact_with_optional_nominal_observer(
        left,
        right,
        type_work,
        constraint_work,
        None,
    )
}

pub(crate) fn same_imported_global_fact_observing_nominals_with_budget(
    left: &ImportedGlobalScheme,
    right: &ExportedGlobal,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    nominal_identities: &mut MatchedNominalIdentities,
) -> Result<bool, ResolvedBuildFailure> {
    same_imported_global_fact_with_optional_nominal_observer(
        left,
        right,
        type_work,
        constraint_work,
        Some(nominal_identities),
    )
}

fn same_imported_global_fact_with_optional_nominal_observer(
    left: &ImportedGlobalScheme,
    right: &ExportedGlobal,
    _type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    nominal_identities: Option<&mut MatchedNominalIdentities>,
) -> Result<bool, ResolvedBuildFailure> {
    if left.binder != right.binder {
        return Ok(false);
    }
    let metadata_work = right
        .scheme
        .type_parameters
        .len()
        .checked_add(right.scheme.requirements.len())
        .and_then(|work| work.checked_add(1))
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    constraint_work
        .charge(metadata_work)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    if !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)? {
        return Ok(false);
    }
    match nominal_identities {
        Some(nominal_identities) => {
            same_constrained_schemes_with_constraint_budget_observing_nominals(
                &left.scheme,
                &right.scheme,
                constraint_work,
                nominal_identities,
            )
        }
        None => same_constrained_schemes_with_constraint_budget(
            &left.scheme,
            &right.scheme,
            constraint_work,
        ),
    }
}

pub(crate) fn same_imported_nominal_closure_with_constraint_budget(
    left: &ImportedNominalFact,
    right: ImportedNominalFactRef<'_>,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    let defining_spelling_matches =
        !left.display_is_private || left.display_spelling.as_deref() == right.display_spelling;
    if left.id != right.id
        || left.parameter_count != right.parameter_count
        || left.constructor_count != right.constructor_count
        || left.parameters.len() != right.parameters.len()
        || left.display_is_private != right.display_is_private
        || !defining_spelling_matches
    {
        return Ok(false);
    }
    for (left, right) in left.parameters.iter().zip(right.parameters) {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if left.id != right.id
            || left.spelling != right.spelling
            || !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)?
            || !same_kind_with_constraint_budget(&left.kind, &right.kind, constraint_work)?
        {
            return Ok(false);
        }
    }
    same_origin_with_constraint_budget(&left.origin, right.origin, constraint_work)
}

#[cfg(test)]
pub(crate) fn same_imported_constructor_fact_with_budget(
    left: &ImportedConstructorFact,
    right: &ExportedConstructor,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    same_imported_constructor_fact_with_optional_nominal_observer(
        left,
        right,
        type_work,
        constraint_work,
        None,
    )
}

pub(crate) fn same_imported_constructor_fact_observing_nominals_with_budget(
    left: &ImportedConstructorFact,
    right: &ExportedConstructor,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    nominal_identities: &mut MatchedNominalIdentities,
) -> Result<bool, ResolvedBuildFailure> {
    same_imported_constructor_fact_with_optional_nominal_observer(
        left,
        right,
        type_work,
        constraint_work,
        Some(nominal_identities),
    )
}

fn same_imported_constructor_fact_with_optional_nominal_observer(
    left: &ImportedConstructorFact,
    right: &ExportedConstructor,
    _type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    mut nominal_identities: Option<&mut MatchedNominalIdentities>,
) -> Result<bool, ResolvedBuildFailure> {
    if left.id != right.id || left.spelling != right.spelling {
        return Ok(false);
    }
    let metadata_work = right
        .scheme
        .type_parameters
        .len()
        .checked_add(right.scheme.requirements.len())
        .and_then(|work| work.checked_add(1))
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    constraint_work
        .charge(metadata_work)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    if !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)?
        || !match nominal_identities.as_deref_mut() {
            Some(nominal_identities) => {
                same_constrained_schemes_with_constraint_budget_observing_nominals(
                    &left.scheme,
                    &right.scheme,
                    constraint_work,
                    nominal_identities,
                )
            }
            None => same_constrained_schemes_with_constraint_budget(
                &left.scheme,
                &right.scheme,
                constraint_work,
            ),
        }?
    {
        return Ok(false);
    }
    match (&left.payload, &right.payload) {
        (None, None) => Ok(true),
        (Some(left), Some(right)) => match nominal_identities {
            Some(nominal_identities) => same_type_with_constraint_budget_observing_nominals(
                left,
                right,
                constraint_work,
                nominal_identities,
            ),
            None => same_type_with_constraint_budget(left, right, constraint_work),
        }
        .map_err(|()| ResolvedBuildFailure::ConstraintResource),
        _ => Ok(false),
    }
}

#[cfg(test)]
pub(crate) fn same_checked_interface_fact_with_budget(
    left: &CheckedInterfaceFact,
    right: &CheckedInterfaceFact,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    same_checked_interface_fact_with_optional_nominal_observer(
        left,
        right,
        type_work,
        constraint_work,
        None,
    )
}

pub(crate) fn same_checked_interface_fact_observing_nominals_with_budget(
    left: &CheckedInterfaceFact,
    right: &CheckedInterfaceFact,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    nominal_identities: &mut MatchedNominalIdentities,
) -> Result<bool, ResolvedBuildFailure> {
    same_checked_interface_fact_with_optional_nominal_observer(
        left,
        right,
        type_work,
        constraint_work,
        Some(nominal_identities),
    )
}

fn same_checked_interface_fact_with_optional_nominal_observer(
    left: &CheckedInterfaceFact,
    right: &CheckedInterfaceFact,
    _type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    mut nominal_identities: Option<&mut MatchedNominalIdentities>,
) -> Result<bool, ResolvedBuildFailure> {
    if left.id != right.id
        || left.spelling != right.spelling
        || left.span != right.span
        || left.methods.len() != right.methods.len()
    {
        return Ok(false);
    }
    authenticate_method_binder_authority(left, None, constraint_work)?;
    authenticate_method_binder_authority(right, None, constraint_work)?;
    let metadata_work = right
        .methods
        .len()
        .checked_add(1)
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    constraint_work
        .charge(metadata_work)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    if !same_summary_resolved_type_variables_with_constraint_budget(
        std::slice::from_ref(&left.parameter),
        std::slice::from_ref(&right.parameter),
        constraint_work,
    )? || !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)?
    {
        return Ok(false);
    }
    for (left, right) in left.methods.iter().zip(&right.methods) {
        if left.id != right.id
            || left.spelling != right.spelling
            || left.span != right.span
            || !same_summary_resolved_type_variables_with_constraint_budget(
                left.type_parameters(),
                right.type_parameters(),
                constraint_work,
            )?
            || !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)?
            || !match nominal_identities.as_deref_mut() {
                Some(nominal_identities) => same_type_with_constraint_budget_observing_nominals(
                    left.value_type(),
                    right.value_type(),
                    constraint_work,
                    nominal_identities,
                ),
                None => same_type_with_constraint_budget(
                    left.value_type(),
                    right.value_type(),
                    constraint_work,
                ),
            }
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
pub(crate) fn same_checked_implementation_fact_with_budget(
    left: &CheckedImplementationFact,
    right: &CheckedImplementationFact,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    same_checked_implementation_fact_with_optional_nominal_observer(
        left,
        right,
        type_work,
        constraint_work,
        None,
    )
}

pub(crate) fn same_checked_implementation_fact_observing_nominals_with_budget(
    left: &CheckedImplementationFact,
    right: &CheckedImplementationFact,
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    nominal_identities: &mut MatchedNominalIdentities,
) -> Result<bool, ResolvedBuildFailure> {
    same_checked_implementation_fact_with_optional_nominal_observer(
        left,
        right,
        type_work,
        constraint_work,
        Some(nominal_identities),
    )
}

fn same_checked_implementation_fact_with_optional_nominal_observer(
    left: &CheckedImplementationFact,
    right: &CheckedImplementationFact,
    _type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    mut nominal_identities: Option<&mut MatchedNominalIdentities>,
) -> Result<bool, ResolvedBuildFailure> {
    if left.id != right.id
        || left.interface != right.interface
        || left.span != right.span
        || left.prerequisites.len() != right.prerequisites.len()
        || left.methods.len() != right.methods.len()
    {
        return Ok(false);
    }
    let metadata_work = right
        .head_parameters
        .len()
        .checked_add(right.prerequisites.len())
        .and_then(|work| work.checked_add(right.methods.len()))
        .and_then(|work| work.checked_add(1))
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    constraint_work
        .charge(metadata_work)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    if !same_summary_resolved_type_variables_with_constraint_budget(
        &left.head_parameters,
        &right.head_parameters,
        constraint_work,
    )? || !match nominal_identities.as_deref_mut() {
        Some(nominal_identities) => same_type_with_constraint_budget_observing_nominals(
            left.argument(),
            right.argument(),
            constraint_work,
            nominal_identities,
        ),
        None => {
            same_type_with_constraint_budget(left.argument(), right.argument(), constraint_work)
        }
    }
    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
        || !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)?
    {
        return Ok(false);
    }
    for (left, right) in left.prerequisites.iter().zip(&right.prerequisites) {
        if left.id != right.id
            || left.interface != right.interface
            || left.span != right.span
            || !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)?
            || !match nominal_identities.as_deref_mut() {
                Some(nominal_identities) => same_type_with_constraint_budget_observing_nominals(
                    left.argument(),
                    right.argument(),
                    constraint_work,
                    nominal_identities,
                ),
                None => same_type_with_constraint_budget(
                    left.argument(),
                    right.argument(),
                    constraint_work,
                ),
            }
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
        {
            return Ok(false);
        }
    }
    for (left, right) in left.methods.iter().zip(&right.methods) {
        if left.id != right.id
            || left.method != right.method
            || left.binder != right.binder
            || left.span != right.span
            || !same_origin_with_constraint_budget(&left.origin, &right.origin, constraint_work)?
            || !match nominal_identities.as_deref_mut() {
                Some(nominal_identities) => {
                    same_constrained_schemes_with_constraint_budget_observing_nominals(
                        &left.scheme,
                        &right.scheme,
                        constraint_work,
                        nominal_identities,
                    )
                }
                None => same_constrained_schemes_with_constraint_budget(
                    &left.scheme,
                    &right.scheme,
                    constraint_work,
                ),
            }?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn same_summary_type_after_single_substitution(
    source: &Type,
    parameter: TypeVariableId,
    argument: &Type,
    actual: &Type,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<bool, ResolvedBuildFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    pending.push((source, actual));
    while let Some((source, actual)) = pending.pop() {
        constraint_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if matches!(source, Type::Variable(identity) if *identity == parameter) {
            if !same_type_with_constraint_budget(argument, actual, constraint_work)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
            {
                return Ok(false);
            }
            continue;
        }
        match (source, actual) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                constraint_work
                    .charge(left.len())
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                pending
                    .try_reserve(left.len())
                    .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
                pending.extend(left.iter().zip(right.iter()).rev());
            }
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            )
            | (
                Type::Function(left_function, left_argument),
                Type::Function(right_function, right_argument),
            ) => {
                constraint_work
                    .charge(2)
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
                pending.push((left_argument, right_argument));
                pending.push((left_function, right_function));
            }
            (Type::Inference(_), _)
            | (_, Type::Inference(_))
            | (Type::Forall(_, _), _)
            | (_, Type::Forall(_, _)) => return Err(ResolvedBuildFailure::InvalidState),
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn authenticate_method_requirement_mirror(
    method_requirement: &CheckedRequirement,
    prerequisite: &CheckedRequirement,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    if method_requirement.id != prerequisite.id
        || method_requirement.interface != prerequisite.interface
        || method_requirement.span != prerequisite.span
        || !same_origin_with_constraint_budget(
            &method_requirement.origin,
            &prerequisite.origin,
            constraint_work,
        )?
        || !same_type_with_constraint_budget(
            method_requirement.argument(),
            prerequisite.argument(),
            constraint_work,
        )
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
    {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    Ok(())
}

fn authenticate_constructor_scheme(
    constructor: &ExportedConstructor,
    parameters: &[ResolvedTypeVariable],
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    authenticate_scheme_parameter_mirror(&constructor.scheme, parameters, constraint_work)?;
    if !constructor.scheme.requirements.is_empty() {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    let result = match (&constructor.payload, constructor.scheme.value_type()) {
        (Some(_), Type::Function(_, result)) => result.as_ref(),
        (None, result) => result,
        (Some(_), _) => return Err(ResolvedBuildFailure::InvalidState),
    };
    let mut result = result;
    for parameter in parameters.iter().rev() {
        type_work
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let Type::Application(function, argument) = result else {
            return Err(ResolvedBuildFailure::InvalidState);
        };
        if !matches!(argument.as_ref(), Type::Variable(identity) if *identity == parameter.id) {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        result = function;
    }
    type_work
        .charge(1)
        .map_err(|()| ResolvedBuildFailure::TypeResource)?;
    if !matches!(result, Type::Nominal(identity) if *identity == constructor.id.owner()) {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    Ok(())
}

#[derive(Default)]
struct SummaryRequirementIndex<'fact> {
    by_interface: HashMap<InterfaceId, Vec<&'fact CheckedRequirement>>,
}

impl<'fact> SummaryRequirementIndex<'fact> {
    fn observe(
        &mut self,
        requirement: &'fact CheckedRequirement,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<(), ResolvedBuildFailure> {
        if let Some(previous) = self.by_interface.get_mut(&requirement.interface) {
            for previous in previous.iter() {
                if same_type_with_constraint_budget(
                    previous.argument(),
                    requirement.argument(),
                    constraint_work,
                )
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
            constraint_work
                .charge(1)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
            previous
                .try_reserve(1)
                .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
            previous.push(requirement);
            return Ok(());
        }

        constraint_work
            .charge(2)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        self.by_interface
            .try_reserve(1)
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        let mut first = Vec::new();
        first
            .try_reserve_exact(1)
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        first.push(requirement);
        self.by_interface.insert(requirement.interface, first);
        Ok(())
    }
}

#[cfg(test)]
fn authenticate_unique_summary_requirements(
    requirements: &[CheckedRequirement],
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    let mut index = SummaryRequirementIndex::default();
    for requirement in requirements {
        index.observe(requirement, constraint_work)?;
    }
    Ok(())
}

fn authenticate_nonoverlapping_summary_implementations<'fact>(
    implementations: impl IntoIterator<Item = &'fact CheckedImplementationFact>,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    let mut by_interface: HashMap<InterfaceId, Vec<&CheckedImplementationFact>> = HashMap::new();
    for implementation in implementations {
        let fact = implementation;
        if let Some(previous) = by_interface.get_mut(&fact.interface) {
            for previous in previous.iter() {
                let overlaps = implementation_heads_overlap_structurally(
                    previous
                        .head_parameters
                        .iter()
                        .map(|parameter| parameter.id),
                    previous.argument(),
                    fact.head_parameters.iter().map(|parameter| parameter.id),
                    fact.argument(),
                    constraint_work,
                )
                .map_err(|failure| match failure {
                    OverlapFailure::InvalidState => ResolvedBuildFailure::InvalidState,
                    OverlapFailure::Resource => ResolvedBuildFailure::ConstraintResource,
                    OverlapFailure::TypeResource => ResolvedBuildFailure::TypeResource,
                })?;
                if overlaps {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
            constraint_work
                .charge(1)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
            previous
                .try_reserve(1)
                .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
            previous.push(fact);
            continue;
        }

        constraint_work
            .charge(2)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        by_interface
            .try_reserve(1)
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        let mut first = Vec::new();
        first
            .try_reserve_exact(1)
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        first.push(fact);
        by_interface.insert(fact.interface, first);
    }
    Ok(())
}

fn retain_hidden_interface_reference(
    interface: InterfaceId,
    public_interfaces: &HashMap<InterfaceId, usize>,
    referenced_interfaces: &mut HashSet<InterfaceId>,
    referenced_interface_order: &mut Vec<InterfaceId>,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    if public_interfaces.contains_key(&interface) || referenced_interfaces.contains(&interface) {
        return Ok(());
    }
    // The seen index and deterministic-order carrier are simultaneously live
    // until closure discovery completes, so each hidden identity owns one
    // charged slot in both transient collections.
    constraint_work
        .charge(2)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    referenced_interfaces
        .try_reserve(1)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    referenced_interface_order
        .try_reserve(1)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    let inserted = referenced_interfaces.insert(interface);
    debug_assert!(inserted);
    referenced_interface_order.push(interface);
    Ok(())
}

fn clone_resolved_method_binder_authorities(
    methods: &[ResolvedInterfaceMethod],
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<Vec<MethodBinderAuthority>, ResolvedBuildFailure> {
    let authority_count = methods.len();
    constraint_work
        .charge(authority_count)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    let mut authorities = Vec::new();
    authorities
        .try_reserve_exact(authority_count)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    for method in methods {
        let parameters =
            clone_resolved_type_variable_buffer_with_budget(&method.type_parameters, type_work)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        authorities.push(MethodBinderAuthority {
            method: method.id,
            parameters: parameters.into_boxed_slice(),
        });
    }
    Ok(authorities)
}

fn clone_method_binder_authority_rows(
    source: &[MethodBinderAuthority],
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<Vec<MethodBinderAuthority>, ResolvedBuildFailure> {
    constraint_work
        .charge(source.len())
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    let mut authorities = Vec::new();
    authorities
        .try_reserve_exact(source.len())
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    for authority in source {
        let parameters =
            clone_resolved_type_variable_buffer_with_budget(&authority.parameters, type_work)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        authorities.push(MethodBinderAuthority {
            method: authority.method,
            parameters: parameters.into_boxed_slice(),
        });
    }
    Ok(authorities)
}

fn authenticate_method_binder_authority(
    interface: &CheckedInterfaceFact,
    source_methods: Option<&[ResolvedInterfaceMethod]>,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<(), ResolvedBuildFailure> {
    if interface.methods.len() != interface.method_binder_authorities.len() {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    constraint_work
        .charge(interface.method_binder_authorities.len())
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    for (method_position, (method, authority)) in interface
        .methods
        .iter()
        .zip(&interface.method_binder_authorities)
        .enumerate()
    {
        if authority.method != method.id
            || !same_summary_resolved_type_variables_with_constraint_budget(
                &authority.parameters,
                method.type_parameters(),
                constraint_work,
            )?
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        if let Some(source_methods) = source_methods {
            let source = source_methods
                .get(method_position)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            if source.id != method.id
                || source.spelling != method.spelling
                || source.span != method.span
                || !same_origin_with_constraint_budget(
                    &source.origin,
                    &method.origin,
                    constraint_work,
                )?
                || !same_type_with_constraint_budget(
                    &source.annotation.ty,
                    method.value_type(),
                    constraint_work,
                )
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            if !same_summary_resolved_type_variables_with_constraint_budget(
                &source.type_parameters,
                &authority.parameters,
                constraint_work,
            )? {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }
    }
    if source_methods.is_some_and(|methods| methods.len() != interface.methods.len()) {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    Ok(())
}

impl ExportSummary {
    pub(crate) fn authenticate(
        &self,
        type_work: &mut TypeWorkBudget,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<(), ResolvedBuildFailure> {
        if self.terms.len() != self.term_order.len()
            || self.nominals.len() != self.nominal_order.len()
            || self.constructors.len() != self.constructor_order.len()
            || self.interface_names.len() != self.interface_name_order.len()
            || self.method_names.len() != self.method_name_order.len()
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        authenticate_identity_order(
            &self.hidden_constructors,
            &self.hidden_constructor_order,
            constraint_work,
        )?;
        authenticate_identity_order(
            &self.hidden_nominals,
            &self.hidden_nominal_order,
            constraint_work,
        )?;

        let expression_count = self
            .term_order
            .len()
            .checked_add(self.method_name_order.len())
            .and_then(|count| count.checked_add(self.constructor_order.len()))
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        let mut expression_spellings = HashSet::new();
        constraint_work
            .charge(expression_count)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        expression_spellings
            .try_reserve(expression_count)
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        if self.term_order.iter().any(|spelling| {
            !self.terms.contains_key(spelling) || !expression_spellings.insert(spelling.as_str())
        }) || self.method_name_order.iter().any(|spelling| {
            !self.method_names.contains_key(spelling)
                || !expression_spellings.insert(spelling.as_str())
        }) || self.constructor_order.iter().any(|spelling| {
            !self.constructors.contains_key(spelling)
                || !expression_spellings.insert(spelling.as_str())
        }) {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        let type_count = self
            .nominal_order
            .len()
            .checked_add(self.interface_name_order.len())
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        let mut type_spellings = HashSet::new();
        constraint_work
            .charge(type_count)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        type_spellings
            .try_reserve(type_count)
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        if self.nominal_order.iter().any(|spelling| {
            !self.nominals.contains_key(spelling) || !type_spellings.insert(spelling.as_str())
        }) || self.interface_name_order.iter().any(|spelling| {
            !self.interface_names.contains_key(spelling)
                || !type_spellings.insert(spelling.as_str())
        }) {
            return Err(ResolvedBuildFailure::InvalidState);
        }

        constraint_work
            .charge(self.withheld.len())
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let withheld_count = self
            .withheld
            .values()
            .try_fold(0usize, |count, withheld| count.checked_add(withheld.len()?))
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        let withheld_storage_work = self
            .withheld_order
            .len()
            .checked_mul(2)
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(withheld_storage_work)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let mut seen_withheld = HashSet::new();
        seen_withheld
            .try_reserve(self.withheld_order.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        let mut withheld_constructor_counts =
            HashMap::<(NominalTypeId, WithheldExportKind), usize>::new();
        withheld_constructor_counts
            .try_reserve(self.withheld_order.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        if withheld_count != self.withheld_order.len() {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        for entry in &self.withheld_order {
            let Some(withheld) = self
                .withheld
                .get(&entry.spelling)
                .and_then(|withheld| withheld.get_ordered(entry))
            else {
                return Err(ResolvedBuildFailure::InvalidState);
            };
            let semantics_are_valid = match entry.namespace {
                WithheldNamespace::Term | WithheldNamespace::Nominal => {
                    entry.owner.is_none()
                        && entry.constructor_index.is_none()
                        && withheld.owner.is_none()
                        && withheld.kind == WithheldExportKind::Private
                }
                WithheldNamespace::Constructor => {
                    entry.owner.is_some()
                        && entry.constructor_index.is_some()
                        && withheld.owner == entry.owner
                }
            };
            if !seen_withheld.insert((
                entry.spelling.as_str(),
                entry.namespace,
                entry.owner,
                entry.constructor_index,
            )) || !semantics_are_valid
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            if entry.namespace == WithheldNamespace::Constructor {
                let owner = entry.owner.ok_or(ResolvedBuildFailure::InvalidState)?;
                let count = withheld_constructor_counts
                    .entry((owner, withheld.kind))
                    .or_default();
                *count = count
                    .checked_add(1)
                    .ok_or(ResolvedBuildFailure::ConstraintResource)?;
            }
        }

        let mut environments = KindEnvironments::new();
        let mut canonical_variables = HashMap::new();
        let mut canonical_nominals = HashMap::<
            NominalTypeId,
            (
                &[ResolvedTypeVariable],
                usize,
                &[ConstructorId],
                ImportedTypeAccess,
                &Origin,
                usize,
            ),
        >::new();
        let nominal_carrier_count = self
            .nominals
            .len()
            .checked_add(self.hidden_nominals.len())
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(nominal_carrier_count)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        canonical_nominals
            .try_reserve(nominal_carrier_count)
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        let family_ordinal_work = self
            .nominals()
            .map(|(_, nominal)| nominal.constructors.len())
            .chain(
                self.hidden_nominals()
                    .map(|nominal| nominal.constructors.len()),
            )
            .try_fold(0usize, |work, family_len| work.checked_add(family_len))
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(family_ordinal_work)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;

        for (_, nominal) in self.nominals() {
            if nominal.parameter_count != nominal.parameters.len()
                || nominal.constructor_count == 0
                || match nominal.access {
                    ExportedTypeAccess::Opaque => !nominal.constructors.is_empty(),
                    ExportedTypeAccess::Transparent => {
                        nominal.constructors.len() != nominal.constructor_count
                    }
                }
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            for (index, constructor) in nominal.constructors.iter().enumerate() {
                if constructor.owner() != nominal.id
                    || usize::try_from(constructor.constructor()) != Ok(index)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
            if let Some((parameters, constructor_count, _, access, origin, _)) =
                canonical_nominals.get(&nominal.id)
            {
                if *access != nominal.access.into()
                    || *constructor_count != nominal.constructor_count
                    || !same_summary_resolved_type_variables_with_constraint_budget(
                        parameters,
                        &nominal.parameters,
                        constraint_work,
                    )?
                    || !same_origin_with_constraint_budget(
                        origin,
                        &nominal.origin,
                        constraint_work,
                    )?
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                continue;
            }
            register_summary_parameters(
                &nominal.parameters,
                SummaryBinderOwner::Nominal(nominal.id),
                &mut canonical_variables,
                &mut environments,
                type_work,
            )?;
            environments
                .insert_nominal(
                    nominal.id,
                    &nominal.parameters,
                    nominal.origin.primary_span(),
                    type_work,
                )
                .map_err(map_summary_kind_failure)?;
            canonical_nominals.insert(
                nominal.id,
                (
                    &nominal.parameters,
                    nominal.constructor_count,
                    &nominal.constructors,
                    nominal.access.into(),
                    &nominal.origin,
                    0,
                ),
            );
        }
        for nominal in self.hidden_nominals() {
            if nominal.parameter_count != nominal.parameters.len()
                || nominal.constructor_count == 0
                || canonical_nominals.contains_key(&nominal.id)
                || match nominal.access {
                    ImportedTypeAccess::Transparent => {
                        nominal.constructors.len() != nominal.constructor_count
                    }
                    ImportedTypeAccess::Opaque | ImportedTypeAccess::Hidden => {
                        !nominal.constructors.is_empty()
                    }
                }
                || (nominal.id.module() == self.module
                    && (nominal.access != ImportedTypeAccess::Hidden
                        || !nominal.constructors.is_empty()
                        || !nominal.display_is_private))
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            for (index, constructor) in nominal.constructors.iter().enumerate() {
                if constructor.owner() != nominal.id
                    || usize::try_from(constructor.constructor()) != Ok(index)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
            register_summary_parameters(
                &nominal.parameters,
                SummaryBinderOwner::Nominal(nominal.id),
                &mut canonical_variables,
                &mut environments,
                type_work,
            )?;
            environments
                .insert_nominal(
                    nominal.id,
                    &nominal.parameters,
                    nominal.origin.primary_span(),
                    type_work,
                )
                .map_err(map_summary_kind_failure)?;
            canonical_nominals.insert(
                nominal.id,
                (
                    &nominal.parameters,
                    nominal.constructor_count,
                    &nominal.constructors,
                    nominal.access,
                    &nominal.origin,
                    0,
                ),
            );
        }

        constraint_work
            .charge(canonical_nominals.len())
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let mut matched_withheld_counts = 0usize;
        for (identity, (_, constructor_count, _, access, _, _)) in &canonical_nominals {
            let retained_count = match access {
                ImportedTypeAccess::Opaque => withheld_constructor_counts
                    .get(&(*identity, WithheldExportKind::OpaqueConstructor))
                    .copied(),
                ImportedTypeAccess::Hidden if identity.module() == self.module => {
                    withheld_constructor_counts
                        .get(&(*identity, WithheldExportKind::Private))
                        .copied()
                }
                ImportedTypeAccess::Transparent | ImportedTypeAccess::Hidden => None,
            };
            if retained_count.is_some() {
                matched_withheld_counts = matched_withheld_counts
                    .checked_add(1)
                    .ok_or(ResolvedBuildFailure::ConstraintResource)?;
            }
            if (matches!(access, ImportedTypeAccess::Opaque)
                || (*access == ImportedTypeAccess::Hidden && identity.module() == self.module))
                && retained_count != Some(*constructor_count)
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }
        if matched_withheld_counts != withheld_constructor_counts.len() {
            return Err(ResolvedBuildFailure::InvalidState);
        }

        if self.interfaces.len() != self.interface_positions.len()
            || self.implementations.len() != self.implementation_positions.len()
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        let interface_fact_count = self
            .interfaces
            .len()
            .checked_add(self.hidden_interfaces.len())
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(interface_fact_count)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let mut interface_facts = HashMap::new();
        interface_facts
            .try_reserve(interface_fact_count)
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        for (position, interface) in self.interfaces.iter().enumerate() {
            if self.interface_positions.get(&interface.id) != Some(&position)
                || interface_facts.insert(interface.id, interface).is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            register_summary_parameters(
                std::slice::from_ref(&interface.parameter),
                SummaryBinderOwner::Interface(interface.id),
                &mut canonical_variables,
                &mut environments,
                type_work,
            )?;
            authenticate_method_binder_authority(interface, None, constraint_work)?;
            for (method, authority) in interface
                .methods
                .iter()
                .zip(&interface.method_binder_authorities)
            {
                register_summary_parameters(
                    &authority.parameters,
                    SummaryBinderOwner::Method(method.id),
                    &mut canonical_variables,
                    &mut environments,
                    type_work,
                )?;
            }
            environments
                .insert_interface(
                    interface.id,
                    &interface.parameter.kind,
                    interface.parameter.origin.primary_span(),
                    type_work,
                )
                .map_err(map_summary_kind_failure)?;
        }
        for interface in &self.hidden_interfaces {
            if interface.id.module() == self.module
                || interface_facts.insert(interface.id, interface).is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            register_summary_parameters(
                std::slice::from_ref(&interface.parameter),
                SummaryBinderOwner::Interface(interface.id),
                &mut canonical_variables,
                &mut environments,
                type_work,
            )?;
            authenticate_method_binder_authority(interface, None, constraint_work)?;
            for (method, authority) in interface
                .methods
                .iter()
                .zip(&interface.method_binder_authorities)
            {
                register_summary_parameters(
                    &authority.parameters,
                    SummaryBinderOwner::Method(method.id),
                    &mut canonical_variables,
                    &mut environments,
                    type_work,
                )?;
            }
            environments
                .insert_interface(
                    interface.id,
                    &interface.parameter.kind,
                    interface.parameter.origin.primary_span(),
                    type_work,
                )
                .map_err(map_summary_kind_failure)?;
        }
        constraint_work
            .charge(self.interface_names.len())
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let mut named_interfaces = HashSet::new();
        named_interfaces
            .try_reserve(self.interface_names.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        for (_, interface) in self.interface_names() {
            if !self.interface_positions.contains_key(&interface) {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            named_interfaces.insert(interface);
        }
        let interface_relation_work = self
            .interfaces
            .len()
            .checked_add(self.method_names.len())
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(interface_relation_work)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if self
            .interfaces
            .iter()
            .any(|interface| !named_interfaces.contains(&interface.id))
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        for (_, method) in self.method_names() {
            if !interface_facts
                .get(&method.interface())
                .is_some_and(|interface| interface.method(method).is_some())
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }

        let mut canonical_globals = HashMap::<BinderId, &ExportedGlobal>::new();
        constraint_work
            .charge(self.terms.len())
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        canonical_globals
            .try_reserve(self.terms.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(self.implementations.len())
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let term_binder_count = self
            .terms
            .len()
            .checked_add(
                self.implementations
                    .iter()
                    .try_fold(0usize, |count, implementation| {
                        count.checked_add(implementation.fact.methods.len())
                    })
                    .ok_or(ResolvedBuildFailure::ConstraintResource)?,
            )
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(term_binder_count)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let mut term_binders = HashSet::new();
        term_binders
            .try_reserve(term_binder_count)
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        for (_, global) in self.terms() {
            if global.binder.module().is_none() {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            if let Some(existing) = canonical_globals.get(&global.binder) {
                if !same_constrained_schemes_with_constraint_budget(
                    &existing.scheme,
                    &global.scheme,
                    constraint_work,
                )? || !same_origin_with_constraint_budget(
                    &existing.origin,
                    &global.origin,
                    constraint_work,
                )? {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                continue;
            }
            canonical_globals.insert(global.binder, global);
            term_binders.insert(global.binder);
            register_summary_scheme_parameters(
                &global.scheme.type_parameters,
                SummaryBinderOwner::Global(global.binder),
                global.origin.primary_span(),
                &mut canonical_variables,
                &mut environments,
                type_work,
            )?;
        }
        for (position, implementation) in self.implementations.iter().enumerate() {
            let fact = &implementation.fact;
            let authorization_is_well_formed = implementation
                .authorization
                .is_well_formed_for(self.module, fact, constraint_work)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
            if self.implementation_positions.get(&fact.id) != Some(&position)
                || !authorization_is_well_formed
                || !interface_facts.contains_key(&fact.interface)
                || matches!(fact.argument(), Type::Variable(_))
                || fact.methods.is_empty()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            if fact.interface.module() != fact.id.module()
                && fact
                    .argument()
                    .outer_nominal()
                    .is_none_or(|nominal| nominal.module() != fact.id.module())
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            for method in &fact.methods {
                if !term_binders.insert(method.binder) {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
            register_summary_parameters(
                &fact.head_parameters,
                SummaryBinderOwner::Implementation(fact.id),
                &mut canonical_variables,
                &mut environments,
                type_work,
            )?;
        }

        for (_, global) in self.terms() {
            if !canonical_globals
                .get(&global.binder)
                .is_some_and(|canonical| std::ptr::eq(*canonical, global))
            {
                continue;
            }
            authenticate_exact_global_scheme_binders(&global.scheme, constraint_work)?;
            let parameter_ids = global
                .scheme
                .type_parameters
                .iter()
                .map(|(identity, _)| *identity);
            authenticate_summary_type_variables(
                global.scheme.value_type(),
                parameter_ids.clone(),
                type_work,
            )?;
            environments
                .expect_body_free_value_type_with_ledger(
                    global.scheme.value_type(),
                    global.origin.primary_span(),
                    type_work,
                )
                .map_err(map_summary_kind_failure)?;
            let mut requirement_index = SummaryRequirementIndex::default();
            for (index, requirement) in global.scheme.requirements.iter().enumerate() {
                if requirement.id.owner()
                    != crate::interface::RequirementOwner::Global(global.binder)
                    || usize::try_from(requirement.id.declaration()) != Ok(index)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                requirement_index.observe(requirement, constraint_work)?;
                authenticate_summary_type_variables(
                    requirement.argument(),
                    parameter_ids.clone(),
                    type_work,
                )?;
                environments
                    .expect_body_free_interface_argument_with_ledger(
                        requirement.interface,
                        requirement.argument(),
                        requirement.span,
                        type_work,
                    )
                    .map_err(map_summary_kind_failure)?;
            }
        }

        for interface in self.interfaces.iter().chain(self.hidden_interfaces.iter()) {
            if interface.methods.is_empty() {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            for (index, method) in interface.methods.iter().enumerate() {
                if method.id.interface() != interface.id
                    || usize::try_from(method.id.declaration()) != Ok(index)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                constraint_work
                    .charge(method.type_parameters().len())
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                let mut method_parameters = Vec::new();
                method_parameters
                    .try_reserve(method.type_parameters().len())
                    .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
                method_parameters.extend(
                    method
                        .type_parameters()
                        .iter()
                        .map(|parameter| parameter.id),
                );
                environments
                    .expect_body_free_interface_method_with_ledger(
                        method.value_type(),
                        interface.parameter.id,
                        &method_parameters,
                        method.span,
                        type_work,
                    )
                    .map_err(map_summary_kind_failure)?;
            }
        }

        let physical_constructor_work = self
            .constructors
            .len()
            .checked_add(self.hidden_constructors.len())
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(physical_constructor_work)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let mut canonical_constructors = HashMap::<ConstructorId, &ExportedConstructor>::new();
        canonical_constructors
            .try_reserve(
                self.constructors
                    .len()
                    .checked_add(self.hidden_constructors.len())
                    .ok_or(ResolvedBuildFailure::ConstraintResource)?,
            )
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        for constructor in self
            .constructors()
            .map(|(_, constructor)| constructor)
            .chain(self.hidden_constructors())
        {
            let Some((parameters, _, family, access, _, _)) =
                canonical_nominals.get(&constructor.id.owner())
            else {
                return Err(ResolvedBuildFailure::InvalidState);
            };
            let constructor_position = usize::try_from(constructor.id.constructor())
                .map_err(|_| ResolvedBuildFailure::InvalidState)?;
            if *access != ImportedTypeAccess::Transparent
                || family.get(constructor_position) != Some(&constructor.id)
                || (self.hidden_constructors.contains_key(&constructor.id)
                    && self.constructor_names_by_id.contains_key(&constructor.id))
                || (self.hidden_constructors.contains_key(&constructor.id)
                    && constructor.id.owner().module() == self.module)
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            if let Some(existing) = canonical_constructors.get(&constructor.id) {
                let payloads_match = match (&existing.payload, &constructor.payload) {
                    (None, None) => true,
                    (Some(left), Some(right)) => {
                        same_type_with_constraint_budget(left, right, constraint_work)
                            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
                    }
                    _ => false,
                };
                if !payloads_match
                    || existing.spelling != constructor.spelling
                    || !same_constrained_schemes_with_constraint_budget(
                        &existing.scheme,
                        &constructor.scheme,
                        constraint_work,
                    )?
                    || !same_origin_with_constraint_budget(
                        &existing.origin,
                        &constructor.origin,
                        constraint_work,
                    )?
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                continue;
            }
            authenticate_constructor_scheme(constructor, parameters, type_work, constraint_work)?;
            environments
                .expect_body_free_constructor_value_type_with_ledger(
                    constructor.scheme.value_type(),
                    constructor.payload.as_ref(),
                    parameters,
                    constructor.origin.primary_span(),
                    type_work,
                )
                .map_err(map_summary_kind_failure)?;
            canonical_constructors.insert(constructor.id, constructor);
            let Some((_, _, _, _, _, physical_count)) =
                canonical_nominals.get_mut(&constructor.id.owner())
            else {
                return Err(ResolvedBuildFailure::InvalidState);
            };
            *physical_count = physical_count
                .checked_add(1)
                .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        }
        constraint_work
            .charge(canonical_nominals.len())
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        for (_, _, family, access, _, physical_count) in canonical_nominals.values() {
            let expected = if *access == ImportedTypeAccess::Transparent {
                family.len()
            } else {
                0
            };
            if *physical_count != expected {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }
        let reverse_index_work = self
            .constructors
            .len()
            .checked_add(self.nominals.len())
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(reverse_index_work)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let mut indexed_constructors = HashSet::new();
        indexed_constructors
            .try_reserve(self.constructors.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        for (_, constructor) in self.constructors() {
            let Some(spelling) = self.constructor_names_by_id.get(&constructor.id) else {
                return Err(ResolvedBuildFailure::InvalidState);
            };
            if !self
                .constructors
                .get(spelling)
                .is_some_and(|indexed| indexed.id == constructor.id)
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            indexed_constructors.insert(constructor.id);
        }
        if indexed_constructors.len() != self.constructor_names_by_id.len() {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        let mut indexed_nominals = HashSet::new();
        indexed_nominals
            .try_reserve(self.nominals.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        for (_, nominal) in self.nominals() {
            let Some(spelling) = self.nominal_names_by_id.get(&nominal.id) else {
                return Err(ResolvedBuildFailure::InvalidState);
            };
            if !self
                .nominals
                .get(spelling)
                .is_some_and(|indexed| indexed.id == nominal.id)
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            indexed_nominals.insert(nominal.id);
        }
        if indexed_nominals.len() != self.nominal_names_by_id.len() {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        for implementation in &self.implementations {
            let fact = &implementation.fact;
            authenticate_exact_implementation_binders(fact, constraint_work)?;
            let parameter_ids = fact.head_parameters.iter().map(|parameter| parameter.id);
            authenticate_summary_type_variables(fact.argument(), parameter_ids.clone(), type_work)?;
            environments
                .expect_body_free_interface_argument_with_ledger(
                    fact.interface,
                    fact.argument(),
                    fact.span,
                    type_work,
                )
                .map_err(map_summary_kind_failure)?;
            let mut prerequisite_index = SummaryRequirementIndex::default();
            for (index, prerequisite) in fact.prerequisites.iter().enumerate() {
                if prerequisite.id.owner() != crate::interface::RequirementOwner::Impl(fact.id)
                    || usize::try_from(prerequisite.id.declaration()) != Ok(index)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                if !implementation_prerequisite_terminates(
                    prerequisite.argument(),
                    fact.argument(),
                    constraint_work,
                )
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                prerequisite_index.observe(prerequisite, constraint_work)?;
                authenticate_summary_type_variables(
                    prerequisite.argument(),
                    parameter_ids.clone(),
                    type_work,
                )?;
                environments
                    .expect_body_free_interface_argument_with_ledger(
                        prerequisite.interface,
                        prerequisite.argument(),
                        prerequisite.span,
                        type_work,
                    )
                    .map_err(map_summary_kind_failure)?;
            }
            let interface = interface_facts
                .get(&fact.interface)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            if fact.methods.len() != interface.methods.len() {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            for (method, interface_method) in fact.methods.iter().zip(interface.methods.iter()) {
                if method.id.implementation() != fact.id
                    || method.id.method() != method.method
                    || method.method != interface_method.id
                    || method.binder.module() != Some(fact.id.module())
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                authenticate_implementation_method_parameter_mirror(
                    method,
                    &fact.head_parameters,
                    interface_method.type_parameters(),
                    constraint_work,
                )?;
                if method.scheme.requirements.len() != fact.prerequisites.len() {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                for (method_requirement, prerequisite) in method
                    .scheme
                    .requirements
                    .iter()
                    .zip(fact.prerequisites.iter())
                {
                    authenticate_method_requirement_mirror(
                        method_requirement,
                        prerequisite,
                        constraint_work,
                    )?;
                }
                let parameter_count = fact
                    .head_parameters
                    .len()
                    .checked_add(interface_method.type_parameters().len())
                    .ok_or(ResolvedBuildFailure::ConstraintResource)?;
                constraint_work
                    .charge(parameter_count)
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                let mut method_parameter_ids = Vec::new();
                method_parameter_ids
                    .try_reserve(parameter_count)
                    .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
                method_parameter_ids
                    .extend(fact.head_parameters.iter().map(|parameter| parameter.id));
                method_parameter_ids.extend(
                    interface_method
                        .type_parameters()
                        .iter()
                        .map(|parameter| parameter.id),
                );
                authenticate_summary_type_variables(
                    method.scheme.value_type(),
                    method_parameter_ids.into_iter(),
                    type_work,
                )?;
                if !same_summary_type_after_single_substitution(
                    interface_method.value_type(),
                    interface.parameter.id,
                    fact.argument(),
                    method.scheme.value_type(),
                    constraint_work,
                )? {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                environments
                    .expect_body_free_value_type_with_ledger(
                        method.scheme.value_type(),
                        method.span,
                        type_work,
                    )
                    .map_err(map_summary_kind_failure)?;
            }
        }
        authenticate_nonoverlapping_summary_implementations(
            self.implementations
                .iter()
                .map(AuthorizedImplementationFact::fact),
            constraint_work,
        )?;
        Ok(())
    }
}

impl ExportSummary {
    fn empty(module: ModuleId) -> Self {
        Self {
            module,
            terms: HashMap::new(),
            term_order: Vec::new(),
            nominals: HashMap::new(),
            nominal_order: Vec::new(),
            nominal_names_by_id: HashMap::new(),
            constructors: HashMap::new(),
            constructor_order: Vec::new(),
            constructor_names_by_id: HashMap::new(),
            hidden_constructors: HashMap::new(),
            hidden_constructor_order: Vec::new(),
            interface_names: HashMap::new(),
            interface_name_order: Vec::new(),
            method_names: HashMap::new(),
            method_name_order: Vec::new(),
            interfaces: Vec::new(),
            interface_positions: HashMap::new(),
            hidden_interfaces: Vec::new(),
            implementations: Vec::new(),
            implementation_positions: HashMap::new(),
            hidden_nominals: HashMap::new(),
            hidden_nominal_order: Vec::new(),
            withheld: HashMap::new(),
            withheld_order: Vec::new(),
        }
    }

    /// Returns the publishing module identity.
    #[must_use]
    pub const fn module(&self) -> ModuleId {
        self.module
    }

    fn take_public_implementation_authorizations(
        &mut self,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<Box<[PublicImplementationAuthorization]>, ()> {
        let mut total_hops = 0usize;
        for implementation in &self.implementations {
            constraint_work.charge(1)?;
            total_hops = total_hops
                .checked_add(implementation.authorization.hops().len())
                .ok_or(())?;
        }
        let retained_work = self
            .implementations
            .len()
            .checked_add(total_hops)
            .ok_or(())?;
        constraint_work.charge(retained_work)?;
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(self.implementations.len())
            .map_err(|_| ())?;
        for implementation in self.implementations.drain(..) {
            retained.push(PublicImplementationAuthorization {
                id: implementation.fact.id,
                authorization: implementation.authorization,
            });
            drop(implementation.fact);
        }
        self.implementation_positions.clear();
        Ok(retained.into_boxed_slice())
    }

    pub(crate) fn freeze(
        resolved: &ResolvedModule,
        checked_globals: &[CheckedGlobalScheme],
        checked_interfaces: &[CheckedInterfaceFact],
        admitted_implementations: &[CheckedImplementation],
        checked_implementations: &[CheckedImplementationFact],
        type_work: &mut TypeWorkBudget,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        type_work
            .charge(checked_globals.len())
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let mut checked_by_binder = HashMap::new();
        checked_by_binder
            .try_reserve(checked_globals.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for scheme in checked_globals {
            if checked_by_binder.insert(scheme.binder, scheme).is_some() {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }
        let mut summary = Self {
            module: resolved.module,
            terms: HashMap::new(),
            term_order: Vec::new(),
            nominals: HashMap::new(),
            nominal_order: Vec::new(),
            nominal_names_by_id: HashMap::new(),
            constructors: HashMap::new(),
            constructor_order: Vec::new(),
            constructor_names_by_id: HashMap::new(),
            hidden_constructors: HashMap::new(),
            hidden_constructor_order: Vec::new(),
            interface_names: HashMap::new(),
            interface_name_order: Vec::new(),
            method_names: HashMap::new(),
            method_name_order: Vec::new(),
            interfaces: Vec::new(),
            interface_positions: HashMap::new(),
            hidden_interfaces: Vec::new(),
            implementations: Vec::new(),
            implementation_positions: HashMap::new(),
            hidden_nominals: HashMap::new(),
            hidden_nominal_order: Vec::new(),
            withheld: HashMap::new(),
            withheld_order: Vec::new(),
        };
        let public_order_count = resolved
            .export_candidate
            .terms
            .len()
            .checked_add(resolved.export_candidate.nominals.len())
            .and_then(|count| count.checked_add(resolved.export_candidate.constructors.len()))
            .and_then(|count| count.checked_add(resolved.export_candidate.interfaces.len()))
            .and_then(|count| count.checked_add(resolved.export_candidate.methods.len()))
            .ok_or(ResolvedBuildFailure::TypeResource)?;
        type_work
            .charge(public_order_count)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        summary
            .term_order
            .try_reserve_exact(resolved.export_candidate.terms.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        summary
            .nominal_order
            .try_reserve_exact(resolved.export_candidate.nominals.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        summary
            .constructor_order
            .try_reserve_exact(resolved.export_candidate.constructors.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        summary
            .interface_name_order
            .try_reserve_exact(resolved.export_candidate.interfaces.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        summary
            .method_name_order
            .try_reserve_exact(resolved.export_candidate.methods.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        type_work
            .charge(resolved.export_candidate.withheld_order.len())
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let withheld_order_work = resolved
            .export_candidate
            .withheld_order
            .len()
            .checked_mul(2)
            .and_then(|work| {
                work.checked_add(
                    resolved
                        .export_candidate
                        .withheld_order
                        .iter()
                        .filter(|entry| entry.namespace == WithheldNamespace::Constructor)
                        .count(),
                )
            })
            .ok_or(ResolvedBuildFailure::TypeResource)?;
        type_work
            .charge(withheld_order_work)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        summary
            .withheld
            .try_reserve(resolved.export_candidate.withheld.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        summary
            .withheld_order
            .try_reserve(resolved.export_candidate.withheld_order.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for entry in &resolved.export_candidate.withheld_order {
            let withheld = resolved
                .export_candidate
                .withheld
                .get(&entry.spelling)
                .and_then(|withheld| withheld.get_ordered(entry))
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let entries = summary.withheld.entry(entry.spelling.clone()).or_default();
            entries
                .try_reserve(entry.namespace, 1)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            if entries.get_exact(entry.namespace, entry.owner).is_some() {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            let constructor_index = entries.insert_new(entry.namespace, withheld.clone());
            if constructor_index != entry.constructor_index {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.withheld_order.push(entry.clone());
        }
        summary
            .terms
            .try_reserve(resolved.export_candidate.terms.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for spelling in &resolved.export_candidate.term_order {
            let candidate = resolved
                .export_candidate
                .terms
                .get(spelling)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let (binder, scheme, origin) = match candidate.source {
                CandidateFactSource::Local => {
                    let checked = checked_by_binder
                        .get(&candidate.binder)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    if candidate.binder.module() != Some(resolved.module) {
                        return Err(ResolvedBuildFailure::InvalidState);
                    }
                    (checked.binder, &checked.scheme, &checked.origin)
                }
                CandidateFactSource::Imported => {
                    let imported = resolved
                        .imported
                        .global(candidate.binder)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    if candidate.binder.module() == Some(resolved.module) {
                        return Err(ResolvedBuildFailure::InvalidState);
                    }
                    (imported.binder, &imported.scheme, &imported.origin)
                }
            };
            if binder != candidate.binder
                || summary
                    .terms
                    .insert(
                        spelling.clone(),
                        ExportedGlobal {
                            binder,
                            scheme: scheme
                                .clone_with_budget(type_work)
                                .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                            origin: origin.clone(),
                        },
                    )
                    .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.term_order.push(spelling.clone());
        }

        let checked_fact_count = checked_interfaces
            .len()
            .checked_add(checked_implementations.len())
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(checked_fact_count)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if checked_interfaces.len() != resolved.interfaces.len()
            || admitted_implementations.len() != checked_implementations.len()
            || checked_implementations.len() != resolved.implementations.len()
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        let mut checked_interfaces_by_id = HashMap::new();
        checked_interfaces_by_id
            .try_reserve(checked_interfaces.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        for (interface, checked) in resolved.interfaces.iter().zip(checked_interfaces) {
            if interface.id != checked.id
                || interface.spelling != checked.spelling
                || interface.methods.len() != checked.methods.len()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            for (method, checked_method) in interface.methods.iter().zip(&checked.methods) {
                if method.id != checked_method.id || method.spelling != checked_method.spelling {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
            authenticate_method_binder_authority(
                checked,
                Some(&interface.methods),
                constraint_work,
            )?;
            if checked_interfaces_by_id
                .insert(checked.id, checked)
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }

        summary
            .interfaces
            .try_reserve(resolved.export_candidate.interfaces.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        summary
            .interface_positions
            .try_reserve(resolved.export_candidate.interfaces.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        summary
            .interface_names
            .try_reserve(resolved.export_candidate.interfaces.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        summary
            .method_names
            .try_reserve(resolved.export_candidate.methods.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;

        for spelling in &resolved.export_candidate.interface_order {
            let candidate = resolved
                .export_candidate
                .interfaces
                .get(spelling)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let checked = match candidate.source {
                CandidateFactSource::Local => checked_interfaces_by_id.get(&candidate.id).copied(),
                CandidateFactSource::Imported => resolved.imported.interface(candidate.id),
            }
            .ok_or(ResolvedBuildFailure::InvalidState)?;
            let owner_is_publisher = candidate.id.module() == resolved.module;
            if checked.id != candidate.id
                || owner_is_publisher != (candidate.source == CandidateFactSource::Local)
                || summary
                    .interface_names
                    .insert(spelling.clone(), candidate.id)
                    .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.interface_name_order.push(spelling.clone());
            if summary.interface_positions.contains_key(&candidate.id) {
                continue;
            }
            let position = summary.interfaces.len();
            summary.interfaces.push(clone_checked_interface_fact(
                checked,
                type_work,
                constraint_work,
            )?);
            if summary
                .interface_positions
                .insert(candidate.id, position)
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }

        for spelling in &resolved.export_candidate.method_order {
            let candidate = resolved
                .export_candidate
                .methods
                .get(spelling)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let interface = match candidate.source {
                CandidateFactSource::Local => checked_interfaces_by_id
                    .get(&candidate.id.interface())
                    .copied(),
                CandidateFactSource::Imported => {
                    resolved.imported.interface(candidate.id.interface())
                }
            }
            .ok_or(ResolvedBuildFailure::InvalidState)?;
            let owner_is_publisher = candidate.id.interface().module() == resolved.module;
            if owner_is_publisher != (candidate.source == CandidateFactSource::Local)
                || interface.method(candidate.id).is_none()
                || summary
                    .method_names
                    .insert(spelling.clone(), candidate.id)
                    .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.method_name_order.push(spelling.clone());
        }

        let selected_public_implementations = resolved.imported.public_implementation_ids().len();
        constraint_work
            .charge(resolved.implementations.len())
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let selected_local_implementations = resolved
            .implementations
            .iter()
            .filter(|implementation| implementation.public)
            .count();
        let implementation_capacity = selected_local_implementations
            .checked_add(selected_public_implementations)
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        reserve_summary_implementation_storage(
            &mut summary.implementations,
            &mut summary.implementation_positions,
            implementation_capacity,
            constraint_work,
        )?;
        for (admitted, checked) in admitted_implementations.iter().zip(checked_implementations) {
            let implementation = resolved
                .implementations
                .get(admitted.source_index)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            if implementation.id != admitted.id
                || implementation.interface.id != admitted.interface
                || checked.id != admitted.id
                || checked.interface != admitted.interface
                || checked.methods.len() != admitted.methods.len()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            if !implementation.public {
                continue;
            }
            let fact = clone_checked_implementation_fact(checked, type_work, constraint_work)?;
            let authorization = ImplementationAuthorization::local();
            if !authorization
                .is_well_formed_for(resolved.module, &fact, constraint_work)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            let position = summary.implementations.len();
            if summary
                .implementation_positions
                .insert(implementation.id, position)
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.implementations.push(AuthorizedImplementationFact {
                fact,
                authorization,
            });
        }
        for implementation in resolved.imported.public_implementation_ids() {
            let imported = resolved
                .imported
                .implementation_import(*implementation)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let public_authorization = imported
                .public_authorization()
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            constraint_work
                .charge(1)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
            if !public_authorization
                .is_well_formed_for(resolved.module, &imported.fact, constraint_work)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            let fact =
                clone_checked_implementation_fact(&imported.fact, type_work, constraint_work)?;
            let authorization = public_authorization
                .clone_with_budget(constraint_work)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
            let position = summary.implementations.len();
            if summary
                .implementation_positions
                .insert(fact.id, position)
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.implementations.push(AuthorizedImplementationFact {
                fact,
                authorization,
            });
        }

        let retained_fact_count = summary
            .terms
            .len()
            .checked_add(summary.implementations.len())
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        constraint_work
            .charge(retained_fact_count)
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let interface_reference_count = summary
            .terms
            .values()
            .try_fold(0usize, |count, exported| {
                count.checked_add(exported.scheme.requirements.len())
            })
            .and_then(|count| {
                summary
                    .implementations
                    .iter()
                    .try_fold(count, |count, implementation| {
                        implementation
                            .fact
                            .prerequisites
                            .len()
                            .checked_add(1)
                            .and_then(|fact_count| count.checked_add(fact_count))
                    })
            })
            .and_then(|count| count.checked_add(resolved.export_candidate.methods.len()))
            .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        if interface_reference_count > 0 {
            let interface_reference_work = summary
                .terms
                .len()
                .checked_mul(2)
                .and_then(|term_work| interface_reference_count.checked_add(term_work))
                .ok_or(ResolvedBuildFailure::ConstraintResource)?;
            constraint_work
                .charge(interface_reference_work)
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
            let mut referenced_interfaces = HashSet::new();
            let mut referenced_interface_order = Vec::new();
            for spelling in &resolved.export_candidate.term_order {
                let exported = summary
                    .terms
                    .get(spelling)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                for requirement in &exported.scheme.requirements {
                    retain_hidden_interface_reference(
                        requirement.interface,
                        &summary.interface_positions,
                        &mut referenced_interfaces,
                        &mut referenced_interface_order,
                        constraint_work,
                    )?;
                }
            }
            for spelling in &resolved.export_candidate.method_order {
                let method = summary
                    .method_names
                    .get(spelling)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                retain_hidden_interface_reference(
                    method.interface(),
                    &summary.interface_positions,
                    &mut referenced_interfaces,
                    &mut referenced_interface_order,
                    constraint_work,
                )?;
            }
            for implementation in &summary.implementations {
                retain_hidden_interface_reference(
                    implementation.fact.interface,
                    &summary.interface_positions,
                    &mut referenced_interfaces,
                    &mut referenced_interface_order,
                    constraint_work,
                )?;
                for prerequisite in &implementation.fact.prerequisites {
                    retain_hidden_interface_reference(
                        prerequisite.interface,
                        &summary.interface_positions,
                        &mut referenced_interfaces,
                        &mut referenced_interface_order,
                        constraint_work,
                    )?;
                }
            }
            constraint_work
                .charge(referenced_interface_order.len())
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
            summary
                .hidden_interfaces
                .try_reserve(referenced_interface_order.len())
                .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
            for interface in referenced_interface_order {
                let fact = resolved
                    .imported
                    .interface(interface)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                if fact.id.module() == resolved.module {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                summary.hidden_interfaces.push(clone_checked_interface_fact(
                    fact,
                    type_work,
                    constraint_work,
                )?);
            }
        }

        summary
            .nominals
            .try_reserve(resolved.export_candidate.nominals.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        summary
            .nominal_names_by_id
            .try_reserve(resolved.export_candidate.nominals.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for spelling in &resolved.export_candidate.nominal_order {
            let candidate = resolved
                .export_candidate
                .nominals
                .get(spelling)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let (parameters, constructor_count, constructors, origin) = match candidate.source {
                CandidateFactSource::Local => {
                    let nominal = resolved
                        .registry
                        .nominal(candidate.id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    let parameters = resolved
                        .registry
                        .nominal_parameters(candidate.id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    if candidate.id.module() != resolved.module {
                        return Err(ResolvedBuildFailure::InvalidState);
                    }
                    (
                        parameters,
                        nominal.constructors.len(),
                        if candidate.access == ExportedTypeAccess::Transparent {
                            nominal.constructors.as_ref()
                        } else {
                            &[]
                        },
                        &nominal.origin,
                    )
                }
                CandidateFactSource::Imported => {
                    let imported = resolved
                        .imported
                        .nominal(candidate.id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    let expected_access = match imported.access {
                        ImportedTypeAccess::Opaque => ExportedTypeAccess::Opaque,
                        ImportedTypeAccess::Transparent => ExportedTypeAccess::Transparent,
                        ImportedTypeAccess::Hidden => {
                            return Err(ResolvedBuildFailure::InvalidState);
                        }
                    };
                    if candidate.id.module() == resolved.module
                        || candidate.access != expected_access
                    {
                        return Err(ResolvedBuildFailure::InvalidState);
                    }
                    (
                        imported.parameters.as_ref(),
                        imported.constructor_count,
                        imported.constructors.as_ref(),
                        &imported.origin,
                    )
                }
            };
            type_work
                .charge(constructors.len())
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            let mut cloned_constructors = Vec::new();
            cloned_constructors
                .try_reserve(constructors.len())
                .map_err(|_| ResolvedBuildFailure::TypeResource)?;
            cloned_constructors.extend_from_slice(constructors);
            let cloned_parameters =
                clone_resolved_type_variable_buffer_with_budget(parameters, type_work)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            summary
                .nominal_names_by_id
                .entry(candidate.id)
                .or_insert_with(|| spelling.clone());
            if summary
                .nominals
                .insert(
                    spelling.clone(),
                    ExportedType {
                        id: candidate.id,
                        parameter_count: parameters.len(),
                        constructor_count,
                        parameters: cloned_parameters.into_boxed_slice(),
                        constructors: cloned_constructors.into_boxed_slice(),
                        access: candidate.access,
                        origin: origin.clone(),
                    },
                )
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.nominal_order.push(spelling.clone());
        }

        summary
            .constructors
            .try_reserve(resolved.export_candidate.constructors.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        summary
            .constructor_names_by_id
            .try_reserve(resolved.export_candidate.constructors.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for spelling in &resolved.export_candidate.constructor_order {
            let candidate = resolved
                .export_candidate
                .constructors
                .get(spelling)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let (defining_spelling, payload, scheme, origin) = match candidate.source {
                CandidateFactSource::Local => {
                    let constructor = resolved
                        .registry
                        .constructor(candidate.id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    let parameters = resolved
                        .registry
                        .nominal_parameters(candidate.id.owner())
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    if candidate.id.owner().module() != resolved.module {
                        return Err(ResolvedBuildFailure::InvalidState);
                    }
                    (
                        constructor.spelling.as_str(),
                        constructor.payload.as_ref(),
                        canonical_constructor_scheme(
                            candidate.id.owner(),
                            parameters,
                            constructor.payload.as_ref(),
                            type_work,
                        )
                        .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                        &constructor.origin,
                    )
                }
                CandidateFactSource::Imported => {
                    let constructor = resolved
                        .imported
                        .constructor(candidate.id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    if candidate.id.owner().module() == resolved.module {
                        return Err(ResolvedBuildFailure::InvalidState);
                    }
                    (
                        constructor.spelling.as_str(),
                        constructor.payload.as_ref(),
                        constructor
                            .scheme
                            .clone_with_budget(type_work)
                            .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                        &constructor.origin,
                    )
                }
            };
            summary
                .constructor_names_by_id
                .entry(candidate.id)
                .or_insert_with(|| spelling.clone());
            if summary
                .constructors
                .insert(
                    spelling.clone(),
                    ExportedConstructor {
                        id: candidate.id,
                        spelling: defining_spelling.to_owned(),
                        payload: payload
                            .map(|payload| clone_type_with_budget(payload, type_work))
                            .transpose()
                            .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                        scheme,
                        origin: origin.clone(),
                    },
                )
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.constructor_order.push(spelling.clone());
        }

        let mut constructor_owners = HashSet::new();
        let mut constructor_owner_order = Vec::new();
        for spelling in &resolved.export_candidate.nominal_order {
            let exported = summary
                .nominals
                .get(spelling)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            if exported.access == ExportedTypeAccess::Transparent
                && !constructor_owners.contains(&exported.id)
            {
                type_work
                    .charge(2)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
                constructor_owners
                    .try_reserve(1)
                    .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                constructor_owner_order
                    .try_reserve(1)
                    .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                constructor_owners.insert(exported.id);
                constructor_owner_order.push(exported.id);
            }
        }
        for spelling in &resolved.export_candidate.constructor_order {
            let exported = summary
                .constructors
                .get(spelling)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let owner = exported.id.owner();
            if !constructor_owners.contains(&owner) {
                type_work
                    .charge(2)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
                constructor_owners
                    .try_reserve(1)
                    .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                constructor_owner_order
                    .try_reserve(1)
                    .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                constructor_owners.insert(owner);
                constructor_owner_order.push(owner);
            }
        }

        type_work
            .charge(constructor_owner_order.len())
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let mut constructor_family_capacity = 0usize;
        for owner in &constructor_owner_order {
            let family_len = if owner.module() == resolved.module {
                resolved
                    .registry
                    .nominal(*owner)
                    .map(|nominal| nominal.constructors.len())
            } else {
                resolved
                    .imported
                    .nominal(*owner)
                    .filter(|nominal| nominal.access == ImportedTypeAccess::Transparent)
                    .map(|nominal| nominal.constructors.len())
            }
            .ok_or(ResolvedBuildFailure::InvalidState)?;
            constructor_family_capacity = constructor_family_capacity
                .checked_add(family_len)
                .ok_or(ResolvedBuildFailure::TypeResource)?;
        }
        let constructor_family_work = constructor_family_capacity
            .checked_mul(3)
            .ok_or(ResolvedBuildFailure::TypeResource)?;
        type_work
            .charge(constructor_family_work)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let mut constructor_family_ids = HashSet::new();
        constructor_family_ids
            .try_reserve(constructor_family_capacity)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        let mut constructor_family_order = Vec::new();
        constructor_family_order
            .try_reserve(constructor_family_capacity)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for owner in constructor_owner_order {
            let family = if owner.module() == resolved.module {
                resolved
                    .registry
                    .nominal(owner)
                    .map(|nominal| nominal.constructors.as_ref())
            } else {
                resolved
                    .imported
                    .nominal(owner)
                    .filter(|nominal| nominal.access == ImportedTypeAccess::Transparent)
                    .map(|nominal| nominal.constructors.as_ref())
            }
            .ok_or(ResolvedBuildFailure::InvalidState)?;
            for constructor in family {
                if constructor_family_ids.insert(*constructor) {
                    constructor_family_order.push(*constructor);
                }
            }
        }
        for spelling in &resolved.export_candidate.constructor_order {
            let exported = summary
                .constructors
                .get(spelling)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            if !constructor_family_ids.contains(&exported.id) {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }
        type_work
            .charge(constructor_family_order.len())
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let hidden_constructor_count = constructor_family_order
            .iter()
            .filter(|identity| !summary.constructor_names_by_id.contains_key(identity))
            .count();
        type_work
            .charge(hidden_constructor_count)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        summary
            .hidden_constructors
            .try_reserve(hidden_constructor_count)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        summary
            .hidden_constructor_order
            .try_reserve_exact(hidden_constructor_count)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for constructor_id in constructor_family_order {
            if summary
                .constructor_names_by_id
                .contains_key(&constructor_id)
            {
                continue;
            }
            type_work
                .charge(1)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            let (spelling, payload, scheme, origin) =
                if constructor_id.owner().module() == resolved.module {
                    let constructor = resolved
                        .registry
                        .constructor(constructor_id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    let parameters = resolved
                        .registry
                        .nominal_parameters(constructor_id.owner())
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    (
                        constructor.spelling.as_str(),
                        constructor.payload.as_ref(),
                        canonical_constructor_scheme(
                            constructor_id.owner(),
                            parameters,
                            constructor.payload.as_ref(),
                            type_work,
                        )
                        .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                        &constructor.origin,
                    )
                } else {
                    let constructor = resolved
                        .imported
                        .constructor(constructor_id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    (
                        constructor.spelling.as_str(),
                        constructor.payload.as_ref(),
                        constructor
                            .scheme
                            .clone_with_budget(type_work)
                            .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                        &constructor.origin,
                    )
                };
            if summary
                .hidden_constructors
                .insert(
                    constructor_id,
                    ExportedConstructor {
                        id: constructor_id,
                        spelling: spelling.to_owned(),
                        payload: payload
                            .map(|payload| clone_type_with_budget(payload, type_work))
                            .transpose()
                            .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                        scheme,
                        origin: origin.clone(),
                    },
                )
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.hidden_constructor_order.push(constructor_id);
        }

        let mut referenced_nominals = HashSet::new();
        for exported in summary.terms.values() {
            collect_scheme_nominal_identities(
                &exported.scheme,
                &mut referenced_nominals,
                type_work,
            )
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        }
        for exported in summary.constructors.values() {
            retain_nominal_identity(exported.id.owner(), &mut referenced_nominals, type_work)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            if let Some(payload) = &exported.payload {
                collect_nominal_identities(payload, &mut referenced_nominals, type_work)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            }
        }
        for exported in summary.hidden_constructors.values() {
            retain_nominal_identity(exported.id.owner(), &mut referenced_nominals, type_work)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            if let Some(payload) = &exported.payload {
                collect_nominal_identities(payload, &mut referenced_nominals, type_work)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            }
        }
        for interface in &summary.interfaces {
            for method in &interface.methods {
                collect_nominal_identities(&method.value_type, &mut referenced_nominals, type_work)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            }
        }
        for interface in &summary.hidden_interfaces {
            for method in &interface.methods {
                collect_nominal_identities(&method.value_type, &mut referenced_nominals, type_work)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            }
        }
        for implementation in &summary.implementations {
            collect_nominal_identities(
                &implementation.fact.argument,
                &mut referenced_nominals,
                type_work,
            )
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            for prerequisite in &implementation.fact.prerequisites {
                collect_nominal_identities(
                    &prerequisite.argument,
                    &mut referenced_nominals,
                    type_work,
                )
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            }
            for method in &implementation.fact.methods {
                collect_scheme_nominal_identities(
                    &method.scheme,
                    &mut referenced_nominals,
                    type_work,
                )
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            }
        }

        type_work
            .charge(resolved.export_candidate.hidden_nominals.len())
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        for identity in &resolved.export_candidate.hidden_nominal_order {
            let candidate = resolved
                .export_candidate
                .hidden_nominals
                .get(identity)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            if !referenced_nominals.contains(&candidate.id) {
                continue;
            }
            let source_parameters = resolved
                .registry
                .nominal_parameters(candidate.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let constructor_count = resolved
                .registry
                .nominal(candidate.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?
                .constructors
                .len();
            type_work
                .charge(2)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            summary
                .hidden_nominals
                .try_reserve(1)
                .map_err(|_| ResolvedBuildFailure::TypeResource)?;
            summary
                .hidden_nominal_order
                .try_reserve(1)
                .map_err(|_| ResolvedBuildFailure::TypeResource)?;
            let parameters =
                clone_resolved_type_variable_buffer_with_budget(source_parameters, type_work)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            if summary
                .hidden_nominals
                .insert(
                    candidate.id,
                    ExportedHiddenType {
                        id: candidate.id,
                        parameter_count: candidate.parameter_count,
                        constructor_count,
                        parameters: parameters.into_boxed_slice(),
                        constructors: Box::new([]),
                        access: ImportedTypeAccess::Hidden,
                        spelling: candidate.spelling.clone(),
                        display_is_private: true,
                        origin: candidate.origin.clone(),
                    },
                )
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.hidden_nominal_order.push(candidate.id);
        }
        type_work
            .charge(resolved.imported.nominals.len())
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        for imported in resolved.imported.nominals() {
            if !referenced_nominals.contains(&imported.id)
                || summary.nominal_names_by_id.contains_key(&imported.id)
                || summary.hidden_nominals.contains_key(&imported.id)
            {
                continue;
            }
            let retains_constructor_family = constructor_owners.contains(&imported.id);
            let source_constructors = if retains_constructor_family {
                imported.constructors.as_ref()
            } else {
                &[]
            };
            type_work
                .charge(
                    source_constructors
                        .len()
                        .checked_add(2)
                        .ok_or(ResolvedBuildFailure::TypeResource)?,
                )
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            summary
                .hidden_nominals
                .try_reserve(1)
                .map_err(|_| ResolvedBuildFailure::TypeResource)?;
            summary
                .hidden_nominal_order
                .try_reserve(1)
                .map_err(|_| ResolvedBuildFailure::TypeResource)?;
            let mut constructors = Vec::new();
            constructors
                .try_reserve(source_constructors.len())
                .map_err(|_| ResolvedBuildFailure::TypeResource)?;
            constructors.extend_from_slice(source_constructors);
            let parameters =
                clone_resolved_type_variable_buffer_with_budget(&imported.parameters, type_work)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            if summary
                .hidden_nominals
                .insert(
                    imported.id,
                    ExportedHiddenType {
                        id: imported.id,
                        parameter_count: imported.parameter_count,
                        constructor_count: imported.constructor_count,
                        parameters: parameters.into_boxed_slice(),
                        constructors: constructors.into_boxed_slice(),
                        access: if retains_constructor_family {
                            imported.access
                        } else {
                            ImportedTypeAccess::Hidden
                        },
                        spelling: imported
                            .display_spelling
                            .clone()
                            .unwrap_or_else(|| "hidden".to_owned()),
                        display_is_private: imported.display_is_private,
                        origin: imported.origin.clone(),
                    },
                )
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.hidden_nominal_order.push(imported.id);
        }

        Ok(summary)
    }

    pub(crate) fn term(&self, spelling: &str) -> Option<&ExportedGlobal> {
        self.terms.get(spelling)
    }

    pub(crate) fn nominal(&self, spelling: &str) -> Option<&ExportedType> {
        self.nominals.get(spelling)
    }

    pub(crate) fn constructor(&self, spelling: &str) -> Option<&ExportedConstructor> {
        self.constructors.get(spelling)
    }

    pub(crate) fn interface(&self, spelling: &str) -> Option<&CheckedInterfaceFact> {
        let id = self.interface_names.get(spelling)?;
        self.interfaces.get(*self.interface_positions.get(id)?)
    }

    pub(crate) fn method(&self, spelling: &str) -> Option<MethodId> {
        self.method_names.get(spelling).copied()
    }

    pub(crate) fn interfaces(&self) -> impl Iterator<Item = &CheckedInterfaceFact> {
        self.interfaces.iter()
    }

    pub(crate) fn hidden_interfaces(&self) -> impl Iterator<Item = &CheckedInterfaceFact> {
        self.hidden_interfaces.iter()
    }

    pub(crate) fn implementations(&self) -> impl Iterator<Item = &AuthorizedImplementationFact> {
        self.implementations.iter()
    }

    /// Looks up one public implementation and its authorization by semantic identity.
    #[must_use]
    pub fn implementation(&self, id: ImplId) -> Option<&AuthorizedImplementationFact> {
        self.implementations
            .get(*self.implementation_positions.get(&id)?)
    }

    pub(crate) fn interface_names(&self) -> impl Iterator<Item = (&str, InterfaceId)> {
        self.interface_name_order.iter().filter_map(|spelling| {
            self.interface_names
                .get(spelling)
                .map(|id| (spelling.as_str(), *id))
        })
    }

    pub(crate) fn method_names(&self) -> impl Iterator<Item = (&str, MethodId)> {
        self.method_name_order.iter().filter_map(|spelling| {
            self.method_names
                .get(spelling)
                .map(|id| (spelling.as_str(), *id))
        })
    }

    pub(crate) fn terms(&self) -> impl Iterator<Item = (&str, &ExportedGlobal)> {
        self.term_order.iter().filter_map(|spelling| {
            self.terms
                .get(spelling)
                .map(|exported| (spelling.as_str(), exported))
        })
    }

    pub(crate) fn namespace_entry_count(&self) -> Option<usize> {
        self.terms
            .len()
            .checked_add(self.nominals.len())
            .and_then(|count| count.checked_add(self.constructors.len()))
            .and_then(|count| count.checked_add(self.interface_names.len()))
            .and_then(|count| count.checked_add(self.method_names.len()))
            .and_then(|count| count.checked_add(self.withheld_order.len()))
    }

    pub(crate) fn namespace_capacities(&self) -> Option<(usize, usize, usize, usize, usize)> {
        Some((
            self.terms.len().checked_add(self.method_names.len())?,
            self.nominals.len(),
            self.interface_names.len(),
            self.constructors.len(),
            self.withheld_order.len(),
        ))
    }

    pub(crate) fn withheld_count(&self) -> usize {
        self.withheld_order.len()
    }

    pub(crate) fn nominals(&self) -> impl Iterator<Item = (&str, &ExportedType)> {
        self.nominal_order.iter().filter_map(|spelling| {
            self.nominals
                .get(spelling)
                .map(|exported| (spelling.as_str(), exported))
        })
    }

    pub(crate) fn constructors(&self) -> impl Iterator<Item = (&str, &ExportedConstructor)> {
        self.constructor_order.iter().filter_map(|spelling| {
            self.constructors
                .get(spelling)
                .map(|exported| (spelling.as_str(), exported))
        })
    }

    pub(crate) fn hidden_constructors(&self) -> impl Iterator<Item = &ExportedConstructor> {
        self.hidden_constructor_order
            .iter()
            .filter_map(|identity| self.hidden_constructors.get(identity))
    }

    pub(crate) fn hidden_nominals(&self) -> impl Iterator<Item = &ExportedHiddenType> {
        self.hidden_nominal_order
            .iter()
            .filter_map(|identity| self.hidden_nominals.get(identity))
    }

    #[cfg(test)]
    pub(crate) fn term_authentication_order_for_test(&self) -> Vec<&str> {
        self.term_order.iter().map(String::as_str).collect()
    }

    #[cfg(test)]
    pub(crate) fn nominal_authentication_order_for_test(&self) -> Vec<&str> {
        self.nominal_order.iter().map(String::as_str).collect()
    }

    #[cfg(test)]
    pub(crate) fn constructor_authentication_order_for_test(&self) -> Vec<&str> {
        self.constructor_order.iter().map(String::as_str).collect()
    }

    pub(crate) fn withheld_export(
        &self,
        namespace: WithheldNamespace,
        spelling: &str,
    ) -> Option<&WithheldExport> {
        self.withheld
            .get(spelling)
            .and_then(|withheld| withheld.get(namespace))
    }

    pub(crate) fn withheld(
        &self,
    ) -> impl Iterator<Item = (WithheldNamespace, &str, &WithheldExport)> {
        self.withheld_order.iter().filter_map(|entry| {
            self.withheld
                .get(&entry.spelling)
                .and_then(|withheld| withheld.get_ordered(entry))
                .map(|withheld| (entry.namespace, entry.spelling.as_str(), withheld))
        })
    }

    pub(crate) fn opaque_constructors(
        &self,
        owner: NominalTypeId,
    ) -> impl Iterator<Item = (&str, &WithheldExport)> {
        self.withheld_order.iter().filter_map(move |entry| {
            if entry.namespace != WithheldNamespace::Constructor || entry.owner != Some(owner) {
                return None;
            }
            let withheld = self
                .withheld
                .get(&entry.spelling)
                .and_then(|withheld| withheld.get_ordered(entry))?;
            (withheld.kind == WithheldExportKind::OpaqueConstructor
                && withheld.owner == Some(owner))
            .then_some((entry.spelling.as_str(), withheld))
        })
    }

    pub(crate) fn nominal_fact(&self, id: NominalTypeId) -> Option<ImportedNominalFactRef<'_>> {
        if let Some(spelling) = self.nominal_names_by_id.get(&id) {
            let exported = self
                .nominals
                .get(spelling)
                .expect("the checked nominal identity index must name an export");
            return Some(ImportedNominalFactRef {
                id,
                parameter_count: exported.parameter_count,
                constructor_count: exported.constructor_count,
                parameters: &exported.parameters,
                constructors: &exported.constructors,
                access: exported.access.into(),
                display_spelling: Some(spelling),
                display_is_private: false,
                origin: &exported.origin,
            });
        }
        self.hidden_nominals
            .get(&id)
            .map(|exported| ImportedNominalFactRef {
                id,
                parameter_count: exported.parameter_count,
                constructor_count: exported.constructor_count,
                parameters: &exported.parameters,
                constructors: &exported.constructors,
                access: exported.access,
                display_spelling: Some(&exported.spelling),
                display_is_private: exported.display_is_private,
                origin: &exported.origin,
            })
    }

    pub(crate) fn constructor_by_id(&self, id: ConstructorId) -> Option<&ExportedConstructor> {
        if let Some(spelling) = self.constructor_names_by_id.get(&id) {
            return self.constructors.get(spelling);
        }
        self.hidden_constructors.get(&id)
    }

    #[cfg(test)]
    pub(crate) fn test_fixture(
        module: ModuleId,
        terms: Vec<(&str, BinderId, Type, Origin)>,
        nominals: Vec<(&str, NominalTypeId, ExportedTypeAccess, Origin)>,
        constructors: Vec<(&str, ConstructorId, Option<Type>, Origin)>,
        unavailable: Vec<&str>,
    ) -> Self {
        let term_order = terms
            .iter()
            .map(|(spelling, _, _, _)| (*spelling).to_owned())
            .collect();
        let nominal_order = nominals
            .iter()
            .map(|(spelling, _, _, _)| (*spelling).to_owned())
            .collect();
        let constructor_order = constructors
            .iter()
            .map(|(spelling, _, _, _)| (*spelling).to_owned())
            .collect();
        let nominal_names_by_id = nominals
            .iter()
            .map(|(spelling, id, _, _)| (*id, (*spelling).to_owned()))
            .collect();
        let constructor_names_by_id = constructors
            .iter()
            .map(|(spelling, id, _, _)| (*id, (*spelling).to_owned()))
            .collect();
        let mut constructor_families = HashMap::<NominalTypeId, Vec<ConstructorId>>::new();
        for (_, constructor, _, _) in &constructors {
            constructor_families
                .entry(constructor.owner())
                .or_default()
                .push(*constructor);
        }
        for family in constructor_families.values_mut() {
            family.sort_unstable_by_key(|constructor| constructor.constructor());
        }
        let withheld_order = unavailable
            .iter()
            .flat_map(|spelling| {
                [WithheldNamespace::Term, WithheldNamespace::Nominal]
                    .into_iter()
                    .map(move |namespace| WithheldOrderEntry {
                        spelling: (*spelling).to_owned(),
                        namespace,
                        owner: None,
                        constructor_index: None,
                    })
            })
            .collect();
        let mut withheld = HashMap::<String, WithheldExports>::new();
        for spelling in unavailable {
            let entries = withheld.entry(spelling.to_owned()).or_default();
            for namespace in [WithheldNamespace::Term, WithheldNamespace::Nominal] {
                let _ = entries.insert_new(
                    namespace,
                    WithheldExport {
                        kind: WithheldExportKind::Private,
                        owner: None,
                        origin: None,
                    },
                );
            }
        }
        Self {
            module,
            terms: terms
                .into_iter()
                .map(|(spelling, binder, scheme, origin)| {
                    (
                        spelling.to_owned(),
                        ExportedGlobal {
                            binder,
                            scheme: ConstrainedScheme::from_rank1_type(scheme),
                            origin,
                        },
                    )
                })
                .collect(),
            term_order,
            nominals: nominals
                .into_iter()
                .map(|(spelling, id, access, origin)| {
                    (
                        spelling.to_owned(),
                        ExportedType {
                            id,
                            parameter_count: 0,
                            constructor_count: constructor_families
                                .get(&id)
                                .map_or(1, |family| family.len().max(1)),
                            parameters: Vec::new().into_boxed_slice(),
                            constructors: if access == ExportedTypeAccess::Transparent {
                                constructor_families
                                    .get(&id)
                                    .cloned()
                                    .unwrap_or_default()
                                    .into_boxed_slice()
                            } else {
                                Box::new([])
                            },
                            access,
                            origin,
                        },
                    )
                })
                .collect(),
            nominal_order,
            nominal_names_by_id,
            constructors: constructors
                .into_iter()
                .map(|(spelling, id, payload, origin)| {
                    let mut type_work = TypeWorkBudget::unbounded();
                    let scheme = canonical_constructor_scheme(
                        id.owner(),
                        &[],
                        payload.as_ref(),
                        &mut type_work,
                    )
                    .expect("a test constructor scheme should fit the address space");
                    (
                        spelling.to_owned(),
                        ExportedConstructor {
                            id,
                            spelling: spelling.to_owned(),
                            payload,
                            scheme,
                            origin,
                        },
                    )
                })
                .collect(),
            constructor_order,
            constructor_names_by_id,
            hidden_constructors: HashMap::new(),
            hidden_constructor_order: Vec::new(),
            interface_names: HashMap::new(),
            interface_name_order: Vec::new(),
            method_names: HashMap::new(),
            method_name_order: Vec::new(),
            interfaces: Vec::new(),
            interface_positions: HashMap::new(),
            hidden_interfaces: Vec::new(),
            implementations: Vec::new(),
            implementation_positions: HashMap::new(),
            hidden_nominals: HashMap::new(),
            hidden_nominal_order: Vec::new(),
            withheld,
            withheld_order,
        }
    }

    #[cfg(test)]
    pub(crate) fn replace_first_term_parameter_kind_for_test(&mut self, kind: Kind) -> bool {
        for spelling in self.term_order.clone() {
            let Some(parameter) = self
                .terms
                .get_mut(&spelling)
                .and_then(|exported| exported.scheme.type_parameters.first_mut())
            else {
                continue;
            };
            drop(std::mem::replace(&mut parameter.1, kind));
            return true;
        }
        false
    }

    #[cfg(test)]
    pub(crate) fn replace_first_constructor_scheme_value_type_for_test(
        &mut self,
        value_type: Type,
    ) -> bool {
        let value_type = IterativeTypeOwner::new(value_type);
        for spelling in self.constructor_order.clone() {
            let Some(exported) = self.constructors.get_mut(&spelling) else {
                continue;
            };
            let displaced =
                std::mem::replace(&mut exported.scheme.value_type, value_type.into_inner());
            discard_type_iteratively(displaced);
            return true;
        }
        false
    }

    #[cfg(test)]
    pub(crate) fn replace_first_implementation_method_value_type_for_test(
        &mut self,
        value_type: Type,
    ) -> bool {
        let value_type = IterativeTypeOwner::new(value_type);
        let Some(method) = self
            .implementations
            .iter_mut()
            .find_map(|implementation| implementation.fact.methods.first_mut())
        else {
            return false;
        };
        discard_type_iteratively(std::mem::replace(
            &mut method.scheme.value_type,
            value_type.into_inner(),
        ));
        true
    }

    #[cfg(test)]
    pub(crate) fn corrupt_first_duplicate_fact_for_test(
        &mut self,
        fact: SummaryDuplicateFactForTest,
    ) -> bool {
        fn wrap_origin(origin: &mut Origin) {
            let placeholder = Origin::Source(origin.primary_span());
            let cause = std::mem::replace(origin, placeholder);
            *origin = Origin::Generated {
                cause: Box::new(cause),
                reason: crate::source::GeneratedReason::ConstantFolding,
            };
        }

        match fact {
            SummaryDuplicateFactForTest::Global => {
                let Some(global) = self
                    .term_order
                    .first()
                    .and_then(|spelling| self.terms.get_mut(spelling))
                else {
                    return false;
                };
                wrap_origin(&mut global.origin);
            }
            SummaryDuplicateFactForTest::GlobalValueType => {
                let Some(global) = self
                    .term_order
                    .first()
                    .and_then(|spelling| self.terms.get_mut(spelling))
                else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    &mut global.scheme.value_type,
                    Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                ));
            }
            SummaryDuplicateFactForTest::GlobalRequirementOrigin => {
                let Some(spelling) = self
                    .term_order
                    .iter()
                    .find(|spelling| {
                        self.terms
                            .get(*spelling)
                            .is_some_and(|global| !global.scheme.requirements.is_empty())
                    })
                    .cloned()
                else {
                    return false;
                };
                let Some(requirement) = self
                    .terms
                    .get_mut(&spelling)
                    .and_then(|global| global.scheme.requirements.first_mut())
                else {
                    return false;
                };
                wrap_origin(&mut requirement.origin);
            }
            SummaryDuplicateFactForTest::GlobalRequirementSpan => {
                let Some(spelling) = self
                    .term_order
                    .iter()
                    .find(|spelling| {
                        self.terms
                            .get(*spelling)
                            .is_some_and(|global| !global.scheme.requirements.is_empty())
                    })
                    .cloned()
                else {
                    return false;
                };
                let Some(global) = self.terms.get_mut(&spelling) else {
                    return false;
                };
                let replacement = global.origin.primary_span();
                let Some(requirement) = global.scheme.requirements.first_mut() else {
                    return false;
                };
                requirement.span = replacement;
            }
            SummaryDuplicateFactForTest::Nominal => {
                let Some(nominal) = self
                    .nominal_order
                    .first()
                    .and_then(|spelling| self.nominals.get_mut(spelling))
                else {
                    return false;
                };
                wrap_origin(&mut nominal.origin);
            }
            SummaryDuplicateFactForTest::NominalParameterOrigin => {
                let Some(spelling) = self.nominal_order.first().cloned() else {
                    return false;
                };
                let Some(parameter) = self
                    .nominals
                    .get_mut(&spelling)
                    .and_then(|nominal| nominal.parameters.first_mut())
                else {
                    return false;
                };
                wrap_origin(&mut parameter.origin);
            }
            SummaryDuplicateFactForTest::Constructor => {
                let Some(constructor) = self
                    .constructor_order
                    .first()
                    .and_then(|spelling| self.constructors.get_mut(spelling))
                else {
                    return false;
                };
                let old_value = std::mem::replace(&mut constructor.scheme.value_type, Type::Unit);
                let Type::Function(domain, result) = old_value else {
                    discard_type_iteratively(old_value);
                    return false;
                };
                discard_type_iteratively(*domain);
                if let Some(payload) = constructor.payload.replace(Type::Unit) {
                    discard_type_iteratively(payload);
                }
                constructor.scheme.value_type = Type::Function(Box::new(Type::Unit), result);
            }
            SummaryDuplicateFactForTest::ConstructorOrigin => {
                let Some(constructor) = self
                    .constructor_order
                    .first()
                    .and_then(|spelling| self.constructors.get_mut(spelling))
                else {
                    return false;
                };
                wrap_origin(&mut constructor.origin);
            }
            SummaryDuplicateFactForTest::Interface => {
                let Some(method) = self
                    .interfaces
                    .iter_mut()
                    .find_map(|interface| interface.methods.first_mut())
                else {
                    return false;
                };
                wrap_origin(&mut method.origin);
            }
            SummaryDuplicateFactForTest::InterfaceOrigin => {
                let Some(interface) = self.interfaces.first_mut() else {
                    return false;
                };
                wrap_origin(&mut interface.origin);
            }
            SummaryDuplicateFactForTest::InterfaceSpan => {
                let Some(interface) = self.interfaces.first_mut() else {
                    return false;
                };
                let Some(method) = interface.methods.first() else {
                    return false;
                };
                interface.span = method.span;
            }
            SummaryDuplicateFactForTest::InterfaceParameterOrigin => {
                let Some(interface) = self.interfaces.first_mut() else {
                    return false;
                };
                wrap_origin(&mut interface.parameter.origin);
            }
            SummaryDuplicateFactForTest::InterfaceMethodSpan => {
                let Some(interface) = self.interfaces.first_mut() else {
                    return false;
                };
                let replacement = interface.span;
                let Some(method) = interface.methods.first_mut() else {
                    return false;
                };
                method.span = replacement;
            }
            SummaryDuplicateFactForTest::InterfaceWithoutImplementationType => {
                let implementation_interfaces = self
                    .implementations
                    .iter()
                    .map(|implementation| implementation.fact.interface)
                    .collect::<HashSet<_>>();
                let Some(interface) = self
                    .interfaces
                    .iter_mut()
                    .find(|interface| !implementation_interfaces.contains(&interface.id))
                else {
                    return false;
                };
                let parameter = interface.parameter.id;
                let Some(method) = interface.methods.first_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    &mut method.value_type,
                    Type::Function(Box::new(Type::Variable(parameter)), Box::new(Type::Unit)),
                ));
            }
            SummaryDuplicateFactForTest::Implementation => {
                let Some(method) = self
                    .implementations
                    .iter_mut()
                    .find_map(|implementation| implementation.fact.methods.first_mut())
                else {
                    return false;
                };
                wrap_origin(&mut method.origin);
            }
            SummaryDuplicateFactForTest::ImplementationOrigin => {
                let Some(implementation) = self.implementations.first_mut() else {
                    return false;
                };
                wrap_origin(&mut implementation.fact.origin);
            }
            SummaryDuplicateFactForTest::ImplementationSpan => {
                let Some(implementation) = self.implementations.first_mut() else {
                    return false;
                };
                let Some(method) = implementation.fact.methods.first() else {
                    return false;
                };
                implementation.fact.span = method.span;
            }
            SummaryDuplicateFactForTest::ImplementationHeadParameterOrigin => {
                let Some(parameter) = self
                    .implementations
                    .iter_mut()
                    .find_map(|implementation| implementation.fact.head_parameters.first_mut())
                else {
                    return false;
                };
                wrap_origin(&mut parameter.origin);
            }
            SummaryDuplicateFactForTest::ImplementationHeadArgument => {
                let Some(implementation) = self.implementations.iter_mut().find(|implementation| {
                    matches!(implementation.fact.argument, Type::Application(_, _))
                        && implementation.fact.methods.first().is_some_and(|method| {
                            matches!(method.scheme.value_type, Type::Function(_, _))
                        })
                }) else {
                    return false;
                };
                let Type::Application(_, argument) = &mut implementation.fact.argument else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(argument.as_mut(), Type::Bool));
                let Some(method) = implementation.fact.methods.first_mut() else {
                    return false;
                };
                let Type::Function(domain, _) = &mut method.scheme.value_type else {
                    return false;
                };
                let Type::Application(_, argument) = domain.as_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(argument.as_mut(), Type::Bool));
            }
            SummaryDuplicateFactForTest::ImplementationPrerequisiteOrigin => {
                let Some(implementation) = self
                    .implementations
                    .iter_mut()
                    .find(|implementation| !implementation.fact.prerequisites.is_empty())
                else {
                    return false;
                };
                wrap_origin(&mut implementation.fact.prerequisites[0].origin);
                for method in &mut implementation.fact.methods {
                    let Some(requirement) = method.scheme.requirements.first_mut() else {
                        return false;
                    };
                    wrap_origin(&mut requirement.origin);
                }
            }
            SummaryDuplicateFactForTest::ImplementationPrerequisiteSpan => {
                let Some(implementation) = self
                    .implementations
                    .iter_mut()
                    .find(|implementation| !implementation.fact.prerequisites.is_empty())
                else {
                    return false;
                };
                let replacement = implementation.fact.span;
                implementation.fact.prerequisites[0].span = replacement;
                for method in &mut implementation.fact.methods {
                    let Some(requirement) = method.scheme.requirements.first_mut() else {
                        return false;
                    };
                    requirement.span = replacement;
                }
            }
            SummaryDuplicateFactForTest::ImplementationPrerequisiteType => {
                let Some(implementation) = self
                    .implementations
                    .iter_mut()
                    .find(|implementation| !implementation.fact.prerequisites.is_empty())
                else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    &mut implementation.fact.prerequisites[0].argument,
                    Type::Bool,
                ));
                for method in &mut implementation.fact.methods {
                    let Some(requirement) = method.scheme.requirements.first_mut() else {
                        return false;
                    };
                    discard_type_iteratively(std::mem::replace(
                        &mut requirement.argument,
                        Type::Bool,
                    ));
                }
            }
            SummaryDuplicateFactForTest::ImplementationMethodSpan => {
                let Some(implementation) = self.implementations.first_mut() else {
                    return false;
                };
                let replacement = implementation.fact.span;
                let Some(method) = implementation.fact.methods.first_mut() else {
                    return false;
                };
                method.span = replacement;
            }
            SummaryDuplicateFactForTest::OpaqueNominalKindClosure => {
                let Some(spelling) = self
                    .nominal_order
                    .iter()
                    .find(|spelling| {
                        self.nominals
                            .get(*spelling)
                            .is_some_and(|nominal| nominal.access == ExportedTypeAccess::Opaque)
                    })
                    .cloned()
                else {
                    return false;
                };
                let Some(nominal) = self.nominals.get_mut(&spelling) else {
                    return false;
                };
                let nominal_id = nominal.id;
                let Some(parameter) = nominal.parameters.first_mut() else {
                    return false;
                };
                drop(std::mem::replace(&mut parameter.kind, Kind::Type));
                let Some(implementation) = self.implementations.iter_mut().find(|implementation| {
                    implementation.fact.argument.outer_nominal() == Some(nominal_id)
                }) else {
                    return false;
                };
                let Some(head_parameter) = implementation.fact.head_parameters.first_mut() else {
                    return false;
                };
                drop(std::mem::replace(&mut head_parameter.kind, Kind::Type));
                let head_parameter = head_parameter.id;
                for method in &mut implementation.fact.methods {
                    let Some(method_parameter) = method
                        .scheme
                        .type_parameters
                        .iter_mut()
                        .find(|parameter| parameter.0 == head_parameter)
                    else {
                        return false;
                    };
                    drop(std::mem::replace(&mut method_parameter.1, Kind::Type));
                }
            }
        }
        true
    }

    #[cfg(test)]
    pub(crate) fn corrupt_order_for_test(&mut self, order: SummaryOrderForTest) -> bool {
        match order {
            SummaryOrderForTest::Term => self.term_order.pop().is_some(),
            SummaryOrderForTest::Nominal => self.nominal_order.pop().is_some(),
            SummaryOrderForTest::Constructor => self.constructor_order.pop().is_some(),
            SummaryOrderForTest::InterfaceName => self.interface_name_order.pop().is_some(),
            SummaryOrderForTest::MethodName => self.method_name_order.pop().is_some(),
            SummaryOrderForTest::HiddenNominal => self.hidden_nominal_order.pop().is_some(),
            SummaryOrderForTest::HiddenConstructor => self.hidden_constructor_order.pop().is_some(),
        }
    }

    #[cfg(test)]
    pub(crate) fn remove_first_reverse_index_for_test(&mut self, constructor: bool) -> bool {
        if constructor {
            let Some(identity) = self
                .constructor_order
                .first()
                .and_then(|spelling| self.constructors.get(spelling))
                .map(|constructor| constructor.id)
            else {
                return false;
            };
            self.constructor_names_by_id.remove(&identity).is_some()
        } else {
            let Some(identity) = self
                .nominal_order
                .first()
                .and_then(|spelling| self.nominals.get(spelling))
                .map(|nominal| nominal.id)
            else {
                return false;
            };
            self.nominal_names_by_id.remove(&identity).is_some()
        }
    }

    #[cfg(test)]
    pub(crate) fn duplicate_withheld_order_entry_for_test(&mut self) -> bool {
        if self.withheld_order.len() < 2 {
            return false;
        }
        self.withheld_order[1] = self.withheld_order[0].clone();
        true
    }

    #[cfg(test)]
    pub(crate) fn corrupt_withheld_for_test(
        &mut self,
        mutation: SummaryWithheldMutationForTest,
    ) -> bool {
        let first_entry = |namespace| {
            self.withheld_order
                .iter()
                .position(|entry| entry.namespace == namespace)
        };
        match mutation {
            SummaryWithheldMutationForTest::TermKind => {
                let Some(position) = first_entry(WithheldNamespace::Term) else {
                    return false;
                };
                let spelling = self.withheld_order[position].spelling.clone();
                let Some(withheld) = self
                    .withheld
                    .get_mut(&spelling)
                    .and_then(|entries| entries.term.as_mut())
                else {
                    return false;
                };
                withheld.kind = WithheldExportKind::OpaqueConstructor;
                true
            }
            SummaryWithheldMutationForTest::TermOwner => {
                let Some(position) = first_entry(WithheldNamespace::Term) else {
                    return false;
                };
                let owner = NominalTypeId::new(self.module, u32::MAX);
                let spelling = self.withheld_order[position].spelling.clone();
                let Some(withheld) = self
                    .withheld
                    .get_mut(&spelling)
                    .and_then(|entries| entries.term.as_mut())
                else {
                    return false;
                };
                withheld.owner = Some(owner);
                self.withheld_order[position].owner = Some(owner);
                true
            }
            SummaryWithheldMutationForTest::NominalKind => {
                let Some(position) = first_entry(WithheldNamespace::Nominal) else {
                    return false;
                };
                let spelling = self.withheld_order[position].spelling.clone();
                let Some(withheld) = self
                    .withheld
                    .get_mut(&spelling)
                    .and_then(|entries| entries.nominal.as_mut())
                else {
                    return false;
                };
                withheld.kind = WithheldExportKind::OpaqueConstructor;
                true
            }
            SummaryWithheldMutationForTest::NominalOwner => {
                let Some(position) = first_entry(WithheldNamespace::Nominal) else {
                    return false;
                };
                let owner = NominalTypeId::new(self.module, u32::MAX);
                let spelling = self.withheld_order[position].spelling.clone();
                let Some(withheld) = self
                    .withheld
                    .get_mut(&spelling)
                    .and_then(|entries| entries.nominal.as_mut())
                else {
                    return false;
                };
                withheld.owner = Some(owner);
                self.withheld_order[position].owner = Some(owner);
                true
            }
            SummaryWithheldMutationForTest::ConstructorOwner => {
                let Some(position) = first_entry(WithheldNamespace::Constructor) else {
                    return false;
                };
                let spelling = self.withheld_order[position].spelling.clone();
                let old_owner = self.withheld_order[position].owner;
                let Some(entries) = self.withheld.get_mut(&spelling) else {
                    return false;
                };
                let Some(constructor_position) = entries.constructor_positions.remove(&old_owner)
                else {
                    return false;
                };
                let Some(withheld) = entries.constructor.get_mut(constructor_position) else {
                    return false;
                };
                withheld.owner = None;
                entries
                    .constructor_positions
                    .insert(None, constructor_position);
                self.withheld_order[position].owner = None;
                true
            }
            SummaryWithheldMutationForTest::ConstructorPosition => {
                let Some(position) = first_entry(WithheldNamespace::Constructor) else {
                    return false;
                };
                let entry = &self.withheld_order[position];
                let Some(entries) = self.withheld.get_mut(&entry.spelling) else {
                    return false;
                };
                entries
                    .constructor_positions
                    .insert(entry.owner, usize::MAX);
                true
            }
            SummaryWithheldMutationForTest::MapOnly => {
                let spelling = "forged-map-only".to_owned();
                let entries = WithheldExports {
                    term: Some(WithheldExport {
                        kind: WithheldExportKind::Private,
                        owner: None,
                        origin: None,
                    }),
                    ..WithheldExports::default()
                };
                if let Some(displaced) = self.withheld.insert(spelling, entries) {
                    discard_withheld_exports(displaced);
                    false
                } else {
                    true
                }
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn corrupt_position_index_for_test(&mut self, implementation: bool) -> bool {
        if implementation {
            let Some(identity) = self.implementations.first().map(|fact| fact.fact.id) else {
                return false;
            };
            self.implementation_positions.insert(identity, usize::MAX);
        } else {
            let Some(identity) = self.interfaces.first().map(|fact| fact.id) else {
                return false;
            };
            self.interface_positions.insert(identity, usize::MAX);
        }
        true
    }

    #[cfg(test)]
    pub(crate) fn increment_first_hidden_constructor_count_for_test(&mut self) -> bool {
        let Some(nominal) = self
            .hidden_nominal_order
            .first()
            .and_then(|identity| self.hidden_nominals.get_mut(identity))
        else {
            return false;
        };
        let Some(count) = nominal.constructor_count.checked_add(1) else {
            return false;
        };
        nominal.constructor_count = count;
        true
    }

    #[cfg(test)]
    pub(crate) fn corrupt_carrier_for_test(
        &mut self,
        mutation: SummaryCarrierMutationForTest,
    ) -> bool {
        let arrow_kind = || Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let replace_parameter_kind = |parameter: &mut ResolvedTypeVariable| {
            drop(std::mem::replace(&mut parameter.kind, arrow_kind()));
        };
        let replace_parameter_kind_with_type = |parameter: &mut ResolvedTypeVariable| {
            drop(std::mem::replace(&mut parameter.kind, Kind::Type));
        };
        let replace_scheme_kind = |parameter: &mut (TypeVariableId, Kind)| {
            drop(std::mem::replace(&mut parameter.1, Kind::Type));
        };
        match mutation {
            SummaryCarrierMutationForTest::PublicNominalKind => self
                .nominal_order
                .first()
                .and_then(|spelling| self.nominals.get_mut(spelling))
                .and_then(|nominal| nominal.parameters.first_mut())
                .is_some_and(|parameter| {
                    replace_parameter_kind_with_type(parameter);
                    true
                }),
            SummaryCarrierMutationForTest::PublicNominalParameterIdentity => self
                .nominal_order
                .first()
                .and_then(|spelling| self.nominals.get_mut(spelling))
                .and_then(|nominal| nominal.parameters.last_mut())
                .is_some_and(|parameter| {
                    parameter.id =
                        TypeVariableId::resolved(parameter.id.module().unwrap(), u32::MAX);
                    true
                }),
            SummaryCarrierMutationForTest::PublicNominalParameterOwner => self
                .nominal_order
                .first()
                .and_then(|spelling| self.nominals.get_mut(spelling))
                .and_then(|nominal| nominal.parameters.first_mut())
                .is_some_and(|parameter| {
                    parameter.id =
                        TypeVariableId::resolved(ModuleId::new(u32::MAX - 1), parameter.id.local());
                    true
                }),
            SummaryCarrierMutationForTest::PublicNominalParameterOrder => self
                .nominal_order
                .first()
                .and_then(|spelling| self.nominals.get_mut(spelling))
                .map(|nominal| &mut nominal.parameters)
                .filter(|parameters| parameters.len() >= 2)
                .is_some_and(|parameters| {
                    parameters.swap(0, 1);
                    true
                }),
            SummaryCarrierMutationForTest::PublicConstructorFamilyOrdinal => self
                .nominal_order
                .first()
                .and_then(|spelling| self.nominals.get_mut(spelling))
                .map(|nominal| &mut nominal.constructors)
                .filter(|constructors| constructors.len() >= 2)
                .is_some_and(|constructors| {
                    constructors.swap(0, 1);
                    true
                }),
            SummaryCarrierMutationForTest::PublicConstructorFamilyOwner => self
                .nominal_order
                .first()
                .and_then(|spelling| self.nominals.get_mut(spelling))
                .and_then(|nominal| nominal.constructors.first_mut())
                .is_some_and(|constructor| {
                    *constructor = ConstructorId::new(
                        NominalTypeId::new(constructor.owner().module(), u32::MAX),
                        constructor.constructor(),
                    );
                    true
                }),
            SummaryCarrierMutationForTest::PublicConstructorResultOwner => {
                let Some(spelling) = self.constructor_order.first().cloned() else {
                    return false;
                };
                let Some(constructor) = self.constructors.get_mut(&spelling) else {
                    return false;
                };
                let result = match &mut constructor.scheme.value_type {
                    Type::Function(_, result) => result.as_mut(),
                    result => result,
                };
                let mut root = result;
                while let Type::Application(function, _) = root {
                    root = function;
                }
                let Type::Nominal(identity) = root else {
                    return false;
                };
                *identity = NominalTypeId::new(ModuleId::new(u32::MAX - 1), 0);
                true
            }
            SummaryCarrierMutationForTest::HiddenNominalKind => self
                .hidden_nominal_order
                .first()
                .and_then(|identity| self.hidden_nominals.get_mut(identity))
                .and_then(|nominal| nominal.parameters.first_mut())
                .is_some_and(|parameter| {
                    replace_parameter_kind_with_type(parameter);
                    true
                }),
            SummaryCarrierMutationForTest::HiddenNominalParameterIdentity => self
                .hidden_nominal_order
                .first()
                .and_then(|identity| self.hidden_nominals.get_mut(identity))
                .and_then(|nominal| nominal.parameters.last_mut())
                .is_some_and(|parameter| {
                    parameter.id = TypeVariableId::resolved(
                        parameter.id.module().unwrap_or(self.module),
                        u32::MAX,
                    );
                    true
                }),
            SummaryCarrierMutationForTest::HiddenNominalParameterOwner => self
                .hidden_nominal_order
                .first()
                .and_then(|identity| self.hidden_nominals.get_mut(identity))
                .and_then(|nominal| nominal.parameters.first_mut())
                .is_some_and(|parameter| {
                    parameter.id =
                        TypeVariableId::resolved(ModuleId::new(u32::MAX - 1), parameter.id.local());
                    true
                }),
            SummaryCarrierMutationForTest::HiddenNominalParameterOrder => self
                .hidden_nominal_order
                .first()
                .and_then(|identity| self.hidden_nominals.get_mut(identity))
                .map(|nominal| &mut nominal.parameters)
                .filter(|parameters| parameters.len() >= 2)
                .is_some_and(|parameters| {
                    parameters.swap(0, 1);
                    true
                }),
            SummaryCarrierMutationForTest::HiddenNominalAccess => self
                .hidden_nominal_order
                .first()
                .and_then(|identity| self.hidden_nominals.get_mut(identity))
                .is_some_and(|nominal| {
                    nominal.access = ImportedTypeAccess::Opaque;
                    true
                }),
            SummaryCarrierMutationForTest::PublicConstructorPayload => {
                let Some(spelling) = self.constructor_order.first().cloned() else {
                    return false;
                };
                let Some(payload) = self
                    .constructors
                    .get_mut(&spelling)
                    .and_then(|constructor| constructor.payload.as_mut())
                else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(payload, Type::Unit));
                true
            }
            SummaryCarrierMutationForTest::PublicConstructorPayloadDomainKind => {
                let Some(spelling) = self.constructor_order.first().cloned() else {
                    return false;
                };
                let Some(constructor) = self.constructors.get_mut(&spelling) else {
                    return false;
                };
                let Some(parameter) = constructor.scheme.type_parameters.last().map(|pair| pair.0)
                else {
                    return false;
                };
                let invalid =
                    || Type::Application(Box::new(Type::Variable(parameter)), Box::new(Type::Int));
                let Some(payload) = constructor.payload.as_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(payload, invalid()));
                let Type::Function(domain, _) = &mut constructor.scheme.value_type else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(domain.as_mut(), invalid()));
                true
            }
            SummaryCarrierMutationForTest::HiddenConstructorPayload => {
                let Some(identity) = self.hidden_constructor_order.first().copied() else {
                    return false;
                };
                let Some(payload) = self
                    .hidden_constructors
                    .get_mut(&identity)
                    .and_then(|constructor| constructor.payload.as_mut())
                else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(payload, Type::Unit));
                true
            }
            SummaryCarrierMutationForTest::HiddenConstructorPayloadDomainKind => {
                let Some(identity) = self.hidden_constructor_order.first().copied() else {
                    return false;
                };
                let Some(constructor) = self.hidden_constructors.get_mut(&identity) else {
                    return false;
                };
                let Some(parameter) = constructor.scheme.type_parameters.last().map(|pair| pair.0)
                else {
                    return false;
                };
                let invalid =
                    || Type::Application(Box::new(Type::Variable(parameter)), Box::new(Type::Int));
                let Some(payload) = constructor.payload.as_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(payload, invalid()));
                let Type::Function(domain, _) = &mut constructor.scheme.value_type else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(domain.as_mut(), invalid()));
                true
            }
            SummaryCarrierMutationForTest::PublicConstructorSchemeKind => {
                let Some(spelling) = self.constructor_order.first().cloned() else {
                    return false;
                };
                let Some(parameter) = self
                    .constructors
                    .get_mut(&spelling)
                    .and_then(|constructor| constructor.scheme.type_parameters.first_mut())
                else {
                    return false;
                };
                replace_scheme_kind(parameter);
                true
            }
            SummaryCarrierMutationForTest::PublicConstructorSchemeParameterIdentity => {
                let Some(spelling) = self.constructor_order.first().cloned() else {
                    return false;
                };
                let Some(parameter) = self
                    .constructors
                    .get_mut(&spelling)
                    .and_then(|constructor| constructor.scheme.type_parameters.first_mut())
                else {
                    return false;
                };
                parameter.0 =
                    TypeVariableId::resolved(parameter.0.module().unwrap_or(self.module), u32::MAX);
                true
            }
            SummaryCarrierMutationForTest::HiddenConstructorSchemeKind => {
                let Some(identity) = self.hidden_constructor_order.first().copied() else {
                    return false;
                };
                let Some(parameter) = self
                    .hidden_constructors
                    .get_mut(&identity)
                    .and_then(|constructor| constructor.scheme.type_parameters.first_mut())
                else {
                    return false;
                };
                replace_scheme_kind(parameter);
                true
            }
            SummaryCarrierMutationForTest::HiddenConstructorSchemeParameterIdentity => {
                let Some(identity) = self.hidden_constructor_order.first().copied() else {
                    return false;
                };
                let Some(parameter) = self
                    .hidden_constructors
                    .get_mut(&identity)
                    .and_then(|constructor| constructor.scheme.type_parameters.first_mut())
                else {
                    return false;
                };
                parameter.0 =
                    TypeVariableId::resolved(parameter.0.module().unwrap_or(self.module), u32::MAX);
                true
            }
            SummaryCarrierMutationForTest::HiddenConstructorResultOwner => {
                let Some(identity) = self.hidden_constructor_order.first().copied() else {
                    return false;
                };
                let Some(constructor) = self.hidden_constructors.get_mut(&identity) else {
                    return false;
                };
                let result = match &mut constructor.scheme.value_type {
                    Type::Function(_, result) => result.as_mut(),
                    result => result,
                };
                let mut root = result;
                while let Type::Application(function, _) = root {
                    root = function;
                }
                let Type::Nominal(identity) = root else {
                    return false;
                };
                *identity = NominalTypeId::new(ModuleId::new(u32::MAX - 1), 0);
                true
            }
            SummaryCarrierMutationForTest::PublicInterfaceKind => {
                self.interfaces.first_mut().is_some_and(|interface| {
                    replace_parameter_kind(&mut interface.parameter);
                    true
                })
            }
            SummaryCarrierMutationForTest::PublicInterfaceParameterIdentity => {
                self.interfaces.first_mut().is_some_and(|interface| {
                    interface.parameter.id = TypeVariableId::resolved(self.module, u32::MAX);
                    true
                })
            }
            SummaryCarrierMutationForTest::PublicInterfaceParameterOwner => {
                self.interfaces.first_mut().is_some_and(|interface| {
                    interface.parameter.id = TypeVariableId::resolved(
                        ModuleId::new(u32::MAX - 1),
                        interface.parameter.id.local(),
                    );
                    true
                })
            }
            SummaryCarrierMutationForTest::HiddenInterfaceKind => {
                self.hidden_interfaces.first_mut().is_some_and(|interface| {
                    replace_parameter_kind(&mut interface.parameter);
                    true
                })
            }
            SummaryCarrierMutationForTest::HiddenInterfaceParameterIdentity => {
                self.hidden_interfaces.first_mut().is_some_and(|interface| {
                    interface.parameter.id = TypeVariableId::resolved(
                        interface.parameter.id.module().unwrap_or(self.module),
                        u32::MAX,
                    );
                    true
                })
            }
            SummaryCarrierMutationForTest::HiddenInterfaceParameterOwner => {
                self.hidden_interfaces.first_mut().is_some_and(|interface| {
                    interface.parameter.id = TypeVariableId::resolved(
                        ModuleId::new(u32::MAX - 1),
                        interface.parameter.id.local(),
                    );
                    true
                })
            }
            SummaryCarrierMutationForTest::HiddenInterfaceIdentity => {
                self.hidden_interfaces.first_mut().is_some_and(|interface| {
                    interface.id = InterfaceId::new(interface.id.module(), u32::MAX);
                    true
                })
            }
            SummaryCarrierMutationForTest::PublicInterfaceMethodType => self
                .interfaces
                .first_mut()
                .and_then(|interface| interface.methods.first_mut())
                .is_some_and(|method| {
                    discard_type_iteratively(std::mem::replace(
                        &mut method.value_type,
                        Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
                    ));
                    true
                }),
            SummaryCarrierMutationForTest::PublicInterfaceMethodNonFunction => {
                let Some(interface) = self.interfaces.first_mut() else {
                    return false;
                };
                let parameter = interface.parameter.id;
                let Some(method) = interface.methods.first_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    &mut method.value_type,
                    Type::Variable(parameter),
                ));
                true
            }
            SummaryCarrierMutationForTest::PublicInterfaceEmptyMethods => {
                let Some(methods) = self.interfaces.first().map(|interface| {
                    interface
                        .methods
                        .iter()
                        .map(|method| method.id)
                        .collect::<HashSet<_>>()
                }) else {
                    return false;
                };
                self.method_names
                    .retain(|_, identity| !methods.contains(identity));
                self.method_name_order
                    .retain(|spelling| self.method_names.contains_key(spelling));
                let Some(interface) = self.interfaces.first_mut() else {
                    return false;
                };
                drop(std::mem::take(&mut interface.methods));
                true
            }
            SummaryCarrierMutationForTest::HiddenInterfaceMethodType => self
                .hidden_interfaces
                .first_mut()
                .and_then(|interface| interface.methods.first_mut())
                .is_some_and(|method| {
                    discard_type_iteratively(std::mem::replace(
                        &mut method.value_type,
                        Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
                    ));
                    true
                }),
            SummaryCarrierMutationForTest::HiddenInterfaceMethodIdentity => self
                .hidden_interfaces
                .first_mut()
                .and_then(|interface| interface.methods.first_mut())
                .is_some_and(|method| {
                    method.id = MethodId::new(method.id.interface(), u32::MAX);
                    true
                }),
            SummaryCarrierMutationForTest::HiddenInterfaceMethodOwner => self
                .hidden_interfaces
                .first_mut()
                .and_then(|interface| interface.methods.first_mut())
                .is_some_and(|method| {
                    method.id = MethodId::new(
                        InterfaceId::new(ModuleId::new(u32::MAX - 1), 0),
                        method.id.declaration(),
                    );
                    true
                }),
            SummaryCarrierMutationForTest::PublicInterfaceMethodFreeBinder
            | SummaryCarrierMutationForTest::HiddenInterfaceMethodFreeBinder => {
                let interface = match mutation {
                    SummaryCarrierMutationForTest::PublicInterfaceMethodFreeBinder => {
                        self.interfaces.first_mut()
                    }
                    SummaryCarrierMutationForTest::HiddenInterfaceMethodFreeBinder => {
                        self.hidden_interfaces.first_mut()
                    }
                    _ => unreachable!(),
                };
                let Some(method) = interface.and_then(|interface| interface.methods.first_mut())
                else {
                    return false;
                };
                let unbound =
                    Type::Variable(TypeVariableId::resolved(ModuleId::new(u32::MAX - 1), 0));
                discard_type_iteratively(std::mem::replace(
                    &mut method.value_type,
                    Type::Function(Box::new(unbound), Box::new(Type::Unit)),
                ));
                true
            }
            SummaryCarrierMutationForTest::PublicInterfaceMethodKind
            | SummaryCarrierMutationForTest::HiddenInterfaceMethodKind => {
                let interface = match mutation {
                    SummaryCarrierMutationForTest::PublicInterfaceMethodKind => {
                        self.interfaces.first_mut()
                    }
                    SummaryCarrierMutationForTest::HiddenInterfaceMethodKind => {
                        self.hidden_interfaces.first_mut()
                    }
                    _ => unreachable!(),
                };
                let Some(interface) = interface else {
                    return false;
                };
                let parameter = interface.parameter.id;
                let Some(method) = interface.methods.first_mut() else {
                    return false;
                };
                let invalid =
                    Type::Application(Box::new(Type::Variable(parameter)), Box::new(Type::Int));
                discard_type_iteratively(std::mem::replace(
                    &mut method.value_type,
                    Type::Function(Box::new(invalid), Box::new(Type::Variable(parameter))),
                ));
                true
            }
            SummaryCarrierMutationForTest::InterfaceIdentity => {
                let Some(original) = self.interfaces.first().map(|interface| interface.id) else {
                    return false;
                };
                let Some(position) = self.interface_positions.remove(&original) else {
                    return false;
                };
                let replacement = InterfaceId::new(original.module(), u32::MAX);
                let Some(interface) = self.interfaces.get_mut(position) else {
                    return false;
                };
                interface.id = replacement;
                for method in &mut interface.methods {
                    let old = method.id;
                    method.id = MethodId::new(replacement, old.declaration());
                    for target in self.method_names.values_mut() {
                        if *target == old {
                            *target = method.id;
                        }
                    }
                }
                for target in self.interface_names.values_mut() {
                    if *target == original {
                        *target = replacement;
                    }
                }
                self.interface_positions.insert(replacement, position);
                true
            }
            SummaryCarrierMutationForTest::MethodIdentity => {
                let Some(method) = self
                    .interfaces
                    .first_mut()
                    .and_then(|interface| interface.methods.first_mut())
                else {
                    return false;
                };
                let original = method.id;
                method.id = MethodId::new(
                    InterfaceId::new(method.id.interface().module(), u32::MAX),
                    method.id.declaration(),
                );
                for target in self.method_names.values_mut() {
                    if *target == original {
                        *target = method.id;
                    }
                }
                true
            }
            SummaryCarrierMutationForTest::MethodOrdinal => {
                let Some(method) = self
                    .interfaces
                    .first_mut()
                    .and_then(|interface| interface.methods.first_mut())
                else {
                    return false;
                };
                let original = method.id;
                method.id = MethodId::new(method.id.interface(), u32::MAX);
                for target in self.method_names.values_mut() {
                    if *target == original {
                        *target = method.id;
                    }
                }
                true
            }
            SummaryCarrierMutationForTest::InterfaceNameTarget => {
                let Some(spelling) = self.interface_name_order.first() else {
                    return false;
                };
                let Some(interface) = self.interface_names.get_mut(spelling) else {
                    return false;
                };
                *interface = InterfaceId::new(interface.module(), u32::MAX);
                true
            }
            SummaryCarrierMutationForTest::MethodNameTarget => {
                let Some(spelling) = self.method_name_order.first() else {
                    return false;
                };
                let Some(method) = self.method_names.get_mut(spelling) else {
                    return false;
                };
                *method = MethodId::new(method.interface(), u32::MAX);
                true
            }
            SummaryCarrierMutationForTest::GlobalParameterIdentity => {
                let Some(spelling) = self.term_order.first().cloned() else {
                    return false;
                };
                let Some(parameter) = self
                    .terms
                    .get_mut(&spelling)
                    .and_then(|global| global.scheme.type_parameters.last_mut())
                else {
                    return false;
                };
                let module = parameter.0.module().unwrap_or(self.module);
                parameter.0 = TypeVariableId::resolved(module, u32::MAX);
                true
            }
            SummaryCarrierMutationForTest::GlobalParameterOrder => {
                let Some(spelling) = self.term_order.first().cloned() else {
                    return false;
                };
                let Some(parameters) = self
                    .terms
                    .get_mut(&spelling)
                    .map(|global| &mut global.scheme.type_parameters)
                    .filter(|parameters| parameters.len() >= 2)
                else {
                    return false;
                };
                parameters.swap(0, 1);
                true
            }
            SummaryCarrierMutationForTest::GlobalUnusedParameter => {
                let Some(spelling) = self.term_order.first().cloned() else {
                    return false;
                };
                let Some(global) = self
                    .terms
                    .get_mut(&spelling)
                    .filter(|global| !global.scheme.type_parameters.is_empty())
                else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    &mut global.scheme.value_type,
                    Type::Unit,
                ));
                true
            }
            SummaryCarrierMutationForTest::GlobalRequirementIdentity => {
                let Some(spelling) = self.term_order.first().cloned() else {
                    return false;
                };
                let Some(global) = self.terms.get_mut(&spelling) else {
                    return false;
                };
                let Some(requirement) = global.scheme.requirements.first_mut() else {
                    return false;
                };
                requirement.id = RequirementId::new(
                    crate::interface::RequirementOwner::Global(global.binder),
                    u32::MAX,
                );
                true
            }
            SummaryCarrierMutationForTest::GlobalRequirementInterface => {
                let Some(requirement) = self
                    .term_order
                    .first()
                    .and_then(|spelling| self.terms.get_mut(spelling))
                    .and_then(|global| global.scheme.requirements.first_mut())
                else {
                    return false;
                };
                requirement.interface = InterfaceId::new(ModuleId::new(u32::MAX - 1), 0);
                true
            }
            SummaryCarrierMutationForTest::GlobalRequirementArgumentKind => {
                let Some(global) = self
                    .term_order
                    .first()
                    .and_then(|spelling| self.terms.get_mut(spelling))
                else {
                    return false;
                };
                let Some(parameter) = global.scheme.type_parameters.last().map(|pair| pair.0)
                else {
                    return false;
                };
                let Some(requirement) = global.scheme.requirements.first_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    &mut requirement.argument,
                    Type::Application(Box::new(Type::Variable(parameter)), Box::new(Type::Int)),
                ));
                true
            }
            SummaryCarrierMutationForTest::GlobalParameterOwner => {
                let Some(parameter) = self
                    .term_order
                    .first()
                    .and_then(|spelling| self.terms.get_mut(spelling))
                    .and_then(|global| global.scheme.type_parameters.first_mut())
                else {
                    return false;
                };
                parameter.0 =
                    TypeVariableId::resolved(ModuleId::new(u32::MAX - 1), parameter.0.local());
                true
            }
            SummaryCarrierMutationForTest::GlobalParameterKind => {
                let Some(parameter) = self
                    .term_order
                    .first()
                    .and_then(|spelling| self.terms.get_mut(spelling))
                    .and_then(|global| global.scheme.type_parameters.last_mut())
                else {
                    return false;
                };
                drop(std::mem::replace(&mut parameter.1, arrow_kind()));
                true
            }
            SummaryCarrierMutationForTest::ImplementationHeadKind => self
                .implementations
                .iter_mut()
                .find_map(|implementation| implementation.fact.head_parameters.first_mut())
                .is_some_and(|parameter| {
                    replace_parameter_kind_with_type(parameter);
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationHeadIdentity => self
                .implementations
                .iter_mut()
                .find_map(|implementation| implementation.fact.head_parameters.last_mut())
                .is_some_and(|parameter| {
                    parameter.id = TypeVariableId::resolved(
                        parameter.id.module().unwrap_or(self.module),
                        u32::MAX,
                    );
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationHeadOrder => self
                .implementations
                .iter_mut()
                .find(|implementation| implementation.fact.head_parameters.len() >= 2)
                .is_some_and(|implementation| {
                    implementation.fact.head_parameters.swap(0, 1);
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationHeadOwner => self
                .implementations
                .iter_mut()
                .find_map(|implementation| implementation.fact.head_parameters.last_mut())
                .is_some_and(|parameter| {
                    parameter.id =
                        TypeVariableId::resolved(ModuleId::new(u32::MAX - 1), parameter.id.local());
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationArgument => self
                .implementations
                .first_mut()
                .is_some_and(|implementation| {
                    discard_type_iteratively(std::mem::replace(
                        &mut implementation.fact.argument,
                        Type::Unit,
                    ));
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationSemanticHead => {
                let Some(other) = self
                    .nominal_order
                    .iter()
                    .filter_map(|spelling| self.nominals.get(spelling))
                    .nth(1)
                    .map(|nominal| nominal.id)
                else {
                    return false;
                };
                let Some(implementation) = self
                    .implementations
                    .iter_mut()
                    .find(|implementation| implementation.fact.head_parameters.len() >= 2)
                else {
                    return false;
                };
                let mut argument = Type::Nominal(other);
                for parameter in &implementation.fact.head_parameters {
                    argument = Type::Application(
                        Box::new(argument),
                        Box::new(Type::Variable(parameter.id)),
                    );
                }
                discard_type_iteratively(std::mem::replace(
                    &mut implementation.fact.argument,
                    argument,
                ));
                true
            }
            SummaryCarrierMutationForTest::ImplementationInterfaceIdentity => self
                .implementations
                .first_mut()
                .is_some_and(|implementation| {
                    implementation.fact.interface =
                        InterfaceId::new(ModuleId::new(u32::MAX - 1), 0);
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationPrerequisiteIdentity => self
                .implementations
                .iter_mut()
                .find_map(|implementation| {
                    implementation
                        .fact
                        .prerequisites
                        .first_mut()
                        .map(|requirement| (implementation.fact.id, requirement))
                })
                .is_some_and(|(implementation, requirement)| {
                    requirement.id = RequirementId::new(
                        crate::interface::RequirementOwner::Impl(implementation),
                        u32::MAX,
                    );
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationPrerequisiteOrder => self
                .implementations
                .iter_mut()
                .find(|implementation| implementation.fact.prerequisites.len() >= 2)
                .is_some_and(|implementation| {
                    implementation.fact.prerequisites.swap(0, 1);
                    for method in &mut implementation.fact.methods {
                        method.scheme.requirements.swap(0, 1);
                    }
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationPrerequisiteDuplicate => {
                let Some(implementation) = self
                    .implementations
                    .iter_mut()
                    .find(|implementation| implementation.fact.prerequisites.len() >= 2)
                else {
                    return false;
                };
                let (first, rest) = implementation.fact.prerequisites.split_first_mut().unwrap();
                let second = &mut rest[0];
                second.interface = first.interface;
                let mut type_work = TypeWorkBudget::unbounded();
                let replacement = clone_type_with_budget(first.argument(), &mut type_work).unwrap();
                discard_type_iteratively(std::mem::replace(&mut second.argument, replacement));
                for method in &mut implementation.fact.methods {
                    let (first, rest) = method.scheme.requirements.split_first_mut().unwrap();
                    let second = &mut rest[0];
                    second.interface = first.interface;
                    let replacement =
                        clone_type_with_budget(first.argument(), &mut type_work).unwrap();
                    discard_type_iteratively(std::mem::replace(&mut second.argument, replacement));
                }
                true
            }
            SummaryCarrierMutationForTest::ImplementationPrerequisiteKind => {
                let Some(implementation) = self
                    .implementations
                    .iter_mut()
                    .find(|implementation| !implementation.fact.prerequisites.is_empty())
                else {
                    return false;
                };
                let Type::Application(partial_head, _) = implementation.fact.argument() else {
                    return false;
                };
                let mut type_work = TypeWorkBudget::unbounded();
                let Ok(prerequisite) = clone_type_with_budget(partial_head, &mut type_work) else {
                    return false;
                };
                let Ok(method_requirement) = clone_type_with_budget(partial_head, &mut type_work)
                else {
                    discard_type_iteratively(prerequisite);
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    &mut implementation.fact.prerequisites[0].argument,
                    prerequisite,
                ));
                for method in &mut implementation.fact.methods {
                    discard_type_iteratively(std::mem::replace(
                        &mut method.scheme.requirements[0].argument,
                        clone_type_with_budget(&method_requirement, &mut type_work)
                            .expect("an in-memory prerequisite mirror should fit"),
                    ));
                }
                discard_type_iteratively(method_requirement);
                true
            }
            SummaryCarrierMutationForTest::ImplementationPrerequisiteInterface => self
                .implementations
                .iter_mut()
                .find_map(|implementation| implementation.fact.prerequisites.first_mut())
                .is_some_and(|prerequisite| {
                    prerequisite.interface = InterfaceId::new(ModuleId::new(u32::MAX - 1), 0);
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationPrerequisiteArgument => {
                let Some(implementation) = self
                    .implementations
                    .iter_mut()
                    .find(|implementation| !implementation.fact.prerequisites.is_empty())
                else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    &mut implementation.fact.prerequisites[0].argument,
                    Type::Int,
                ));
                true
            }
            SummaryCarrierMutationForTest::ImplementationPrerequisiteOriginMirror => {
                let Some(prerequisite) = self
                    .implementations
                    .iter_mut()
                    .find_map(|implementation| implementation.fact.prerequisites.first_mut())
                else {
                    return false;
                };
                let cause = prerequisite.origin.clone();
                discard_origin_iteratively(std::mem::replace(
                    &mut prerequisite.origin,
                    Origin::Generated {
                        cause: Box::new(cause),
                        reason: crate::source::GeneratedReason::ConstantFolding,
                    },
                ));
                true
            }
            SummaryCarrierMutationForTest::ImplementationPrerequisiteSpanMirror => {
                let Some(implementation) = self
                    .implementations
                    .iter_mut()
                    .find(|implementation| !implementation.fact.prerequisites.is_empty())
                else {
                    return false;
                };
                implementation.fact.prerequisites[0].span = implementation.fact.span;
                true
            }
            SummaryCarrierMutationForTest::ImplementationMethodRequirementIdentity => self
                .implementations
                .iter_mut()
                .find_map(|implementation| {
                    implementation
                        .fact
                        .methods
                        .iter_mut()
                        .find_map(|method| method.scheme.requirements.first_mut())
                })
                .is_some_and(|requirement| {
                    requirement.id = RequirementId::new(requirement.id.owner(), u32::MAX);
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationMethodSchemeParameterIdentity => self
                .implementations
                .iter_mut()
                .find_map(|implementation| {
                    implementation
                        .fact
                        .methods
                        .iter_mut()
                        .find_map(|method| method.scheme.type_parameters.first_mut())
                })
                .is_some_and(|parameter| {
                    parameter.0 = TypeVariableId::resolved(
                        parameter.0.module().unwrap_or(self.module),
                        u32::MAX,
                    );
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationMethodSchemeParameterKind => self
                .implementations
                .iter_mut()
                .find_map(|implementation| {
                    implementation
                        .fact
                        .methods
                        .iter_mut()
                        .find_map(|method| method.scheme.type_parameters.first_mut())
                })
                .is_some_and(|parameter| {
                    replace_scheme_kind(parameter);
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationMethodIdentity => self
                .implementations
                .first_mut()
                .and_then(|implementation| implementation.fact.methods.first_mut())
                .is_some_and(|method| {
                    method.id = ImplMethodId::new(
                        ImplId::new(method.id.implementation().module(), u32::MAX),
                        method.id.method(),
                    );
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationMethodMapping => self
                .implementations
                .first_mut()
                .and_then(|implementation| implementation.fact.methods.first_mut())
                .is_some_and(|method| {
                    method.method = MethodId::new(method.method.interface(), u32::MAX);
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationMethodBinder => self
                .implementations
                .first_mut()
                .and_then(|implementation| implementation.fact.methods.first_mut())
                .is_some_and(|method| {
                    method.binder = BinderId::resolved(ModuleId::new(u32::MAX), u32::MAX);
                    true
                }),
            SummaryCarrierMutationForTest::ImplementationAuthorization => {
                let Some(implementation) = self.implementations.first_mut() else {
                    return false;
                };
                implementation.authorization =
                    ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                        from: self.module,
                        to: self.module,
                        import_span: implementation.fact.span,
                    }]);
                true
            }
            SummaryCarrierMutationForTest::ImplementationOverlap => {
                if self.implementations.len() < 2 {
                    return false;
                }
                let (first, rest) = self.implementations.split_first_mut().unwrap();
                let first_outer = first.fact.argument().outer_nominal();
                let Some(second) = rest.first_mut() else {
                    return false;
                };
                if second.fact.head_parameters.is_empty() {
                    return false;
                }
                let Some(nominal) = first_outer else {
                    return false;
                };
                let mut argument = Type::Nominal(nominal);
                for parameter in &second.fact.head_parameters {
                    argument = Type::Application(
                        Box::new(argument),
                        Box::new(Type::Variable(parameter.id)),
                    );
                }
                let method_type =
                    Type::Function(Box::new(argument.clone()), Box::new(argument.clone()));
                discard_type_iteratively(std::mem::replace(&mut second.fact.argument, argument));
                let Some(method) = second.fact.methods.first_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    &mut method.scheme.value_type,
                    method_type,
                ));
                true
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn corrupt_first_constructor_fusion_obligation_for_test(
        &mut self,
        mutation: SummaryConstructorFusionMutationForTest,
    ) -> bool {
        let module = self.module;
        let requirement_interface = self.interfaces.first().map(|interface| interface.id);
        let registered_foreign_parameter = self
            .interfaces
            .first()
            .map(|interface| interface.parameter.id);
        let Some(spelling) = self.constructor_order.first().cloned() else {
            return false;
        };
        let Some(constructor) = self.constructors.get_mut(&spelling) else {
            return false;
        };
        let Type::Function(domain, result) = &mut constructor.scheme.value_type else {
            return false;
        };
        match mutation {
            SummaryConstructorFusionMutationForTest::RegisteredForeignPayloadVariable => {
                let Some(foreign) = registered_foreign_parameter else {
                    return false;
                };
                let invalid = Type::Variable(foreign);
                let mirror = Type::Variable(foreign);
                let Some(payload) = constructor.payload.as_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(payload, invalid));
                discard_type_iteratively(std::mem::replace(domain.as_mut(), mirror));
                true
            }
            SummaryConstructorFusionMutationForTest::UnboundPayloadVariable
            | SummaryConstructorFusionMutationForTest::InferencePayload
            | SummaryConstructorFusionMutationForTest::OuterForallPayload
            | SummaryConstructorFusionMutationForTest::NestedForallPayload => {
                let fresh = TypeVariableId::resolved(module, u32::MAX);
                let invalid = match mutation {
                    SummaryConstructorFusionMutationForTest::UnboundPayloadVariable => {
                        Type::Variable(fresh)
                    }
                    SummaryConstructorFusionMutationForTest::InferencePayload => {
                        Type::Inference(crate::types::InferenceVariableId::new(u32::MAX))
                    }
                    SummaryConstructorFusionMutationForTest::OuterForallPayload => Type::Forall(
                        vec![(fresh, Kind::Type)].into_boxed_slice(),
                        Box::new(Type::Variable(fresh)),
                    ),
                    SummaryConstructorFusionMutationForTest::NestedForallPayload => Type::Function(
                        Box::new(Type::Unit),
                        Box::new(Type::Forall(
                            vec![(fresh, Kind::Type)].into_boxed_slice(),
                            Box::new(Type::Variable(fresh)),
                        )),
                    ),
                    _ => unreachable!("the payload mutation cases are closed"),
                };
                let mirror = clone_type_with_budget(&invalid, &mut TypeWorkBudget::default())
                    .expect("the shallow test mutation should clone");
                let Some(payload) = constructor.payload.as_mut() else {
                    discard_type_iteratively(invalid);
                    discard_type_iteratively(mirror);
                    return false;
                };
                discard_type_iteratively(std::mem::replace(payload, invalid));
                discard_type_iteratively(std::mem::replace(domain.as_mut(), mirror));
                true
            }
            SummaryConstructorFusionMutationForTest::UnexpectedRequirement => {
                let Some(interface) = requirement_interface else {
                    return false;
                };
                constructor.scheme.requirements = vec![CheckedRequirement {
                    id: RequirementId::new(
                        crate::interface::RequirementOwner::Global(BinderId::resolved(
                            module,
                            u32::MAX,
                        )),
                        0,
                    ),
                    interface,
                    argument: Type::Unit,
                    origin: constructor.origin.clone(),
                    span: constructor.origin.primary_span(),
                }]
                .into_boxed_slice();
                true
            }
            SummaryConstructorFusionMutationForTest::ResultSpineTooShort
            | SummaryConstructorFusionMutationForTest::ResultSpineExtra
            | SummaryConstructorFusionMutationForTest::ResultArgumentSwap
            | SummaryConstructorFusionMutationForTest::ResultArgumentDuplicate => {
                if constructor.scheme.type_parameters.len() != 2 {
                    return false;
                }
                let first = constructor.scheme.type_parameters[0].0;
                let second = constructor.scheme.type_parameters[1].0;
                let owner = constructor.id.owner();
                let application = |arguments: &[TypeVariableId]| {
                    arguments
                        .iter()
                        .fold(Type::Nominal(owner), |function, identity| {
                            Type::Application(
                                Box::new(function),
                                Box::new(Type::Variable(*identity)),
                            )
                        })
                };
                let forged = match mutation {
                    SummaryConstructorFusionMutationForTest::ResultSpineTooShort => {
                        application(&[first])
                    }
                    SummaryConstructorFusionMutationForTest::ResultSpineExtra => Type::Application(
                        Box::new(application(&[first, second])),
                        Box::new(Type::Unit),
                    ),
                    SummaryConstructorFusionMutationForTest::ResultArgumentSwap => {
                        application(&[second, first])
                    }
                    SummaryConstructorFusionMutationForTest::ResultArgumentDuplicate => {
                        application(&[first, first])
                    }
                    _ => unreachable!("the result mutation cases are closed"),
                };
                discard_type_iteratively(std::mem::replace(result.as_mut(), forged));
                true
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn corrupt_hidden_diamond_fact_for_test(
        &mut self,
        mutation: SummaryHiddenDiamondMutationForTest,
    ) -> bool {
        let wrap_origin = |origin: &mut Origin| {
            *origin = Origin::Generated {
                cause: Box::new(origin.clone()),
                reason: crate::source::GeneratedReason::ConstantFolding,
            };
        };
        match mutation {
            SummaryHiddenDiamondMutationForTest::NominalOrigin => self
                .hidden_nominal_order
                .first()
                .and_then(|identity| self.hidden_nominals.get_mut(identity))
                .is_some_and(|nominal| {
                    wrap_origin(&mut nominal.origin);
                    true
                }),
            SummaryHiddenDiamondMutationForTest::NominalParameterOrigin => self
                .hidden_nominal_order
                .first()
                .and_then(|identity| self.hidden_nominals.get_mut(identity))
                .and_then(|nominal| nominal.parameters.first_mut())
                .is_some_and(|parameter| {
                    wrap_origin(&mut parameter.origin);
                    true
                }),
            SummaryHiddenDiamondMutationForTest::ConstructorOrigin => {
                let identity =
                    self.hidden_constructor_order
                        .iter()
                        .copied()
                        .find(|identity| {
                            self.nominals.values().any(|nominal| {
                                nominal.access == ExportedTypeAccess::Transparent
                                    && nominal.constructors.contains(identity)
                            }) || self.hidden_nominals.get(&identity.owner()).is_some_and(
                                |nominal| {
                                    nominal.access == ImportedTypeAccess::Transparent
                                        && nominal.constructors.contains(identity)
                                },
                            )
                        });
                identity
                    .and_then(|identity| self.hidden_constructors.get_mut(&identity))
                    .is_some_and(|constructor| {
                        wrap_origin(&mut constructor.origin);
                        true
                    })
            }
            SummaryHiddenDiamondMutationForTest::InterfaceOrigin => {
                self.hidden_interfaces.first_mut().is_some_and(|interface| {
                    wrap_origin(&mut interface.origin);
                    true
                })
            }
            SummaryHiddenDiamondMutationForTest::InterfaceParameterOrigin => {
                self.hidden_interfaces.first_mut().is_some_and(|interface| {
                    wrap_origin(&mut interface.parameter.origin);
                    true
                })
            }
            SummaryHiddenDiamondMutationForTest::InterfaceMethodOrigin => self
                .hidden_interfaces
                .first_mut()
                .and_then(|interface| interface.methods.first_mut())
                .is_some_and(|method| {
                    wrap_origin(&mut method.origin);
                    true
                }),
            SummaryHiddenDiamondMutationForTest::InterfaceMethodSpan => {
                let Some(interface) = self.hidden_interfaces.first_mut() else {
                    return false;
                };
                let replacement = interface.span;
                let Some(method) = interface.methods.first_mut() else {
                    return false;
                };
                method.span = replacement;
                true
            }
            SummaryHiddenDiamondMutationForTest::InterfaceMethodType => {
                let implementation_interfaces = self
                    .implementations
                    .iter()
                    .map(|implementation| implementation.fact.interface)
                    .collect::<HashSet<_>>();
                let Some(interface) = self
                    .hidden_interfaces
                    .iter_mut()
                    .find(|interface| !implementation_interfaces.contains(&interface.id))
                else {
                    return false;
                };
                let parameter = interface.parameter.id;
                let Some(method) = interface.methods.first_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    &mut method.value_type,
                    Type::Function(Box::new(Type::Variable(parameter)), Box::new(Type::Unit)),
                ));
                true
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn collide_first_method_with_first_term_for_test(&mut self) -> bool {
        let Some(term) = self.term_order.first().cloned() else {
            return false;
        };
        let Some(method_spelling) = self.method_name_order.first_mut() else {
            return false;
        };
        let mut method_names = self.method_names.clone();
        let Some(method) = method_names.remove(method_spelling) else {
            return false;
        };
        *method_spelling = term.clone();
        if method_names.insert(term, method).is_some() {
            return false;
        }
        drop(std::mem::replace(&mut self.method_names, method_names));
        true
    }

    #[cfg(test)]
    pub(crate) fn collide_first_interface_with_first_nominal_for_test(&mut self) -> bool {
        let Some(nominal) = self.nominal_order.first().cloned() else {
            return false;
        };
        let Some(interface_spelling) = self.interface_name_order.first_mut() else {
            return false;
        };
        let mut interface_names = self.interface_names.clone();
        let Some(interface) = interface_names.remove(interface_spelling) else {
            return false;
        };
        *interface_spelling = nominal.clone();
        if interface_names.insert(nominal, interface).is_some() {
            return false;
        }
        drop(std::mem::replace(
            &mut self.interface_names,
            interface_names,
        ));
        true
    }

    #[cfg(test)]
    pub(crate) fn duplicate_first_global_with_conflicting_scheme_for_test(
        &mut self,
        spelling: &str,
        value_type: Type,
    ) -> bool {
        if self.terms.contains_key(spelling) {
            discard_type_iteratively(value_type);
            return false;
        }
        let Some(source_spelling) = self.term_order.first() else {
            discard_type_iteratively(value_type);
            return false;
        };
        let Some(source) = self.terms.get(source_spelling) else {
            discard_type_iteratively(value_type);
            return false;
        };
        let mut type_work = TypeWorkBudget::unbounded();
        let Ok(mut scheme) = source.scheme.clone_with_budget(&mut type_work) else {
            discard_type_iteratively(value_type);
            return false;
        };
        discard_type_iteratively(std::mem::replace(&mut scheme.value_type, value_type));
        let exported = ExportedGlobal {
            binder: source.binder,
            scheme,
            origin: source.origin.clone(),
        };
        self.term_order.push(spelling.to_owned());
        if let Some(displaced) = self.terms.insert(spelling.to_owned(), exported) {
            drop(displaced.scheme);
            discard_origin_iteratively(displaced.origin);
            false
        } else {
            true
        }
    }

    #[cfg(test)]
    pub(crate) fn duplicate_first_nominal_with_conflicting_origin_for_test(
        &mut self,
        spelling: &str,
    ) -> bool {
        if self.nominals.contains_key(spelling) {
            return false;
        }
        let Some(source) = self
            .nominal_order
            .first()
            .and_then(|source_spelling| self.nominals.get(source_spelling))
        else {
            return false;
        };
        let mut type_work = TypeWorkBudget::unbounded();
        let Ok(parameters) =
            clone_resolved_type_variables_with_budget(&source.parameters, &mut type_work)
        else {
            return false;
        };
        let exported = ExportedType {
            id: source.id,
            parameter_count: source.parameter_count,
            constructor_count: source.constructor_count,
            parameters: parameters.into_boxed_slice(),
            constructors: source.constructors.to_vec().into_boxed_slice(),
            access: source.access,
            origin: Origin::Generated {
                cause: Box::new(source.origin.clone()),
                reason: crate::source::GeneratedReason::ConstantFolding,
            },
        };
        self.nominal_order.push(spelling.to_owned());
        if let Some(displaced) = self.nominals.insert(spelling.to_owned(), exported) {
            for parameter in displaced.parameters.into_vec() {
                discard_resolved_type_variable(parameter);
            }
            discard_origin_iteratively(displaced.origin);
            false
        } else {
            true
        }
    }

    #[cfg(test)]
    pub(crate) fn increment_first_constructor_count_for_test(&mut self) -> bool {
        if let Some(nominal) = self
            .nominal_order
            .first()
            .and_then(|spelling| self.nominals.get_mut(spelling))
        {
            let Some(count) = nominal.constructor_count.checked_add(1) else {
                return false;
            };
            nominal.constructor_count = count;
            return true;
        }
        if let Some(nominal) = self
            .hidden_nominal_order
            .first()
            .and_then(|identity| self.hidden_nominals.get_mut(identity))
        {
            let Some(count) = nominal.constructor_count.checked_add(1) else {
                return false;
            };
            nominal.constructor_count = count;
            return true;
        }
        false
    }

    #[cfg(test)]
    pub(crate) fn reuse_nominal_parameter_as_interface_owner_for_test(&mut self) -> bool {
        let Some(identity) = self
            .nominal_order
            .iter()
            .find_map(|spelling| self.nominals.get(spelling))
            .and_then(|nominal| nominal.parameters.first())
            .map(|parameter| parameter.id)
        else {
            return false;
        };
        let Some(interface) = self.interfaces.first_mut() else {
            return false;
        };
        interface.parameter.id = identity;
        true
    }

    #[cfg(test)]
    pub(crate) fn collide_first_implementation_method_with_global_for_test(&mut self) -> bool {
        let Some(binder) = self
            .term_order
            .first()
            .and_then(|spelling| self.terms.get(spelling))
            .map(|global| global.binder)
        else {
            return false;
        };
        let Some(method) = self
            .implementations
            .iter_mut()
            .find_map(|implementation| implementation.fact.methods.first_mut())
        else {
            return false;
        };
        method.binder = binder;
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_implementation_head_with_bare_parameter_for_test(
        &mut self,
    ) -> bool {
        let Some(fact) = self
            .implementations
            .iter_mut()
            .map(|implementation| &mut implementation.fact)
            .find(|fact| !fact.head_parameters.is_empty())
        else {
            return false;
        };
        let parameter = fact.head_parameters[0].id;
        discard_type_iteratively(std::mem::replace(
            &mut fact.argument,
            Type::Variable(parameter),
        ));
        let Some(method) = fact.methods.first_mut() else {
            return false;
        };
        discard_type_iteratively(std::mem::replace(
            &mut method.scheme.value_type,
            Type::Function(Box::new(Type::Variable(parameter)), Box::new(Type::Unit)),
        ));
        true
    }

    #[cfg(test)]
    pub(crate) fn replace_first_implementation_head_with_foreign_nominal_for_test(
        &mut self,
    ) -> bool {
        let Some(implementation_id) = self
            .implementations
            .iter()
            .map(|implementation| &implementation.fact)
            .find(|fact| fact.interface.module() != fact.id.module())
            .map(|fact| fact.id)
        else {
            return false;
        };
        let Some(foreign) = self
            .nominal_order
            .iter()
            .find_map(|spelling| self.nominals.get(spelling))
            .map(|nominal| nominal.id)
            .filter(|nominal| nominal.module() != implementation_id.module())
        else {
            return false;
        };
        let Some(fact) = self
            .implementations
            .iter_mut()
            .map(|implementation| &mut implementation.fact)
            .find(|fact| fact.id == implementation_id)
        else {
            return false;
        };
        discard_type_iteratively(std::mem::replace(
            &mut fact.argument,
            Type::Nominal(foreign),
        ));
        let Some(method) = fact.methods.first_mut() else {
            return false;
        };
        discard_type_iteratively(std::mem::replace(
            &mut method.scheme.value_type,
            Type::Function(Box::new(Type::Nominal(foreign)), Box::new(Type::Unit)),
        ));
        true
    }

    #[cfg(test)]
    pub(crate) fn remove_first_hidden_constructor_for_test(&mut self) -> bool {
        let Some(identity) = self.hidden_constructor_order.pop() else {
            return false;
        };
        if let Some(constructor) = self.hidden_constructors.remove(&identity) {
            constructor.discard_iteratively();
            true
        } else {
            false
        }
    }

    #[cfg(test)]
    pub(crate) fn remove_last_public_constructor_fact_preserving_family_for_test(
        &mut self,
    ) -> bool {
        let Some(spelling) = self.constructor_order.last() else {
            return false;
        };
        if let Some(constructor) = self.constructors.remove(spelling) {
            constructor.discard_iteratively();
            true
        } else {
            false
        }
    }

    #[cfg(test)]
    pub(crate) fn replace_first_implementation_prerequisite_with_head_for_test(&mut self) -> bool {
        let Some(implementation) = self
            .implementations
            .iter_mut()
            .find(|implementation| !implementation.fact.prerequisites.is_empty())
        else {
            return false;
        };
        let mut type_work = TypeWorkBudget::unbounded();
        let Ok(argument) = clone_type_with_budget(implementation.fact.argument(), &mut type_work)
        else {
            return false;
        };
        let argument = IterativeTypeOwner::new(argument);
        let method_argument = IterativeTypeOwner::new(
            clone_type_with_budget(implementation.fact.argument(), &mut type_work)
                .expect("an in-memory test prerequisite clone should fit"),
        );
        discard_type_iteratively(std::mem::replace(
            &mut implementation.fact.prerequisites[0].argument,
            argument.into_inner(),
        ));
        for method in &mut implementation.fact.methods {
            let Some(requirement) = method.scheme.requirements.first_mut() else {
                return false;
            };
            let replacement = clone_type_with_budget(&method_argument, &mut type_work)
                .expect("an in-memory test prerequisite clone should fit");
            discard_type_iteratively(std::mem::replace(&mut requirement.argument, replacement));
        }
        true
    }

    #[cfg(test)]
    pub(crate) fn test_fixture_with_access(
        module: ModuleId,
        terms: Vec<(&str, BinderId, Type, Origin)>,
        nominals: Vec<(&str, NominalTypeId, ExportedTypeAccess, Origin)>,
        constructors: Vec<(&str, ConstructorId, Option<Type>, Origin)>,
        unavailable: Vec<&str>,
        opaque_constructors: Vec<(&str, Origin)>,
        hidden_nominals: Vec<(&str, NominalTypeId, usize, bool, Origin)>,
    ) -> Self {
        let mut summary = Self::test_fixture(module, terms, nominals, constructors, unavailable);
        let opaque_owner = summary
            .nominal_order
            .iter()
            .find_map(|spelling| {
                summary
                    .nominals
                    .get(spelling)
                    .filter(|nominal| nominal.access == ExportedTypeAccess::Opaque)
            })
            .map(|nominal| nominal.id);
        if let Some(owner) = opaque_owner {
            let spelling = summary.nominal_order.iter().find_map(|spelling| {
                summary
                    .nominals
                    .get(spelling)
                    .is_some_and(|nominal| nominal.id == owner)
                    .then(|| spelling.clone())
            });
            if let Some(nominal) = spelling.and_then(|spelling| summary.nominals.get_mut(&spelling))
            {
                nominal.constructor_count = opaque_constructors.len().max(1);
            }
        }
        for (spelling, _) in &opaque_constructors {
            if let Some(withheld) = summary.withheld.get_mut(*spelling) {
                withheld.term = None;
                withheld.constructor.clear();
                withheld.constructor_positions.clear();
            }
            summary.withheld_order.retain(|entry| {
                entry.spelling != *spelling
                    || !matches!(
                        entry.namespace,
                        WithheldNamespace::Term | WithheldNamespace::Constructor
                    )
            });
        }
        for (spelling, origin) in opaque_constructors {
            let Some(owner) = opaque_owner else {
                continue;
            };
            let constructor_index = summary
                .withheld
                .entry(spelling.to_owned())
                .or_default()
                .insert_new(
                    WithheldNamespace::Constructor,
                    WithheldExport {
                        kind: WithheldExportKind::OpaqueConstructor,
                        owner: Some(owner),
                        origin: Some(origin),
                    },
                );
            summary.withheld_order.push(WithheldOrderEntry {
                spelling: spelling.to_owned(),
                namespace: WithheldNamespace::Constructor,
                owner: Some(owner),
                constructor_index,
            });
        }
        for (spelling, id, parameter_count, display_is_private, origin) in hidden_nominals {
            let constructor_origin = origin.clone();
            summary.hidden_nominal_order.push(id);
            summary.hidden_nominals.insert(
                id,
                ExportedHiddenType {
                    id,
                    parameter_count,
                    constructor_count: 1,
                    parameters: Vec::new().into_boxed_slice(),
                    constructors: Box::new([]),
                    access: ImportedTypeAccess::Hidden,
                    spelling: spelling.to_owned(),
                    display_is_private,
                    origin,
                },
            );
            if id.module() != module {
                continue;
            }
            let entries = summary.withheld.entry(spelling.to_owned()).or_default();
            let constructor_index = entries.insert_new(
                WithheldNamespace::Constructor,
                WithheldExport {
                    kind: WithheldExportKind::Private,
                    owner: Some(id),
                    origin: Some(constructor_origin),
                },
            );
            summary.withheld_order.push(WithheldOrderEntry {
                spelling: spelling.to_owned(),
                namespace: WithheldNamespace::Constructor,
                owner: Some(id),
                constructor_index,
            });
        }
        summary
    }
}

fn collect_nominal_identities(
    root: &Type,
    output: &mut HashSet<NominalTypeId>,
    budget: &mut TypeWorkBudget,
) -> Result<(), ()> {
    budget.charge(1)?;
    let mut work = Vec::new();
    work.try_reserve(1).map_err(|_| ())?;
    work.push(root);
    while let Some(ty) = work.pop() {
        match ty {
            Type::Nominal(id) => {
                retain_nominal_identity(*id, output, budget)?;
            }
            Type::Application(function, argument) => {
                budget.charge(2)?;
                work.try_reserve(2).map_err(|_| ())?;
                work.push(argument);
                work.push(function);
            }
            Type::Tuple(elements) => {
                budget.charge(elements.len())?;
                work.try_reserve(elements.len()).map_err(|_| ())?;
                work.extend(elements);
            }
            Type::Function(domain, codomain) => {
                budget.charge(2)?;
                work.try_reserve(2).map_err(|_| ())?;
                work.push(codomain);
                work.push(domain);
            }
            Type::Forall(_, body) => {
                budget.charge(1)?;
                work.try_reserve(1).map_err(|_| ())?;
                work.push(body);
            }
            Type::Int | Type::Bool | Type::Unit | Type::Variable(_) | Type::Inference(_) => {}
        }
    }
    Ok(())
}

fn retain_nominal_identity(
    identity: NominalTypeId,
    output: &mut HashSet<NominalTypeId>,
    budget: &mut TypeWorkBudget,
) -> Result<(), ()> {
    if output.contains(&identity) {
        return Ok(());
    }
    budget.charge(1)?;
    output.try_reserve(1).map_err(|_| ())?;
    output.insert(identity);
    Ok(())
}

fn collect_scheme_nominal_identities(
    scheme: &ConstrainedScheme,
    output: &mut HashSet<NominalTypeId>,
    budget: &mut TypeWorkBudget,
) -> Result<(), ()> {
    collect_nominal_identities(&scheme.value_type, output, budget)?;
    for requirement in &scheme.requirements {
        collect_nominal_identities(&requirement.argument, output, budget)?;
    }
    Ok(())
}

#[derive(Clone, Copy)]
pub(crate) struct ImportedNominalFactRef<'a> {
    pub(crate) id: NominalTypeId,
    pub(crate) parameter_count: usize,
    pub(crate) constructor_count: usize,
    pub(crate) parameters: &'a [ResolvedTypeVariable],
    pub(crate) constructors: &'a [ConstructorId],
    pub(crate) access: ImportedTypeAccess,
    pub(crate) display_spelling: Option<&'a str>,
    pub(crate) display_is_private: bool,
    pub(crate) origin: &'a Origin,
}

impl Drop for ExportSummary {
    fn drop(&mut self) {
        for (_, exported) in self.terms.drain() {
            drop(exported.scheme);
            discard_origin_iteratively(exported.origin);
        }
        self.term_order.clear();
        for (_, exported) in self.nominals.drain() {
            for parameter in exported.parameters.into_vec() {
                discard_origin_iteratively(parameter.origin);
            }
            discard_origin_iteratively(exported.origin);
        }
        self.nominal_order.clear();
        self.nominal_names_by_id.clear();
        for (_, exported) in self.constructors.drain() {
            drop(exported.scheme);
            if let Some(payload) = exported.payload {
                discard_type_iteratively(payload);
            }
            discard_origin_iteratively(exported.origin);
        }
        self.constructor_order.clear();
        self.constructor_names_by_id.clear();
        for (_, exported) in self.hidden_constructors.drain() {
            drop(exported.scheme);
            if let Some(payload) = exported.payload {
                discard_type_iteratively(payload);
            }
            discard_origin_iteratively(exported.origin);
        }
        self.hidden_constructor_order.clear();
        self.interface_names.clear();
        self.interface_name_order.clear();
        self.method_names.clear();
        self.method_name_order.clear();
        for fact in self.interfaces.drain(..) {
            drop(fact);
        }
        self.interface_positions.clear();
        for fact in self.hidden_interfaces.drain(..) {
            drop(fact);
        }
        for fact in self.implementations.drain(..) {
            drop(fact);
        }
        self.implementation_positions.clear();
        for (_, exported) in self.hidden_nominals.drain() {
            for parameter in exported.parameters.into_vec() {
                discard_origin_iteratively(parameter.origin);
            }
            discard_origin_iteratively(exported.origin);
        }
        self.hidden_nominal_order.clear();
        for (_, withheld) in self.withheld.drain() {
            for withheld in withheld.into_values() {
                if let Some(origin) = withheld.origin {
                    discard_origin_iteratively(origin);
                }
            }
        }
        self.withheld_order.clear();
    }
}

/// Ordered resolved type-variable identities owned by one non-empty global scheme.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ResolvedGlobalParameterRow {
    owner: BinderId,
    parameters: Box<[TypeVariableId]>,
}

impl ResolvedGlobalParameterRow {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) const fn owner(&self) -> BinderId {
        self.owner
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn parameters(&self) -> &[TypeVariableId] {
        &self.parameters
    }
}

/// Immutable resolved metadata for one source file.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResolvedRegistry {
    nominals: Box<[ResolvedNominalType]>,
    constructors: Box<[ResolvedConstructor]>,
    nominal_positions: HashMap<NominalTypeId, usize>,
    constructor_positions: HashMap<ConstructorId, usize>,
    nominal_parameters: HashMap<NominalTypeId, Box<[ResolvedTypeVariable]>>,
    type_variables: HashMap<TypeVariableId, ResolvedTypeVariable>,
    global_parameter_rows: Box<[ResolvedGlobalParameterRow]>,
    global_parameter_positions: HashMap<BinderId, usize>,
    abstract_nominal_names: HashMap<NominalTypeId, String>,
    abstract_nominal_kinds: HashMap<NominalTypeId, NonMaterializedNominalKindFact>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NonMaterializedNominalKindFact {
    kind: Kind,
    origin: Span,
}

pub(crate) enum CanonicalNominalKind<'a> {
    Parameters {
        parameters: &'a [ResolvedTypeVariable],
        origin: Span,
    },
    Frozen {
        kind: &'a Kind,
        origin: Span,
    },
}

struct ResolvedConstructorBuffer(Vec<ResolvedConstructor>);

struct ResolvedNominalBuffer(Vec<ResolvedNominalType>);

impl ResolvedNominalBuffer {
    fn into_vec(mut self) -> Vec<ResolvedNominalType> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedNominalBuffer {
    fn drop(&mut self) {
        for nominal in self.0.drain(..) {
            discard_origin_iteratively(nominal.origin);
        }
    }
}

struct ResolvedTypeVariableBuffer(Vec<ResolvedTypeVariable>);

impl ResolvedTypeVariableBuffer {
    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn push(&mut self, parameter: ResolvedTypeVariable) {
        self.0.push(parameter);
    }

    fn iter(&self) -> std::slice::Iter<'_, ResolvedTypeVariable> {
        self.0.iter()
    }

    fn into_vec(mut self) -> Vec<ResolvedTypeVariable> {
        std::mem::take(&mut self.0)
    }

    fn into_boxed_slice(mut self) -> Box<[ResolvedTypeVariable]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for ResolvedTypeVariableBuffer {
    fn drop(&mut self) {
        for parameter in self.0.drain(..) {
            discard_resolved_type_variable(parameter);
        }
    }
}

struct ResolvedNominalParameterBuffer(Vec<(NominalTypeId, Box<[ResolvedTypeVariable]>)>);

struct ResolvedNominalParameterVecBuffer(Vec<(NominalTypeId, Vec<ResolvedTypeVariable>)>);

impl ResolvedNominalParameterBuffer {
    fn into_vec(mut self) -> Vec<(NominalTypeId, Box<[ResolvedTypeVariable]>)> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedNominalParameterBuffer {
    fn drop(&mut self) {
        for (_, parameters) in self.0.drain(..) {
            discard_resolved_type_variables(parameters);
        }
    }
}

impl ResolvedNominalParameterVecBuffer {
    fn into_vec(mut self) -> Vec<(NominalTypeId, Vec<ResolvedTypeVariable>)> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedNominalParameterVecBuffer {
    fn drop(&mut self) {
        for (_, parameters) in self.0.drain(..) {
            for parameter in parameters {
                discard_resolved_type_variable(parameter);
            }
        }
    }
}

#[derive(Default)]
struct CombinedRegistryCounts {
    modules: usize,
    nominals: usize,
    family_entries: usize,
    constructors: usize,
    nominal_parameters: usize,
    interfaces: usize,
    method_parameters: usize,
    schemes: usize,
    global_rows: usize,
    global_parameters: usize,
    implementations: usize,
    implementation_parameters: usize,
    type_variables: usize,
    fixed_constraint_work: usize,
    retention_type_work: usize,
}

struct CombinedRegistryBuilder {
    nominals: ResolvedNominalBuffer,
    constructors: ResolvedConstructorBuffer,
    nominal_positions: HashMap<NominalTypeId, usize>,
    constructor_positions: HashMap<ConstructorId, usize>,
    parameter_rows: ResolvedNominalParameterBuffer,
    canonical_variables: ResolvedTypeVariableBuffer,
    nominal_parameters: HashMap<NominalTypeId, Box<[ResolvedTypeVariable]>>,
    type_variables: HashMap<TypeVariableId, ResolvedTypeVariable>,
    global_parameter_rows: Vec<ResolvedGlobalParameterRow>,
    global_parameter_positions: HashMap<BinderId, usize>,
}

impl CombinedRegistryBuilder {
    fn with_counts(counts: &CombinedRegistryCounts) -> Result<Self, ResolvedBuildFailure> {
        let mut builder = Self {
            nominals: ResolvedNominalBuffer(Vec::new()),
            constructors: ResolvedConstructorBuffer(Vec::new()),
            nominal_positions: HashMap::new(),
            constructor_positions: HashMap::new(),
            parameter_rows: ResolvedNominalParameterBuffer(Vec::new()),
            canonical_variables: ResolvedTypeVariableBuffer(Vec::new()),
            nominal_parameters: HashMap::new(),
            type_variables: HashMap::new(),
            global_parameter_rows: Vec::new(),
            global_parameter_positions: HashMap::new(),
        };
        builder
            .nominals
            .0
            .try_reserve_exact(counts.nominals)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        builder
            .constructors
            .0
            .try_reserve_exact(counts.constructors)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        builder
            .nominal_positions
            .try_reserve(counts.nominals)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        builder
            .constructor_positions
            .try_reserve(counts.constructors)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        builder
            .parameter_rows
            .0
            .try_reserve_exact(counts.nominals)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        builder
            .canonical_variables
            .0
            .try_reserve_exact(counts.type_variables)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        builder
            .nominal_parameters
            .try_reserve(counts.nominals)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        builder
            .type_variables
            .try_reserve(counts.type_variables)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        builder
            .global_parameter_rows
            .try_reserve_exact(counts.global_rows)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        builder
            .global_parameter_positions
            .try_reserve(counts.global_rows)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        Ok(builder)
    }

    fn retain_global_parameter_row(
        &mut self,
        _validated: &ValidatedCheckedRegistries<'_>,
        owner: BinderId,
        parameters: &[(TypeVariableId, Kind)],
    ) -> Result<(), ResolvedBuildFailure> {
        debug_assert!(owner.module().is_some());
        debug_assert!(!parameters.is_empty());
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(parameters.len())
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        retained.extend(parameters.iter().map(|(identity, _)| *identity));
        let retained = retained.into_boxed_slice();

        let position = self.global_parameter_rows.len();
        let displaced = self.global_parameter_positions.insert(owner, position);
        debug_assert!(displaced.is_none());
        self.global_parameter_rows.push(ResolvedGlobalParameterRow {
            owner,
            parameters: retained,
        });
        Ok(())
    }

    fn install_parameter_row(
        &mut self,
        owner: NominalTypeId,
        parameters: Box<[ResolvedTypeVariable]>,
    ) {
        if let Some(displaced) = self.nominal_parameters.insert(owner, parameters) {
            discard_resolved_type_variables(displaced);
        }
    }

    fn install_canonical_variable(&mut self, parameter: ResolvedTypeVariable) {
        if let Some(displaced) = self.type_variables.insert(parameter.id, parameter) {
            discard_resolved_type_variable(displaced);
        }
    }

    fn finish(mut self) -> ResolvedRegistry {
        let parameter_rows = std::mem::replace(
            &mut self.parameter_rows,
            ResolvedNominalParameterBuffer(Vec::new()),
        );
        for (owner, parameters) in parameter_rows.into_vec() {
            self.install_parameter_row(owner, parameters);
        }
        let canonical_variables = std::mem::replace(
            &mut self.canonical_variables,
            ResolvedTypeVariableBuffer(Vec::new()),
        );
        for parameter in canonical_variables.into_vec() {
            self.install_canonical_variable(parameter);
        }
        let nominals =
            std::mem::replace(&mut self.nominals, ResolvedNominalBuffer(Vec::new())).into_vec();
        let constructors = std::mem::replace(
            &mut self.constructors,
            ResolvedConstructorBuffer(Vec::new()),
        )
        .into_vec();
        ResolvedRegistry {
            nominals: nominals.into_boxed_slice(),
            constructors: constructors.into_boxed_slice(),
            nominal_positions: std::mem::take(&mut self.nominal_positions),
            constructor_positions: std::mem::take(&mut self.constructor_positions),
            nominal_parameters: std::mem::take(&mut self.nominal_parameters),
            type_variables: std::mem::take(&mut self.type_variables),
            global_parameter_rows: std::mem::take(&mut self.global_parameter_rows)
                .into_boxed_slice(),
            global_parameter_positions: std::mem::take(&mut self.global_parameter_positions),
            abstract_nominal_names: HashMap::new(),
            abstract_nominal_kinds: HashMap::new(),
        }
    }
}

impl Drop for CombinedRegistryBuilder {
    fn drop(&mut self) {
        for parameters in self
            .nominal_parameters
            .drain()
            .map(|(_, parameters)| parameters)
        {
            discard_resolved_type_variables(parameters);
        }
        for parameter in self.type_variables.drain().map(|(_, parameter)| parameter) {
            discard_resolved_type_variable(parameter);
        }
    }
}

fn checked_accumulate(total: &mut usize, work: usize) -> Result<(), ResolvedBuildFailure> {
    *total = total
        .checked_add(work)
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    Ok(())
}

fn type_accumulate(total: &mut usize, work: usize) -> Result<(), ResolvedBuildFailure> {
    *total = total
        .checked_add(work)
        .ok_or(ResolvedBuildFailure::TypeResource)?;
    Ok(())
}

fn retained_type_variable_work(
    parameter: &ResolvedTypeVariable,
) -> Result<usize, ResolvedBuildFailure> {
    retained_kind_record_work(&parameter.kind)
}

fn retained_kind_record_work(kind: &Kind) -> Result<usize, ResolvedBuildFailure> {
    let mut work = 1usize;
    charge_kind_with_charge(kind, || {
        work = work.checked_add(1).ok_or(())?;
        Ok(())
    })
    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
    Ok(work)
}

fn checked_registry_counts(
    modules: &[CheckedModule],
) -> Result<CombinedRegistryCounts, ResolvedBuildFailure> {
    let mut counts = CombinedRegistryCounts {
        modules: modules.len(),
        ..CombinedRegistryCounts::default()
    };
    for checked in modules {
        let registry = checked.registry();
        checked_accumulate(&mut counts.nominals, registry.nominals.len())?;
        checked_accumulate(&mut counts.constructors, registry.constructors.len())?;
        checked_accumulate(&mut counts.interfaces, checked.interface_facts().len())?;
        checked_accumulate(&mut counts.schemes, checked.schemes().len())?;
        checked_accumulate(
            &mut counts.implementations,
            checked.implementation_facts().len(),
        )?;
        for nominal in registry.nominals() {
            checked_accumulate(&mut counts.family_entries, nominal.constructors.len())?;
            if let Some(parameters) = registry.nominal_parameters.get(&nominal.id) {
                checked_accumulate(&mut counts.nominal_parameters, parameters.len())?;
                for parameter in parameters {
                    type_accumulate(
                        &mut counts.retention_type_work,
                        retained_type_variable_work(parameter)?,
                    )?;
                }
            }
        }
        for constructor in registry.constructors() {
            if let Some(payload) = &constructor.payload {
                let mut payload_work = TypeWorkBudget::unbounded();
                charge_type_cells(payload, &mut payload_work)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
                type_accumulate(&mut counts.retention_type_work, payload_work.used())?;
            }
        }
        for scheme in checked.schemes() {
            if !scheme.scheme.type_parameters.is_empty() {
                checked_accumulate(&mut counts.global_rows, 1)?;
            }
            checked_accumulate(
                &mut counts.global_parameters,
                scheme.scheme.type_parameters.len(),
            )?;
        }
        for implementation in checked.implementation_facts() {
            checked_accumulate(
                &mut counts.implementation_parameters,
                implementation.head_parameters.len(),
            )?;
        }
        for interface in checked.interface_facts() {
            for method in &interface.methods {
                checked_accumulate(
                    &mut counts.method_parameters,
                    method.type_parameters().len(),
                )?;
            }
        }
        // Retention clones canonical records from the registry map, not from
        // the independently retained interface, global, or implementation
        // mirrors. Price those exact sources so deferred mirror rejection
        // cannot make a deeper canonical Kind bypass the aggregate precharge.
        for parameter in registry.type_variables.values() {
            type_accumulate(
                &mut counts.retention_type_work,
                retained_type_variable_work(parameter)?,
            )?;
        }
    }
    counts.type_variables = counts
        .nominal_parameters
        .checked_add(counts.interfaces)
        .and_then(|count| count.checked_add(counts.method_parameters))
        .and_then(|count| count.checked_add(counts.global_parameters))
        .and_then(|count| count.checked_add(counts.implementation_parameters))
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    let builder_storage = counts
        .family_entries
        .checked_add(
            counts
                .nominals
                .checked_mul(4)
                .ok_or(ResolvedBuildFailure::TypeResource)?,
        )
        .and_then(|work| {
            counts
                .constructors
                .checked_mul(2)
                .and_then(|constructors| work.checked_add(constructors))
        })
        .and_then(|work| work.checked_add(counts.type_variables))
        .and_then(|work| {
            counts
                .global_rows
                .checked_mul(2)
                .and_then(|global_rows| work.checked_add(global_rows))
        })
        .and_then(|work| work.checked_add(counts.global_parameters))
        .ok_or(ResolvedBuildFailure::TypeResource)?;
    type_accumulate(&mut counts.retention_type_work, builder_storage)?;
    let deterministic_visits = counts
        .modules
        .checked_add(
            counts
                .nominals
                .checked_mul(2)
                .ok_or(ResolvedBuildFailure::ConstraintResource)?,
        )
        .and_then(|work| work.checked_add(counts.family_entries))
        .and_then(|work| work.checked_add(counts.constructors))
        .and_then(|work| work.checked_add(counts.interfaces))
        .and_then(|work| work.checked_add(counts.schemes))
        .and_then(|work| work.checked_add(counts.implementations))
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    let uniqueness = counts
        .modules
        .checked_add(counts.nominals)
        .and_then(|work| work.checked_add(counts.family_entries))
        .and_then(|work| work.checked_add(counts.constructors))
        .and_then(|work| work.checked_add(counts.global_rows))
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    counts.fixed_constraint_work = deterministic_visits
        .checked_add(uniqueness)
        .ok_or(ResolvedBuildFailure::ConstraintResource)?;
    Ok(counts)
}

/// Borrowed authority that the checked registry set passed semantic validation.
struct ValidatedCheckedRegistries<'a> {
    modules: &'a [CheckedModule],
}

impl ValidatedCheckedRegistries<'_> {
    #[cfg(test)]
    fn modules(&self) -> &[CheckedModule] {
        self.modules
    }
}

fn validate_checked_registries<'a>(
    modules: &'a [CheckedModule],
    counts: &CombinedRegistryCounts,
    constraint_work: &mut crate::interface::InterfaceConstraintBudget,
) -> Result<ValidatedCheckedRegistries<'a>, ResolvedBuildFailure> {
    constraint_work
        .charge(counts.fixed_constraint_work)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    let mut module_ids = HashSet::new();
    let mut nominal_ids = HashSet::new();
    let mut family_ids = HashSet::new();
    let mut constructor_ids = HashSet::new();
    let mut global_owners = HashSet::new();
    module_ids
        .try_reserve(counts.modules)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    nominal_ids
        .try_reserve(counts.nominals)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    family_ids
        .try_reserve(counts.family_entries)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    constructor_ids
        .try_reserve(counts.constructors)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    global_owners
        .try_reserve(counts.global_rows)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;

    for checked in modules {
        let module = checked.module();
        let registry = checked.registry();
        if !module_ids.insert(module)
            || !registry.abstract_nominal_names.is_empty()
            || !registry.abstract_nominal_kinds.is_empty()
            || registry.nominal_positions.len() != registry.nominals.len()
            || registry.constructor_positions.len() != registry.constructors.len()
            || registry.nominal_parameters.len() != registry.nominals.len()
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        let mut local_variable_count = 0usize;
        for (position, nominal) in registry.nominals().iter().enumerate() {
            if nominal.id.module() != module
                || !nominal_ids.insert(nominal.id)
                || registry.nominal_positions.get(&nominal.id) != Some(&position)
                || nominal.constructors.is_empty()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            for (ordinal, constructor) in nominal.constructors.iter().enumerate() {
                if constructor.owner() != nominal.id
                    || usize::try_from(constructor.constructor()) != Ok(ordinal)
                    || !family_ids.insert(*constructor)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
            let parameters = registry
                .nominal_parameters
                .get(&nominal.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            local_variable_count = local_variable_count
                .checked_add(parameters.len())
                .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        }
        for (position, constructor) in registry.constructors().iter().enumerate() {
            let ordinal = usize::try_from(constructor.id.constructor())
                .map_err(|_| ResolvedBuildFailure::InvalidState)?;
            let owner = registry
                .nominal(constructor.owner)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            if constructor.owner != constructor.id.owner()
                || constructor.owner.module() != module
                || !constructor_ids.insert(constructor.id)
                || registry.constructor_positions.get(&constructor.id) != Some(&position)
                || owner.constructors.get(ordinal) != Some(&constructor.id)
                || !family_ids.contains(&constructor.id)
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }
        if family_ids.len() != constructor_ids.len() {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        for interface in checked.interface_facts() {
            local_variable_count = local_variable_count
                .checked_add(1)
                .ok_or(ResolvedBuildFailure::ConstraintResource)?;
            for method in &interface.methods {
                local_variable_count = local_variable_count
                    .checked_add(method.type_parameters().len())
                    .ok_or(ResolvedBuildFailure::ConstraintResource)?;
            }
            if interface.id.module() != module {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }
        for scheme in checked.schemes() {
            if scheme.binder.module() != Some(module)
                || (!scheme.scheme.type_parameters.is_empty()
                    && !global_owners.insert(scheme.binder))
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            local_variable_count = local_variable_count
                .checked_add(scheme.scheme.type_parameters.len())
                .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        }
        for implementation in checked.implementation_facts() {
            if implementation.id.module() != module {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            local_variable_count = local_variable_count
                .checked_add(implementation.head_parameters.len())
                .ok_or(ResolvedBuildFailure::ConstraintResource)?;
        }
        if local_variable_count != registry.type_variables.len() {
            return Err(ResolvedBuildFailure::InvalidState);
        }
    }
    if module_ids.len() != counts.modules
        || nominal_ids.len() != counts.nominals
        || family_ids.len() != counts.family_entries
        || constructor_ids.len() != counts.constructors
        || global_owners.len() != counts.global_rows
    {
        return Err(ResolvedBuildFailure::InvalidState);
    }

    constraint_work
        .charge(counts.type_variables)
        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
    let mut type_variable_ids = HashSet::new();
    type_variable_ids
        .try_reserve(counts.type_variables)
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    for checked in modules {
        let registry = checked.registry();
        let local_variable_start = type_variable_ids.len();
        for nominal in registry.nominals() {
            let parameters = registry
                .nominal_parameters
                .get(&nominal.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let mut previous = None;
            for parameter in parameters {
                constraint_work
                    .charge(1)
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                if parameter.id.module() != Some(checked.module())
                    || previous.is_some_and(|previous| parameter.id.local() <= previous)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                previous = Some(parameter.id.local());
                if !type_variable_ids.insert(parameter.id) {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                let canonical = registry
                    .type_variables
                    .get(&parameter.id)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                if !same_checker_type_variable_after_base_charge(
                    canonical,
                    parameter,
                    constraint_work,
                )? {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
        }
        for interface in checked.interface_facts() {
            let parameter = &interface.parameter;
            if parameter.id.module() != Some(checked.module())
                || !type_variable_ids.insert(parameter.id)
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            let canonical = registry
                .type_variables
                .get(&parameter.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            if canonical.id != parameter.id {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            // The consuming linked-evidence validator authenticates the
            // interface carrier's complete spelling, Origin, and Kind mirror
            // against this registry before it constructs Kind environments.
            // Combination owns only canonical existence and cross-owner
            // uniqueness for that independently retained carrier.
            for method in &interface.methods {
                let mut previous = None;
                for parameter in method.type_parameters() {
                    constraint_work
                        .charge(1)
                        .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                    if parameter.id.module() != Some(checked.module())
                        || previous.is_some_and(|previous| parameter.id.local() <= previous)
                        || !type_variable_ids.insert(parameter.id)
                    {
                        return Err(ResolvedBuildFailure::InvalidState);
                    }
                    previous = Some(parameter.id.local());
                    let canonical = registry
                        .type_variables
                        .get(&parameter.id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    if !same_checker_type_variable_after_base_charge(
                        canonical,
                        parameter,
                        constraint_work,
                    )? {
                        return Err(ResolvedBuildFailure::InvalidState);
                    }
                }
            }
        }
        for scheme in checked.schemes() {
            let mut previous = None;
            for (identity, kind) in &scheme.scheme.type_parameters {
                constraint_work
                    .charge(1)
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                if identity.module() != Some(checked.module())
                    || previous.is_some_and(|previous| identity.local() <= previous)
                    || !type_variable_ids.insert(*identity)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                previous = Some(identity.local());
                let canonical = registry
                    .type_variables
                    .get(identity)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                if canonical.id != *identity
                    || !same_kind_with_constraint_budget(&canonical.kind, kind, constraint_work)?
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
        }
        for implementation in checked.implementation_facts() {
            let mut previous = None;
            for parameter in &implementation.head_parameters {
                constraint_work
                    .charge(1)
                    .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
                if parameter.id.module() != Some(checked.module())
                    || previous.is_some_and(|previous| parameter.id.local() <= previous)
                    || !type_variable_ids.insert(parameter.id)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                previous = Some(parameter.id.local());
                let canonical = registry
                    .type_variables
                    .get(&parameter.id)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                if !same_checker_type_variable_after_base_charge(
                    canonical,
                    parameter,
                    constraint_work,
                )? {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
        }
        let local_variable_count = type_variable_ids
            .len()
            .checked_sub(local_variable_start)
            .ok_or(ResolvedBuildFailure::InvalidState)?;
        if local_variable_count != registry.type_variables.len() {
            return Err(ResolvedBuildFailure::InvalidState);
        }
    }
    if type_variable_ids.len() != counts.type_variables {
        return Err(ResolvedBuildFailure::InvalidState);
    }
    Ok(ValidatedCheckedRegistries { modules })
}

fn try_clone_string(value: &str) -> Result<String, ResolvedBuildFailure> {
    let mut cloned = String::new();
    cloned
        .try_reserve_exact(value.len())
        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
    cloned.push_str(value);
    Ok(cloned)
}

fn clone_constructor_ids_for_combined_registry(
    constructors: &[ConstructorId],
) -> Result<Box<[ConstructorId]>, ResolvedBuildFailure> {
    let mut cloned = Vec::new();
    cloned
        .try_reserve_exact(constructors.len())
        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
    cloned.extend_from_slice(constructors);
    Ok(cloned.into_boxed_slice())
}

fn clone_type_variable_after_combined_precharge(
    parameter: &ResolvedTypeVariable,
) -> Result<ResolvedTypeVariable, ResolvedBuildFailure> {
    let spelling = try_clone_string(&parameter.spelling)?;
    let mut unbounded = TypeWorkBudget::unbounded();
    let kind = clone_kind_with_budget(&parameter.kind, &mut unbounded)
        .map_err(|()| ResolvedBuildFailure::TypeResource)?;
    Ok(ResolvedTypeVariable {
        id: parameter.id,
        spelling,
        kind,
        origin: parameter.origin.clone(),
    })
}

fn clone_type_variable_row_after_combined_precharge(
    parameters: &[ResolvedTypeVariable],
) -> Result<Box<[ResolvedTypeVariable]>, ResolvedBuildFailure> {
    let mut cloned = ResolvedTypeVariableBuffer(Vec::new());
    cloned
        .0
        .try_reserve_exact(parameters.len())
        .map_err(|_| ResolvedBuildFailure::TypeResource)?;
    for parameter in parameters {
        cloned
            .0
            .push(clone_type_variable_after_combined_precharge(parameter)?);
    }
    Ok(cloned.into_vec().into_boxed_slice())
}

fn retain_checked_registries(
    validated: ValidatedCheckedRegistries<'_>,
    mut builder: CombinedRegistryBuilder,
) -> Result<ResolvedRegistry, ResolvedBuildFailure> {
    for checked in validated.modules {
        let registry = checked.registry();
        for nominal in registry.nominals() {
            let position = builder.nominals.0.len();
            let retained = ResolvedNominalType {
                id: nominal.id,
                spelling: try_clone_string(&nominal.spelling)?,
                constructors: clone_constructor_ids_for_combined_registry(&nominal.constructors)?,
                origin: nominal.origin.clone(),
            };
            let displaced = builder.nominal_positions.insert(nominal.id, position);
            debug_assert!(displaced.is_none());
            builder.nominals.0.push(retained);

            let parameters = registry
                .nominal_parameters
                .get(&nominal.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            builder.parameter_rows.0.push((
                nominal.id,
                clone_type_variable_row_after_combined_precharge(parameters)?,
            ));
            for parameter in parameters {
                let canonical = registry
                    .type_variables
                    .get(&parameter.id)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                builder
                    .canonical_variables
                    .0
                    .push(clone_type_variable_after_combined_precharge(canonical)?);
            }
        }
        for constructor in registry.constructors() {
            let position = builder.constructors.0.len();
            let spelling = try_clone_string(&constructor.spelling)?;
            let mut unbounded = TypeWorkBudget::unbounded();
            let payload = constructor
                .payload
                .as_ref()
                .map(|payload| clone_type_with_budget(payload, &mut unbounded))
                .transpose()
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            let retained = ResolvedConstructor {
                id: constructor.id,
                owner: constructor.owner,
                spelling,
                payload,
                origin: constructor.origin.clone(),
            };
            let displaced = builder
                .constructor_positions
                .insert(constructor.id, position);
            debug_assert!(displaced.is_none());
            builder.constructors.0.push(retained);
        }
        for interface in checked.interface_facts() {
            let canonical = registry
                .type_variables
                .get(&interface.parameter.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            builder
                .canonical_variables
                .0
                .push(clone_type_variable_after_combined_precharge(canonical)?);
            for method in &interface.methods {
                for parameter in method.type_parameters() {
                    let canonical = registry
                        .type_variables
                        .get(&parameter.id)
                        .ok_or(ResolvedBuildFailure::InvalidState)?;
                    builder
                        .canonical_variables
                        .0
                        .push(clone_type_variable_after_combined_precharge(canonical)?);
                }
            }
        }
        for scheme in checked.schemes() {
            if !scheme.scheme.type_parameters.is_empty() {
                builder.retain_global_parameter_row(
                    &validated,
                    scheme.binder,
                    &scheme.scheme.type_parameters,
                )?;
            }
            for (identity, _) in &scheme.scheme.type_parameters {
                let canonical = registry
                    .type_variables
                    .get(identity)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                builder
                    .canonical_variables
                    .0
                    .push(clone_type_variable_after_combined_precharge(canonical)?);
            }
        }
        for implementation in checked.implementation_facts() {
            for parameter in &implementation.head_parameters {
                let canonical = registry
                    .type_variables
                    .get(&parameter.id)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                builder
                    .canonical_variables
                    .0
                    .push(clone_type_variable_after_combined_precharge(canonical)?);
            }
        }
    }
    Ok(builder.finish())
}

impl ResolvedConstructorBuffer {
    fn into_vec(mut self) -> Vec<ResolvedConstructor> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedConstructorBuffer {
    fn drop(&mut self) {
        for constructor in self.0.drain(..) {
            if let Some(payload) = constructor.payload {
                discard_type_iteratively(payload);
            }
            discard_origin_iteratively(constructor.origin);
        }
    }
}

impl ResolvedRegistry {
    /// Constructs one closed registry after two-pass resolution.
    #[must_use]
    pub fn new(nominals: Vec<ResolvedNominalType>, constructors: Vec<ResolvedConstructor>) -> Self {
        let nominal_positions = nominals
            .iter()
            .enumerate()
            .map(|(index, nominal)| (nominal.id, index))
            .collect();
        let constructor_positions = constructors
            .iter()
            .enumerate()
            .map(|(index, constructor)| (constructor.id, index))
            .collect();
        Self {
            nominals: nominals.into_boxed_slice(),
            constructors: constructors.into_boxed_slice(),
            nominal_positions,
            constructor_positions,
            nominal_parameters: HashMap::new(),
            type_variables: HashMap::new(),
            global_parameter_rows: Box::new([]),
            global_parameter_positions: HashMap::new(),
            abstract_nominal_names: HashMap::new(),
            abstract_nominal_kinds: HashMap::new(),
        }
    }

    /// Builds the semantic registry view needed while checking one module.
    ///
    /// Only transparent imported nominals are materialized. Hidden and opaque
    /// identities remain abstract rather than masquerading as empty types.
    pub(crate) fn checker_view(
        &self,
        imported: &ImportedFacts,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        for fact in imported.nominals() {
            budget
                .charge(
                    fact.constructors
                        .len()
                        .checked_add(1)
                        .ok_or(ResolvedBuildFailure::TypeResource)?,
                )
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            if !imported_nominal_family_is_valid(fact) {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }
        let materialized_import_count = imported
            .nominals()
            .filter(|fact| fact.access == ImportedTypeAccess::Transparent)
            .count();
        let materialized_nominal_count = self
            .nominals
            .len()
            .checked_add(materialized_import_count)
            .ok_or(ResolvedBuildFailure::TypeResource)?;
        let mut nominals = ResolvedNominalBuffer(Vec::new());
        nominals
            .0
            .try_reserve_exact(materialized_nominal_count)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for nominal in &self.nominals {
            nominals.0.push(nominal.clone());
        }
        let constructor_capacity = self
            .constructors
            .len()
            .checked_add(imported.constructors.len())
            .ok_or(ResolvedBuildFailure::TypeResource)?;
        let mut constructors = ResolvedConstructorBuffer(Vec::new());
        constructors
            .0
            .try_reserve_exact(constructor_capacity)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for constructor in &self.constructors {
            constructors.0.push(ResolvedConstructor {
                id: constructor.id,
                owner: constructor.owner,
                spelling: constructor.spelling.clone(),
                payload: constructor
                    .payload
                    .as_ref()
                    .map(|payload| clone_type_with_budget(payload, budget))
                    .transpose()
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                origin: constructor.origin.clone(),
            });
        }
        let mut parameters = ResolvedNominalParameterVecBuffer(Vec::new());
        parameters
            .0
            .try_reserve_exact(materialized_nominal_count)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for nominal in &self.nominals {
            let owner_parameters = self
                .nominal_parameters
                .get(&nominal.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            parameters.0.push((
                nominal.id,
                clone_resolved_type_variables_with_budget(owner_parameters, budget)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?,
            ));
        }

        for fact in imported.nominals() {
            if fact.access != ImportedTypeAccess::Transparent {
                continue;
            }
            if fact.parameters.len() != fact.parameter_count
                || nominals.0.iter().any(|nominal| nominal.id == fact.id)
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            for id in &fact.constructors {
                let constructor = imported
                    .constructor(*id)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                if constructor.id.owner() != fact.id {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                constructors.0.push(ResolvedConstructor {
                    id: constructor.id,
                    owner: fact.id,
                    spelling: constructor.spelling.clone(),
                    payload: constructor
                        .payload
                        .as_ref()
                        .map(|payload| clone_type_with_budget(payload, budget))
                        .transpose()
                        .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                    origin: constructor.origin.clone(),
                });
            }
            nominals.0.push(ResolvedNominalType {
                id: fact.id,
                spelling: fact
                    .display_spelling
                    .clone()
                    .unwrap_or_else(|| "<imported>".to_owned()),
                constructors: fact.constructors.clone(),
                origin: fact.origin.clone(),
            });
            parameters.0.push((
                fact.id,
                clone_resolved_type_variables_with_budget(&fact.parameters, budget)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?,
            ));
        }

        let abstract_nominal_count = imported
            .nominals()
            .filter(|fact| fact.access != ImportedTypeAccess::Transparent)
            .count();
        budget
            .charge(abstract_nominal_count)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let mut abstract_nominal_names = HashMap::new();
        let mut abstract_nominal_kinds = HashMap::new();
        abstract_nominal_names
            .try_reserve(abstract_nominal_count)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        abstract_nominal_kinds
            .try_reserve(abstract_nominal_count)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        for fact in imported
            .nominals()
            .filter(|fact| fact.access != ImportedTypeAccess::Transparent)
        {
            let kind = clone_arrows_with_budget(
                fact.parameters.iter().map(|parameter| &parameter.kind),
                Kind::Type,
                budget,
            )
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            let origin = fact.origin.primary_span();
            if abstract_nominal_kinds
                .insert(fact.id, NonMaterializedNominalKindFact { kind, origin })
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            if abstract_nominal_names
                .insert(fact.id, {
                    let spelling = fact.display_spelling.as_deref().unwrap_or("hidden");
                    if fact.display_is_private {
                        format!("<private {spelling}>")
                    } else {
                        spelling.to_owned()
                    }
                })
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }
        let mut local_nominal_parameter_ids = HashSet::new();
        for nominal in &self.nominals {
            let parameters = self
                .nominal_parameters
                .get(&nominal.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            for parameter in parameters {
                budget
                    .charge(1)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
                local_nominal_parameter_ids
                    .try_reserve(1)
                    .map_err(|_| ResolvedBuildFailure::TypeResource)?;
                if !local_nominal_parameter_ids.insert(parameter.id) {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
        }
        let mut registry = Self::new(nominals.into_vec(), constructors.into_vec())
            .with_type_parameters_with_budget(parameters.into_vec(), budget)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?
            .with_abstract_nominal_facts(abstract_nominal_names, abstract_nominal_kinds);
        for nominal in &self.nominals {
            let parameters = self
                .nominal_parameters
                .get(&nominal.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            for parameter in parameters {
                budget
                    .charge(1)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
                let mirror = self
                    .type_variables
                    .get(&parameter.id)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                let canonical = registry
                    .type_variables
                    .get(&parameter.id)
                    .ok_or(ResolvedBuildFailure::InvalidState)?;
                let matches = same_checker_type_variable_with_budget(canonical, mirror, budget)
                    .map_err(|()| ResolvedBuildFailure::TypeResource)?;
                if !matches {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
        }
        let remaining_count = self
            .type_variables
            .len()
            .checked_sub(local_nominal_parameter_ids.len())
            .ok_or(ResolvedBuildFailure::InvalidState)?;
        budget
            .charge(remaining_count)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let mut remaining = Vec::new();
        remaining
            .try_reserve(remaining_count)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        remaining.extend(
            self.type_variables
                .values()
                .filter(|parameter| !local_nominal_parameter_ids.contains(&parameter.id)),
        );
        if remaining.len() != remaining_count {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        remaining.sort_unstable_by_key(|parameter| parameter.id);
        for parameter in remaining {
            registry.try_insert_checker_type_variable(parameter, budget)?;
        }
        for imported_interface in imported.interface_imports() {
            registry
                .try_insert_checker_type_variable(&imported_interface.fact.parameter, budget)?;
            for method in &imported_interface.fact.methods {
                for parameter in method.type_parameters() {
                    registry.try_insert_checker_type_variable(parameter, budget)?;
                }
            }
        }
        for imported_implementation in imported.implementations() {
            for parameter in &imported_implementation.fact.head_parameters {
                registry.try_insert_checker_type_variable(parameter, budget)?;
            }
        }
        Ok(registry)
    }

    /// Combines complete defining registries by canonical semantic identity.
    ///
    /// Registry structure, combination-owned mirrors, and the exact compiler
    /// TypeWork precharge are validated before any retained carrier is cloned.
    /// The independently retained interface mirror is authenticated at the
    /// consuming linked-evidence boundary. A later allocation failure is
    /// reported as TypeResource and guarded staging is dismantled without
    /// publishing a registry; compiler-work consumption is not rolled back.
    pub(crate) fn combine_checked(
        modules: &[CheckedModule],
        type_work: &mut TypeWorkBudget,
        constraint_work: &mut crate::interface::InterfaceConstraintBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        let counts = checked_registry_counts(modules)?;
        let validated = validate_checked_registries(modules, &counts, constraint_work)?;
        type_work
            .charge(counts.retention_type_work)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let builder = CombinedRegistryBuilder::with_counts(&counts)?;
        retain_checked_registries(validated, builder)
    }

    /// Attaches ordered declaration parameters after nominal identity allocation.
    #[must_use]
    pub fn with_type_parameters(
        self,
        parameters: Vec<(NominalTypeId, Vec<ResolvedTypeVariable>)>,
    ) -> Self {
        let mut budget = TypeWorkBudget::unbounded();
        match self.with_type_parameters_with_budget(parameters, &mut budget) {
            Ok(registry) => registry,
            Err(()) => {
                unreachable!("in-memory type parameters cannot exceed the address-space work bound")
            }
        }
    }

    pub(crate) fn with_type_parameters_with_budget(
        mut self,
        parameters: Vec<(NominalTypeId, Vec<ResolvedTypeVariable>)>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, ()> {
        let mut pending = ResolvedNominalParameterVecBuffer(parameters);
        let parameter_count = pending.0.iter().try_fold(0usize, |count, (_, row)| {
            count.checked_add(row.len()).ok_or(())
        })?;
        self.nominal_parameters
            .try_reserve(pending.0.len())
            .map_err(|_| ())?;
        self.type_variables
            .try_reserve(parameter_count)
            .map_err(|_| ())?;
        pending.0.reverse();
        while let Some((owner, parameters)) = pending.0.pop() {
            let parameters = ResolvedTypeVariableBuffer(parameters);
            for parameter in parameters.iter() {
                self.insert_type_variable(clone_resolved_type_variable_with_budget(
                    parameter, budget,
                )?);
            }
            let parameters = parameters.into_vec();
            if let Some(replaced) = self
                .nominal_parameters
                .insert(owner, parameters.into_boxed_slice())
            {
                discard_resolved_type_variables(replaced);
            }
        }
        Ok(self)
    }

    /// Attaches non-nominal type parameters before the registry is published.
    #[must_use]
    pub(crate) fn with_additional_type_variables(
        mut self,
        parameters: impl IntoIterator<Item = ResolvedTypeVariable>,
    ) -> Self {
        for parameter in parameters {
            self.insert_type_variable(parameter);
        }
        self
    }

    fn with_abstract_nominal_facts(
        mut self,
        names: HashMap<NominalTypeId, String>,
        kinds: HashMap<NominalTypeId, NonMaterializedNominalKindFact>,
    ) -> Self {
        self.abstract_nominal_names = names;
        let displaced = std::mem::replace(&mut self.abstract_nominal_kinds, kinds);
        for fact in displaced.into_values() {
            discard_non_materialized_nominal_kind_fact(fact);
        }
        self
    }

    fn insert_type_variable(&mut self, parameter: ResolvedTypeVariable) {
        if let Some(replaced) = self.type_variables.insert(parameter.id, parameter) {
            discard_resolved_type_variable(replaced);
        }
    }

    /// Installs one checker-view binder from immutable canonical authority.
    /// The retained record is charged and every destination is reserved before
    /// cloning Kind or provenance. Duplicate identities never replace authority.
    fn try_insert_checker_type_variable(
        &mut self,
        parameter: &ResolvedTypeVariable,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ResolvedBuildFailure> {
        budget
            .charge(1)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        if self.type_variables.contains_key(&parameter.id) {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        self.type_variables
            .try_reserve(1)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        let kind = clone_kind_with_budget(&parameter.kind, budget)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let retained = ResolvedTypeVariable {
            id: parameter.id,
            spelling: parameter.spelling.clone(),
            kind,
            origin: parameter.origin.clone(),
        };
        let displaced = self.type_variables.insert(parameter.id, retained);
        debug_assert!(displaced.is_none());
        Ok(())
    }

    /// Returns nominal declarations in source order.
    #[must_use]
    pub fn nominals(&self) -> &[ResolvedNominalType] {
        &self.nominals
    }

    /// Returns constructors in file and declaration order.
    #[must_use]
    pub fn constructors(&self) -> &[ResolvedConstructor] {
        &self.constructors
    }

    /// Looks up a nominal declaration by stable identity.
    #[must_use]
    pub fn nominal(&self, id: NominalTypeId) -> Option<&ResolvedNominalType> {
        self.nominal_positions
            .get(&id)
            .and_then(|index| self.nominals.get(*index))
            .filter(|nominal| nominal.id == id)
    }

    /// Looks up a constructor by stable identity.
    #[must_use]
    pub fn constructor(&self, id: ConstructorId) -> Option<&ResolvedConstructor> {
        self.constructor_positions
            .get(&id)
            .and_then(|index| self.constructors.get(*index))
            .filter(|constructor| constructor.id == id)
    }

    /// Looks up a declaration type parameter by stable identity.
    #[must_use]
    pub fn type_variable(&self, id: TypeVariableId) -> Option<&ResolvedTypeVariable> {
        self.type_variables.get(&id)
    }

    /// Returns a nominal declaration's ordered parameters.
    #[must_use]
    pub fn nominal_parameters(&self, id: NominalTypeId) -> Option<&[ResolvedTypeVariable]> {
        self.nominal(id)?;
        Some(self.nominal_parameters.get(&id).map_or(&[], Box::as_ref))
    }

    pub(crate) fn canonical_nominal_parameters(
        &self,
        id: NominalTypeId,
    ) -> Option<&[ResolvedTypeVariable]> {
        self.nominal(id)?;
        self.nominal_parameters.get(&id).map(Box::as_ref)
    }

    pub(crate) fn nominal_kind(&self, id: NominalTypeId) -> Option<CanonicalNominalKind<'_>> {
        if let Some(nominal) = self.nominal(id) {
            return Some(CanonicalNominalKind::Parameters {
                parameters: self.nominal_parameters.get(&id).map_or(&[], Box::as_ref),
                origin: nominal.origin.primary_span(),
            });
        }
        self.abstract_nominal_kinds
            .get(&id)
            .map(|fact| CanonicalNominalKind::Frozen {
                kind: &fact.kind,
                origin: fact.origin,
            })
    }

    pub(crate) fn nominal_parameter_entries(
        &self,
    ) -> impl Iterator<Item = (NominalTypeId, &[ResolvedTypeVariable])> {
        self.nominal_parameters
            .iter()
            .map(|(owner, parameters)| (*owner, parameters.as_ref()))
    }

    pub(crate) fn type_variables(&self) -> impl Iterator<Item = &ResolvedTypeVariable> {
        self.type_variables.values()
    }

    pub(crate) fn type_variable_count(&self) -> usize {
        self.type_variables.len()
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn global_parameter_rows(&self) -> &[ResolvedGlobalParameterRow] {
        &self.global_parameter_rows
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn global_parameter_row(
        &self,
        owner: BinderId,
    ) -> Option<&ResolvedGlobalParameterRow> {
        self.global_parameter_positions
            .get(&owner)
            .and_then(|position| self.global_parameter_rows.get(*position))
            .filter(|row| row.owner == owner)
    }

    pub(crate) fn global_parameter_position_count(&self) -> usize {
        self.global_parameter_positions.len()
    }

    #[cfg(test)]
    pub(crate) fn clear_global_parameter_positions_for_core_test(&mut self) {
        self.global_parameter_positions.clear();
    }

    #[cfg(test)]
    pub(crate) fn global_parameter_position_for_core_test(&self, owner: BinderId) -> Option<usize> {
        self.global_parameter_positions.get(&owner).copied()
    }

    #[cfg(test)]
    pub(crate) fn corrupt_global_parameter_rows_for_core_test(
        &mut self,
        mutation: CoreGlobalParameterRowMutationForTest,
    ) -> bool {
        match mutation {
            CoreGlobalParameterRowMutationForTest::EmptyFirstRow => {
                let Some(row) = self.global_parameter_rows.first_mut() else {
                    return false;
                };
                row.parameters = Box::new([]);
            }
            CoreGlobalParameterRowMutationForTest::ReplaceFirstOwner(owner) => {
                let Some(row) = self.global_parameter_rows.first_mut() else {
                    return false;
                };
                let previous = row.owner;
                if previous == owner || self.global_parameter_positions.contains_key(&owner) {
                    return false;
                }
                let Some(position) = self.global_parameter_positions.remove(&previous) else {
                    return false;
                };
                row.owner = owner;
                self.global_parameter_positions.insert(owner, position);
            }
            CoreGlobalParameterRowMutationForTest::ReplaceFirstParameter(parameter) => {
                let Some(first) = self
                    .global_parameter_rows
                    .first_mut()
                    .and_then(|row| row.parameters.first_mut())
                else {
                    return false;
                };
                *first = parameter;
            }
            CoreGlobalParameterRowMutationForTest::DuplicateFirstParameter => {
                let Some(row) = self.global_parameter_rows.first_mut() else {
                    return false;
                };
                let [first, second, ..] = row.parameters.as_mut() else {
                    return false;
                };
                *second = *first;
            }
            CoreGlobalParameterRowMutationForTest::DuplicateAcrossRows => {
                let [first, second, ..] = self.global_parameter_rows.as_mut() else {
                    return false;
                };
                let Some(parameter) = first.parameters.first().copied() else {
                    return false;
                };
                let Some(replaced) = second.parameters.first_mut() else {
                    return false;
                };
                *replaced = parameter;
            }
            CoreGlobalParameterRowMutationForTest::SwapFirstOwnerPositions => {
                let [first, second, ..] = self.global_parameter_rows.as_ref() else {
                    return false;
                };
                let (first_owner, second_owner) = (first.owner, second.owner);
                let Some(first_position) =
                    self.global_parameter_positions.get(&first_owner).copied()
                else {
                    return false;
                };
                let Some(second_position) =
                    self.global_parameter_positions.get(&second_owner).copied()
                else {
                    return false;
                };
                self.global_parameter_positions
                    .insert(first_owner, second_position);
                self.global_parameter_positions
                    .insert(second_owner, first_position);
            }
            CoreGlobalParameterRowMutationForTest::DuplicateFirstOwner { filler } => {
                let [first, second, ..] = self.global_parameter_rows.as_mut() else {
                    return false;
                };
                if self.global_parameter_positions.contains_key(&filler) {
                    return false;
                }
                let duplicate = first.owner;
                let replaced = second.owner;
                self.global_parameter_positions.remove(&replaced);
                second.owner = duplicate;
                self.global_parameter_positions.insert(filler, usize::MAX);
            }
            CoreGlobalParameterRowMutationForTest::RemoveLastRow => {
                let mut rows = std::mem::take(&mut self.global_parameter_rows).into_vec();
                let Some(removed) = rows.pop() else {
                    return false;
                };
                self.global_parameter_positions.remove(&removed.owner);
                self.global_parameter_rows = rows.into_boxed_slice();
            }
            CoreGlobalParameterRowMutationForTest::AppendRow { owner, parameter } => {
                if self.global_parameter_positions.contains_key(&owner) {
                    return false;
                }
                let mut rows = std::mem::take(&mut self.global_parameter_rows).into_vec();
                let position = rows.len();
                rows.push(ResolvedGlobalParameterRow {
                    owner,
                    parameters: Box::new([parameter]),
                });
                self.global_parameter_positions.insert(owner, position);
                self.global_parameter_rows = rows.into_boxed_slice();
            }
            CoreGlobalParameterRowMutationForTest::RemoveCanonicalParameter(parameter) => {
                let Some(removed) = self.type_variables.remove(&parameter) else {
                    return false;
                };
                discard_resolved_type_variable(removed);
            }
            CoreGlobalParameterRowMutationForTest::AddSurplusPosition(owner) => {
                if self.global_parameter_positions.contains_key(&owner) {
                    return false;
                }
                self.global_parameter_positions.insert(owner, usize::MAX);
            }
        }
        true
    }

    /// Renders a type with source declaration spellings for nominal identities.
    #[must_use]
    pub fn display_type(&self, ty: &Type) -> String {
        self.display_type_with_inference(ty, false)
    }

    /// Renders a source-facing type without exposing elaborator inference identities.
    #[must_use]
    pub(crate) fn display_source_type(&self, ty: &Type) -> String {
        self.display_type_with_inference(ty, true)
    }

    fn display_type_with_inference(&self, ty: &Type, anonymous_inference: bool) -> String {
        enum Task<'a> {
            Type(&'a Type),
            ApplicationSpine(&'a Type),
            Text(&'static str),
        }

        let mut output = String::new();
        let mut work = vec![Task::Type(ty)];
        while let Some(task) = work.pop() {
            match task {
                Task::Text(text) => output.push_str(text),
                Task::Type(Type::Int) => output.push_str("Int"),
                Task::Type(Type::Bool) => output.push_str("Bool"),
                Task::Type(Type::Unit) => output.push_str("Unit"),
                Task::Type(Type::Nominal(id)) => {
                    if let Some(nominal) = self.nominal(*id) {
                        output.push_str(&nominal.spelling);
                    } else if let Some(spelling) = self.abstract_nominal_names.get(id) {
                        output.push_str(spelling);
                    } else {
                        output.push_str(&Type::Nominal(*id).to_string());
                    }
                }
                Task::Type(Type::Variable(id)) => {
                    if let Some(variable) = self.type_variable(*id) {
                        output.push_str(&variable.spelling);
                    } else {
                        output.push_str(&Type::Variable(*id).to_string());
                    }
                }
                Task::Type(Type::Inference(id)) => {
                    if anonymous_inference {
                        output.push('_');
                    } else {
                        output.push_str(&Type::Inference(*id).to_string());
                    }
                }
                Task::Type(application @ Type::Application(_, _)) => {
                    work.push(Task::Text(">"));
                    work.push(Task::ApplicationSpine(application));
                }
                Task::ApplicationSpine(Type::Application(function, argument)) => {
                    work.push(Task::Type(argument));
                    if matches!(function.as_ref(), Type::Application(_, _)) {
                        work.push(Task::Text(", "));
                        work.push(Task::ApplicationSpine(function));
                    } else {
                        work.push(Task::Text("<"));
                        if matches!(function.as_ref(), Type::Function(_, _) | Type::Forall(_, _)) {
                            work.push(Task::Text(")"));
                            work.push(Task::Type(function));
                            work.push(Task::Text("("));
                        } else {
                            work.push(Task::Type(function));
                        }
                    }
                }
                Task::ApplicationSpine(_) => unreachable!("application spine tasks are closed"),
                Task::Type(Type::Forall(parameters, body)) => {
                    output.push_str("forall ");
                    for (index, (parameter, kind)) in parameters.iter().enumerate() {
                        if index > 0 {
                            output.push_str(", ");
                        }
                        if let Some(variable) = self.type_variable(*parameter) {
                            output.push_str(&variable.spelling);
                        } else {
                            output.push_str(&format!("T{}", parameter.local()));
                        }
                        output.push_str(" : ");
                        output.push_str(&kind.to_string());
                    }
                    output.push_str(". ");
                    work.push(Task::Type(body));
                }
                Task::Type(Type::Tuple(elements)) => {
                    output.push('(');
                    work.push(Task::Text(")"));
                    for (index, element) in elements.iter().enumerate().rev() {
                        work.push(Task::Type(element));
                        if index > 0 {
                            work.push(Task::Text(", "));
                        }
                    }
                }
                Task::Type(Type::Function(domain, codomain)) => {
                    work.push(Task::Type(codomain));
                    work.push(Task::Text(" -> "));
                    if matches!(domain.as_ref(), Type::Function(_, _)) {
                        work.push(Task::Text(")"));
                        work.push(Task::Type(domain));
                        work.push(Task::Text("("));
                    } else {
                        work.push(Task::Type(domain));
                    }
                }
            }
        }
        output
    }

    /// Destroys untrusted registry payloads without following host recursion.
    pub(crate) fn discard_iteratively(mut self) {
        self.discard_owned_payloads();
    }

    fn discard_owned_payloads(&mut self) {
        let nominals = std::mem::take(&mut self.nominals);
        let constructors = std::mem::take(&mut self.constructors);
        let nominal_parameters = std::mem::take(&mut self.nominal_parameters);
        let type_variables = std::mem::take(&mut self.type_variables);
        let global_parameter_rows = std::mem::take(&mut self.global_parameter_rows);
        let abstract_nominal_kinds = std::mem::take(&mut self.abstract_nominal_kinds);
        self.nominal_positions.clear();
        self.constructor_positions.clear();
        self.global_parameter_positions.clear();
        for nominal in nominals.into_vec() {
            discard_origin_iteratively(nominal.origin);
        }
        for constructor in constructors.into_vec() {
            if let Some(payload) = constructor.payload {
                discard_type_iteratively(payload);
            }
            discard_origin_iteratively(constructor.origin);
        }
        for parameters in nominal_parameters.into_values() {
            discard_resolved_type_variables(parameters);
        }
        for parameter in type_variables.into_values() {
            discard_resolved_type_variable(parameter);
        }
        drop(global_parameter_rows);
        drop(abstract_nominal_kinds);
    }
}

fn discard_resolved_type_variable(parameter: ResolvedTypeVariable) {
    discard_origin_iteratively(parameter.origin);
}

fn discard_non_materialized_nominal_kind_fact(fact: NonMaterializedNominalKindFact) {
    drop(fact);
}

pub(crate) fn clone_resolved_type_variable_with_budget(
    parameter: &ResolvedTypeVariable,
    budget: &mut TypeWorkBudget,
) -> Result<ResolvedTypeVariable, ()> {
    budget.charge(1)?;
    let kind = clone_kind_with_budget(&parameter.kind, budget)?;
    Ok(ResolvedTypeVariable {
        id: parameter.id,
        spelling: parameter.spelling.clone(),
        kind,
        origin: parameter.origin.clone(),
    })
}

pub(crate) fn same_resolved_type_variables_with_charge(
    left: &[ResolvedTypeVariable],
    right: &[ResolvedTypeVariable],
    mut charge: impl FnMut(usize) -> Result<(), ()>,
) -> Result<bool, ()> {
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        charge(1)?;
        if left.id != right.id || left.spelling != right.spelling || left.origin != right.origin {
            return Ok(false);
        }
        if !same_kind_with_charge(&left.kind, &right.kind, || charge(1))? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
pub(crate) fn same_resolved_type_variables_with_budget(
    left: &[ResolvedTypeVariable],
    right: &[ResolvedTypeVariable],
    budget: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    same_resolved_type_variables_with_charge(left, right, |work| budget.charge(work))
}

/// Authenticates one checker-view mirror without recursive Origin comparison.
fn same_checker_type_variable_with_budget(
    left: &ResolvedTypeVariable,
    right: &ResolvedTypeVariable,
    budget: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    budget.charge(1)?;
    if left.id != right.id || left.spelling != right.spelling {
        return Ok(false);
    }
    if !same_origin_with_budget(&left.origin, &right.origin, budget)? {
        return Ok(false);
    }
    same_kind_with_charge(&left.kind, &right.kind, || budget.charge(1))
}

pub(crate) fn same_origin_with_budget(
    mut left: &Origin,
    mut right: &Origin,
    budget: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    loop {
        budget.charge(1)?;
        match (left, right) {
            (Origin::Source(left), Origin::Source(right)) => return Ok(left == right),
            (
                Origin::Generated {
                    cause: left_cause,
                    reason: left_reason,
                },
                Origin::Generated {
                    cause: right_cause,
                    reason: right_reason,
                },
            ) if left_reason == right_reason => {
                left = left_cause;
                right = right_cause;
            }
            (
                Origin::Related {
                    primary: left_primary,
                    related: left_related,
                },
                Origin::Related {
                    primary: right_primary,
                    related: right_related,
                },
            ) if left_related.len() == right_related.len() => {
                budget.charge(left_related.len())?;
                if left_related != right_related {
                    return Ok(false);
                }
                left = left_primary;
                right = right_primary;
            }
            _ => return Ok(false),
        }
    }
}

pub(crate) fn clone_resolved_type_variables_with_budget(
    parameters: &[ResolvedTypeVariable],
    budget: &mut TypeWorkBudget,
) -> Result<Vec<ResolvedTypeVariable>, ()> {
    clone_resolved_type_variable_buffer_with_budget(parameters, budget)
        .map(ResolvedTypeVariableBuffer::into_vec)
}

fn clone_resolved_type_variable_buffer_with_budget(
    parameters: &[ResolvedTypeVariable],
    budget: &mut TypeWorkBudget,
) -> Result<ResolvedTypeVariableBuffer, ()> {
    let mut cloned = ResolvedTypeVariableBuffer(Vec::new());
    cloned.try_reserve(parameters.len()).map_err(|_| ())?;
    for parameter in parameters {
        cloned.push(clone_resolved_type_variable_with_budget(parameter, budget)?);
    }
    Ok(cloned)
}

fn discard_resolved_type_variables(parameters: Box<[ResolvedTypeVariable]>) {
    for parameter in parameters.into_vec() {
        discard_resolved_type_variable(parameter);
    }
}

impl Drop for ResolvedRegistry {
    fn drop(&mut self) {
        self.discard_owned_payloads();
    }
}

/// Resolved metadata for one nominal declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedNominalType {
    /// Stable source-order identity.
    pub id: NominalTypeId,
    /// Exact declaration spelling.
    pub spelling: String,
    /// Constructor identities in declaration order.
    pub constructors: Box<[ConstructorId]>,
    /// Declaration provenance.
    pub origin: Origin,
}

/// One resolved source type binder.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedTypeVariable {
    /// Stable program-local identity.
    pub id: TypeVariableId,
    /// Exact source spelling.
    pub spelling: String,
    /// Fixed semantic kind assigned by the defining declaration.
    pub kind: Kind,
    /// Definition provenance.
    pub origin: Origin,
}

/// Resolved metadata for one constructor declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedConstructor {
    /// Stable constructor identity.
    pub id: ConstructorId,
    /// Owning nominal identity.
    pub owner: NominalTypeId,
    /// Exact constructor spelling.
    pub spelling: String,
    /// Zero or one semantic payload type.
    pub payload: Option<Type>,
    /// Declaration provenance.
    pub origin: Origin,
}

impl ResolvedConstructor {
    /// Consumes standalone constructor metadata and dismantles its optional
    /// payload without recursive type drop.
    pub fn discard_iteratively(self) {
        if let Some(payload) = self.payload {
            discard_type_iteratively(payload);
        }
        discard_origin_iteratively(self.origin);
    }
}

/// One fully resolved type occurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedType {
    /// Resolved structural or nominal type.
    pub ty: Type,
    /// Stack-safe provenance aligned with every structural type component.
    pub provenance: ResolvedTypeProvenance,
    /// Causal source provenance.
    pub origin: Origin,
    /// Complete source occurrence span.
    pub span: Span,
}

impl ResolvedType {
    /// Consumes a standalone resolved type and dismantles its structural tree
    /// without following the host call stack.
    pub fn discard_iteratively(self) {
        discard_resolved_type(self);
    }
}

/// Shareable arena-shaped provenance for one resolved type occurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedTypeProvenance {
    nodes: Arc<[ResolvedTypeProvenanceNode]>,
    root: usize,
}

/// One node in a resolved type-provenance arena.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedTypeProvenanceNode {
    /// An atomic or nominal type occurrence.
    Fact(Span),
    /// A tuple occurrence and its element provenance roots.
    Tuple { span: Span, elements: Box<[usize]> },
    /// A function occurrence and its component provenance roots.
    Function {
        span: Span,
        domain: usize,
        codomain: usize,
    },
    /// One canonical unary type application and its causal source argument.
    Application {
        span: Span,
        function: usize,
        argument: usize,
        argument_span: Span,
    },
}

impl ResolvedTypeProvenance {
    /// Builds an admitted provenance arena from source-ordered nodes.
    #[must_use]
    pub(crate) fn new(nodes: Vec<ResolvedTypeProvenanceNode>, root: usize) -> Self {
        Self {
            nodes: nodes.into(),
            root,
        }
    }

    /// Returns the complete source span of this provenance view.
    #[must_use]
    pub fn span(&self) -> Option<Span> {
        self.nodes.get(self.root).map(|node| match node {
            ResolvedTypeProvenanceNode::Fact(span)
            | ResolvedTypeProvenanceNode::Tuple { span, .. }
            | ResolvedTypeProvenanceNode::Function { span, .. }
            | ResolvedTypeProvenanceNode::Application { span, .. } => *span,
        })
    }

    /// Returns views of a function domain and codomain.
    #[must_use]
    pub fn function_parts(&self) -> Option<(Self, Self)> {
        let ResolvedTypeProvenanceNode::Function {
            domain, codomain, ..
        } = self.nodes.get(self.root)?
        else {
            return None;
        };
        Some((self.view(*domain)?, self.view(*codomain)?))
    }

    /// Returns tuple element views in source order.
    #[must_use]
    pub fn tuple_elements(&self) -> Option<Vec<Self>> {
        let ResolvedTypeProvenanceNode::Tuple { elements, .. } = self.nodes.get(self.root)? else {
            return None;
        };
        elements.iter().map(|root| self.view(*root)).collect()
    }

    fn view(&self, root: usize) -> Option<Self> {
        self.nodes.get(root)?;
        Some(Self {
            nodes: Arc::clone(&self.nodes),
            root,
        })
    }

    pub(crate) fn nodes(&self) -> &[ResolvedTypeProvenanceNode] {
        &self.nodes
    }

    pub(crate) const fn root(&self) -> usize {
        self.root
    }
}

/// One resolved global definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedDefinition {
    /// Presentation-specific definition payload.
    pub kind: ResolvedDefinitionKind,
    /// Complete definition span.
    pub span: Span,
}

/// One locally declared method-only interface after name resolution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedInterfaceDeclaration {
    /// Stable module-qualified interface identity.
    pub id: InterfaceId,
    /// Whether the interface is eligible for checked publication.
    pub public: bool,
    /// Exact declared spelling.
    pub spelling: String,
    /// The interface's single resolved type parameter.
    pub parameter: ResolvedTypeVariable,
    /// Nonempty methods in semantic declaration order.
    pub methods: Box<[ResolvedInterfaceMethod]>,
    /// Causal declaration provenance.
    pub origin: Origin,
    /// Complete declaration span.
    pub span: Span,
}

/// One resolved signature-only interface method.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedInterfaceMethod {
    /// Stable identity within the owning interface.
    pub id: MethodId,
    /// Exact declared spelling.
    pub spelling: String,
    /// Resolved source value type.
    pub annotation: ResolvedType,
    /// Ordered method-local binders or absent-list rejection candidates.
    pub type_parameters: Box<[ResolvedTypeVariable]>,
    /// Whether `type_parameters` came from a present, nonempty complete source list.
    pub has_explicit_type_parameters: bool,
    /// Causal method provenance.
    pub origin: Origin,
    /// Complete method-signature span.
    pub span: Span,
}

/// One resolved occurrence of an interface in a requirement or impl head.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedInterfaceOccurrence {
    /// Stable selected interface identity.
    pub id: InterfaceId,
    /// Exact source spelling.
    pub spelling: String,
    /// Causal source provenance.
    pub origin: Origin,
}

/// One ordered resolved interface requirement outside the ordinary type algebra.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedRequirement {
    /// Owner-qualified occurrence identity.
    pub id: RequirementId,
    /// Resolved interface occurrence.
    pub interface: ResolvedInterfaceOccurrence,
    /// Resolved single type argument.
    pub argument: ResolvedType,
    /// Complete requirement span.
    pub span: Span,
}

/// One resolved implementation declaration retained for Task 4 checking.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedImplementation {
    /// Stable category-local implementation identity.
    pub id: ImplId,
    /// Whether the checked anonymous fact is eligible for publication.
    pub public: bool,
    /// Implemented interface occurrence.
    pub interface: ResolvedInterfaceOccurrence,
    /// Resolved implementation head argument.
    pub argument: ResolvedType,
    /// Rigid parameters discovered from the head in first-occurrence order.
    pub head_parameters: Box<[ResolvedTypeVariable]>,
    /// Candidate variables found only in prerequisites.
    pub prerequisite_only_parameters: Box<[ResolvedTypeVariable]>,
    /// Ordered prerequisites owned by this implementation.
    pub prerequisites: Box<[ResolvedRequirement]>,
    /// Maximal contiguous source method groups.
    pub method_groups: Box<[ResolvedImplementationMethodGroup]>,
    /// Complete implementation span.
    pub span: Span,
}

/// One maximal contiguous implementation method-equation group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedImplementationMethodGroup {
    /// Interface method named by the source head, when it is a method at all.
    pub method: Option<MethodId>,
    /// Identity derived from the impl and method, retained even for duplicates.
    pub identity: Option<ImplMethodId>,
    /// Hidden module-qualified binder allocated for this exact source group.
    pub binder: Binder,
    /// Nonempty equations in the contiguous group.
    pub equations: Box<[ResolvedEquation]>,
    /// Complete group span.
    pub span: Span,
}

/// The closed resolved global-definition family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedDefinitionKind {
    /// An external interface followed by an equation.
    Equational(ResolvedEquationalGlobal),
    /// An inline operational function definition.
    InlineOperational(ResolvedInlineOperationalGlobal),
}

/// A resolved equational global.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedEquationalGlobal {
    /// Separately written external interface.
    pub interface: ResolvedExternalInterface,
    /// Nonempty contiguous clause group.
    pub equations: Vec<ResolvedEquation>,
}

/// A resolved external interface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedExternalInterface {
    /// Global definition site.
    pub name: Binder,
    /// Declared resolved type.
    pub annotation: ResolvedType,
    /// Ordered explicit interface requirements.
    pub requirements: Box<[ResolvedRequirement]>,
    /// Implicit outer type binders in first-occurrence order.
    pub type_parameters: Box<[ResolvedTypeVariable]>,
    /// Complete interface span.
    pub span: Span,
}

/// A resolved equation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedEquation {
    /// Repeated global name in the equation head.
    pub name: ResolvedEquationHead,
    /// Patterns consuming successive arrow domains.
    pub patterns: Vec<ResolvedPattern>,
    /// Resolved equation body.
    pub body: ResolvedExpr,
    /// Complete equation span.
    pub span: Span,
}

/// A resolved inline operational global.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedInlineOperationalGlobal {
    /// Complete operational header.
    pub header: ResolvedInlineOperationalHeader,
    /// Resolved braced body.
    pub body: ResolvedBlock,
}

/// A resolved inline operational header.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedInlineOperationalHeader {
    /// Global definition site.
    pub name: Binder,
    /// Nonempty typed operational parameter vector.
    pub parameters: Vec<ResolvedTypedPattern>,
    /// Declared result type.
    pub result_type: ResolvedType,
    /// Ordered explicit interface requirements.
    pub requirements: Box<[ResolvedRequirement]>,
    /// Implicit outer type binders in first-occurrence order.
    pub type_parameters: Box<[ResolvedTypeVariable]>,
    /// Complete header span, excluding the body.
    pub span: Span,
}

/// One resolved pattern with a resolved type annotation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedTypedPattern {
    /// Resolved pattern.
    pub pattern: ResolvedPattern,
    /// Required resolved type.
    pub annotation: ResolvedType,
    /// Complete source span.
    pub span: Span,
}

/// One resolved pattern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedPattern {
    /// Resolved pattern payload.
    pub kind: ResolvedPatternKind,
    /// Complete pattern span.
    pub span: Span,
}

/// The closed resolved pattern family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedPatternKind {
    /// A stable binder definition.
    Binder(Binder),
    /// A nonbinding wildcard.
    Wildcard,
    /// A Boolean literal pattern.
    Boolean(bool),
    /// Unit.
    Unit,
    /// A structural tuple pattern.
    Tuple(Vec<ResolvedPattern>),
    /// A constructor identity and optional payload pattern.
    Constructor {
        /// Resolved constructor identity.
        constructor: ConstructorId,
        /// Original spelling and source provenance.
        occurrence: ResolvedConstructorOccurrence,
        /// Optional payload pattern.
        payload: Option<Box<ResolvedPattern>>,
    },
}

/// A resolved sequential block.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedBlock {
    /// Ordered resolved local declarations.
    pub declarations: Vec<ResolvedLocalDeclaration>,
    /// Required block result expression.
    pub result: Box<ResolvedExpr>,
    /// Complete braced span.
    pub span: Span,
}

/// The closed resolved local-declaration family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedLocalDeclaration {
    /// A sequential nonrecursive binding.
    Binding(Box<ResolvedBinding>),
    /// A simultaneous recursive binding group.
    Recursive(ResolvedRecursiveGroup),
}

/// One resolved simultaneous recursive binding group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedRecursiveGroup {
    /// Members in source order.
    pub members: Vec<ResolvedRecursiveMember>,
    /// Complete recursive group span.
    pub span: Span,
}

/// One resolved recursive group member.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedRecursiveMember {
    /// The `let rec` or `and` delimiter introducing this member.
    pub introducer_span: Span,
    /// Introduced definition site.
    pub binder: Binder,
    /// Required declared monotype.
    pub annotation: ResolvedType,
    /// Initializer resolved in the simultaneous group scope.
    pub initializer: ResolvedExpr,
    /// Complete member span.
    pub span: Span,
}

/// A resolved immutable local binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedBinding {
    /// Introduced irrefutable pattern.
    pub pattern: ResolvedPattern,
    /// Optional source type annotation.
    pub annotation: Option<ResolvedType>,
    /// Initializer resolved in the incoming scope.
    pub initializer: ResolvedExpr,
    /// Complete binding span.
    pub span: Span,
}

/// A resolved expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedExpr {
    /// Resolved expression payload.
    pub kind: ResolvedExprKind,
    /// Complete expression span.
    pub span: Span,
}

/// The closed resolved expression family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolvedExprKind {
    /// An arbitrary-precision integer literal.
    Integer(Integer),
    /// A Boolean literal.
    Boolean(bool),
    /// The unit value.
    Unit,
    /// A resolved name occurrence.
    Occurrence(ResolvedOccurrence),
    /// A resolved constructor term occurrence.
    Constructor(ResolvedConstructorOccurrence),
    /// A strict structural tuple.
    Tuple(Vec<ResolvedExpr>),
    /// Strict unary application.
    Apply(ResolvedApplicationExpr),
    /// Integer addition.
    Add(ResolvedBinaryExpr),
    /// Integer multiplication.
    Multiply(ResolvedBinaryExpr),
    /// Integer equality.
    Equal(ResolvedBinaryExpr),
    /// A sequential block expression.
    Block(ResolvedBlock),
    /// An anonymous unary function.
    Function(ResolvedFunctionExpr),
    /// A structured match.
    Match(ResolvedMatchExpr),
}

/// One resolved constructor occurrence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedConstructorOccurrence {
    /// Stable constructor identity.
    pub constructor: ConstructorId,
    /// Exact source spelling.
    pub spelling: String,
    /// Causal source provenance.
    pub origin: Origin,
}

/// A resolved structured match.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedMatchExpr {
    /// Resolved scrutinee.
    pub scrutinee: Box<ResolvedExpr>,
    /// Source-ordered arms.
    pub arms: Vec<ResolvedMatchArm>,
}

/// One resolved match arm.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedMatchArm {
    /// Resolved arm pattern.
    pub pattern: ResolvedPattern,
    /// Resolved arm body.
    pub body: ResolvedExpr,
    /// Complete arm span.
    pub span: Span,
}

/// A resolved unary application.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedApplicationExpr {
    /// Resolved function position.
    pub function: Box<ResolvedExpr>,
    /// Resolved argument position.
    pub argument: Box<ResolvedExpr>,
}

/// A resolved binary expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedBinaryExpr {
    /// Resolved left operand.
    pub left: Box<ResolvedExpr>,
    /// Resolved right operand.
    pub right: Box<ResolvedExpr>,
    /// Exact source span of the operator token.
    pub operator_span: Span,
}

/// A resolved anonymous function expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedFunctionExpr {
    /// Unary domain pattern.
    pub pattern: ResolvedPattern,
    /// Resolved braced body.
    pub body: ResolvedBlock,
}

pub(crate) fn discard_resolved_definition_iteratively(definition: ResolvedDefinition) {
    let mut expressions = Vec::new();
    let mut patterns = Vec::new();
    match definition.kind {
        ResolvedDefinitionKind::Equational(global) => {
            discard_external_interface(global.interface);
            for equation in global.equations {
                discard_equation_into_work(equation, &mut expressions, &mut patterns);
            }
        }
        ResolvedDefinitionKind::InlineOperational(global) => {
            discard_binder(global.header.name);
            for parameter in global.header.parameters {
                patterns.push(parameter.pattern);
                discard_resolved_type(parameter.annotation);
            }
            discard_resolved_type(global.header.result_type);
            for requirement in global.header.requirements {
                discard_resolved_requirement(requirement);
            }
            for parameter in global.header.type_parameters {
                discard_origin_iteratively(parameter.origin);
            }
            discard_block_into_work(global.body, &mut expressions, &mut patterns);
        }
    }
    discard_resolved_body_work(expressions, patterns);
}

pub(crate) fn discard_resolved_implementation_iteratively(implementation: ResolvedImplementation) {
    discard_origin_iteratively(implementation.interface.origin);
    discard_resolved_type(implementation.argument);
    for parameter in implementation.head_parameters {
        discard_origin_iteratively(parameter.origin);
    }
    for parameter in implementation.prerequisite_only_parameters {
        discard_origin_iteratively(parameter.origin);
    }
    for prerequisite in implementation.prerequisites {
        discard_resolved_requirement(prerequisite);
    }
    let mut expressions = Vec::new();
    let mut patterns = Vec::new();
    for group in implementation.method_groups {
        discard_binder(group.binder);
        for equation in group.equations {
            discard_equation_into_work(equation, &mut expressions, &mut patterns);
        }
    }
    discard_resolved_body_work(expressions, patterns);
}

pub(crate) fn discard_resolved_interface_iteratively(interface: ResolvedInterfaceDeclaration) {
    discard_origin_iteratively(interface.parameter.origin);
    for method in interface.methods.into_vec() {
        discard_resolved_type(method.annotation);
        for parameter in method.type_parameters.into_vec() {
            discard_origin_iteratively(parameter.origin);
        }
        discard_origin_iteratively(method.origin);
    }
    discard_origin_iteratively(interface.origin);
}

fn discard_external_interface(interface: ResolvedExternalInterface) {
    discard_binder(interface.name);
    discard_resolved_type(interface.annotation);
    for requirement in interface.requirements {
        discard_resolved_requirement(requirement);
    }
    for parameter in interface.type_parameters {
        discard_origin_iteratively(parameter.origin);
    }
}

pub(crate) fn discard_resolved_requirement(requirement: ResolvedRequirement) {
    discard_origin_iteratively(requirement.interface.origin);
    discard_resolved_type(requirement.argument);
}

pub(crate) fn discard_resolved_equation_iteratively(equation: ResolvedEquation) {
    discard_resolved_body_work(vec![equation.body], equation.patterns);
    discard_origin_iteratively(equation.name.origin);
}

fn discard_resolved_type(resolved: ResolvedType) {
    discard_type_iteratively(resolved.ty);
    discard_origin_iteratively(resolved.origin);
}

fn discard_binder(binder: Binder) {
    discard_origin_iteratively(binder.origin);
}

fn discard_equation_into_work(
    equation: ResolvedEquation,
    expressions: &mut Vec<ResolvedExpr>,
    patterns: &mut Vec<ResolvedPattern>,
) {
    discard_origin_iteratively(equation.name.origin);
    patterns.extend(equation.patterns);
    expressions.push(equation.body);
}

fn discard_block_into_work(
    block: ResolvedBlock,
    expressions: &mut Vec<ResolvedExpr>,
    patterns: &mut Vec<ResolvedPattern>,
) {
    expressions.push(*block.result);
    for declaration in block.declarations {
        match declaration {
            ResolvedLocalDeclaration::Binding(binding) => {
                let binding = *binding;
                patterns.push(binding.pattern);
                if let Some(annotation) = binding.annotation {
                    discard_resolved_type(annotation);
                }
                expressions.push(binding.initializer);
            }
            ResolvedLocalDeclaration::Recursive(group) => {
                for member in group.members {
                    discard_binder(member.binder);
                    discard_resolved_type(member.annotation);
                    expressions.push(member.initializer);
                }
            }
        }
    }
}

fn discard_resolved_body_work(
    mut expressions: Vec<ResolvedExpr>,
    mut patterns: Vec<ResolvedPattern>,
) {
    while let Some(expression) = expressions.pop() {
        match expression.kind {
            ResolvedExprKind::Integer(_)
            | ResolvedExprKind::Boolean(_)
            | ResolvedExprKind::Unit => {}
            ResolvedExprKind::Occurrence(occurrence) => {
                discard_origin_iteratively(occurrence.origin);
            }
            ResolvedExprKind::Constructor(occurrence) => {
                discard_origin_iteratively(occurrence.origin);
            }
            ResolvedExprKind::Tuple(elements) => expressions.extend(elements),
            ResolvedExprKind::Apply(application) => {
                expressions.push(*application.function);
                expressions.push(*application.argument);
            }
            ResolvedExprKind::Add(binary)
            | ResolvedExprKind::Multiply(binary)
            | ResolvedExprKind::Equal(binary) => {
                expressions.push(*binary.left);
                expressions.push(*binary.right);
            }
            ResolvedExprKind::Block(block) => {
                discard_block_into_work(block, &mut expressions, &mut patterns);
            }
            ResolvedExprKind::Function(function) => {
                patterns.push(function.pattern);
                discard_block_into_work(function.body, &mut expressions, &mut patterns);
            }
            ResolvedExprKind::Match(matched) => {
                expressions.push(*matched.scrutinee);
                for arm in matched.arms {
                    patterns.push(arm.pattern);
                    expressions.push(arm.body);
                }
            }
        }
    }
    while let Some(pattern) = patterns.pop() {
        match pattern.kind {
            ResolvedPatternKind::Binder(binder) => discard_binder(binder),
            ResolvedPatternKind::Wildcard
            | ResolvedPatternKind::Boolean(_)
            | ResolvedPatternKind::Unit => {}
            ResolvedPatternKind::Tuple(elements) => patterns.extend(elements),
            ResolvedPatternKind::Constructor {
                occurrence,
                payload,
                ..
            } => {
                discard_origin_iteratively(occurrence.origin);
                if let Some(payload) = payload {
                    patterns.push(*payload);
                }
            }
        }
    }
}

pub(crate) fn discard_resolved_expression_iteratively(expression: ResolvedExpr) {
    discard_resolved_body_work(vec![expression], Vec::new());
}

pub(crate) fn discard_resolved_pattern_iteratively(pattern: ResolvedPattern) {
    discard_resolved_body_work(Vec::new(), vec![pattern]);
}

pub(crate) fn discard_resolved_local_declaration_iteratively(
    declaration: ResolvedLocalDeclaration,
) {
    let span = match &declaration {
        ResolvedLocalDeclaration::Binding(binding) => binding.span,
        ResolvedLocalDeclaration::Recursive(group) => group.span,
    };
    discard_resolved_body_work(
        vec![ResolvedExpr {
            kind: ResolvedExprKind::Block(ResolvedBlock {
                declarations: vec![declaration],
                result: Box::new(ResolvedExpr {
                    kind: ResolvedExprKind::Unit,
                    span,
                }),
                span,
            }),
            span,
        }],
        Vec::new(),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy)]
    enum FamilyCarrierForTest {
        Public { aliases: usize },
        HiddenTransparent,
        HiddenIdentity,
    }

    fn family_authentication_summary(
        carrier: FamilyCarrierForTest,
        width: usize,
        omitted_physical: Option<usize>,
    ) -> ExportSummary {
        let source = SourceFile::new("family-authentication.ash", "family")
            .expect("the family-authentication source should fit");
        let span = source
            .span(ByteRange::new(0, 6).expect("the family range should be ordered"))
            .expect("the family span should fit");
        let summary_module = ModuleId::new(9_800);
        let owner_module = if matches!(carrier, FamilyCarrierForTest::Public { .. }) {
            summary_module
        } else {
            ModuleId::new(9_801)
        };
        let owner = NominalTypeId::new(owner_module, 0);
        let family = (0..width)
            .map(|index| {
                ConstructorId::new(
                    owner,
                    u32::try_from(index).expect("the family width should fit"),
                )
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let mut summary = ExportSummary::empty(summary_module);
        match carrier {
            FamilyCarrierForTest::Public { aliases } => {
                for index in 0..aliases {
                    let spelling = format!("Family{index}");
                    summary.nominal_order.push(spelling.clone());
                    summary.nominals.insert(
                        spelling.clone(),
                        ExportedType {
                            id: owner,
                            parameter_count: 0,
                            constructor_count: width,
                            parameters: Box::new([]),
                            constructors: family.clone(),
                            access: ExportedTypeAccess::Transparent,
                            origin: Origin::Source(span),
                        },
                    );
                    summary.nominal_names_by_id.entry(owner).or_insert(spelling);
                }
            }
            FamilyCarrierForTest::HiddenTransparent | FamilyCarrierForTest::HiddenIdentity => {
                summary.hidden_nominal_order.push(owner);
                summary.hidden_nominals.insert(
                    owner,
                    ExportedHiddenType {
                        id: owner,
                        parameter_count: 0,
                        constructor_count: width,
                        parameters: Box::new([]),
                        constructors: if matches!(carrier, FamilyCarrierForTest::HiddenTransparent)
                        {
                            family.clone()
                        } else {
                            Box::new([])
                        },
                        access: if matches!(carrier, FamilyCarrierForTest::HiddenTransparent) {
                            ImportedTypeAccess::Transparent
                        } else {
                            ImportedTypeAccess::Hidden
                        },
                        spelling: "Family".to_owned(),
                        display_is_private: false,
                        origin: Origin::Source(span),
                    },
                );
            }
        }
        if !matches!(carrier, FamilyCarrierForTest::HiddenIdentity) {
            for (index, identity) in family.iter().copied().enumerate() {
                if omitted_physical == Some(index) {
                    continue;
                }
                let spelling = format!("Value{index}");
                let constructor = ExportedConstructor {
                    id: identity,
                    spelling: spelling.clone(),
                    payload: None,
                    scheme: ConstrainedScheme::from_rank1_type(Type::Nominal(owner)),
                    origin: Origin::Source(span),
                };
                match carrier {
                    FamilyCarrierForTest::Public { .. } => {
                        summary.constructor_order.push(spelling.clone());
                        summary
                            .constructor_names_by_id
                            .insert(identity, spelling.clone());
                        summary.constructors.insert(spelling, constructor);
                    }
                    FamilyCarrierForTest::HiddenTransparent => {
                        summary.hidden_constructor_order.push(identity);
                        summary.hidden_constructors.insert(identity, constructor);
                    }
                    FamilyCarrierForTest::HiddenIdentity => unreachable!(),
                }
            }
        }
        summary
    }

    #[test]
    fn constructor_family_authentication_has_exact_constraint_limits_and_reusable_inputs() {
        fn assert_clean(summary: &ExportSummary, exact: usize, short_used: usize) {
            let mut short = crate::interface::InterfaceConstraintBudget::with_limit(exact - 1);
            assert_eq!(
                summary.authenticate(&mut TypeWorkBudget::default(), &mut short),
                Err(ResolvedBuildFailure::ConstraintResource),
            );
            assert_eq!(short.used(), short_used);
            for _ in 0..2 {
                let mut constraint = crate::interface::InterfaceConstraintBudget::with_limit(exact);
                summary
                    .authenticate(&mut TypeWorkBudget::default(), &mut constraint)
                    .expect("the exact family summary should remain reusable");
                assert_eq!(constraint.used(), exact);
            }
        }

        const WIDTH: usize = 4;
        const ALIASES: usize = 3;
        // Each public spelling contributes one fused order/namespace cell.
        // Each alias after the canonical nominal contributes one Source-Origin
        // equality cell before the batched public reverse-index charge.
        const PUBLIC_PRE_REVERSE: usize =
            ALIASES * WIDTH + 2 * ALIASES + 2 * WIDTH + 2 + (ALIASES - 1);
        const PUBLIC_EXACT: usize = PUBLIC_PRE_REVERSE + ALIASES + WIDTH;
        const HIDDEN_TRANSPARENT_EXACT: usize = 3 * WIDTH + 4;
        const HIDDEN_IDENTITY_EXACT: usize = 4;
        assert_clean(
            &family_authentication_summary(
                FamilyCarrierForTest::Public { aliases: ALIASES },
                WIDTH,
                None,
            ),
            PUBLIC_EXACT,
            PUBLIC_PRE_REVERSE,
        );
        assert_clean(
            &family_authentication_summary(FamilyCarrierForTest::HiddenTransparent, WIDTH, None),
            HIDDEN_TRANSPARENT_EXACT,
            HIDDEN_TRANSPARENT_EXACT - 1,
        );
        assert_clean(
            &family_authentication_summary(FamilyCarrierForTest::HiddenIdentity, WIDTH, None),
            HIDDEN_IDENTITY_EXACT,
            HIDDEN_IDENTITY_EXACT - 1,
        );

        for omitted in [0, WIDTH - 1] {
            for (carrier, exact) in [
                (FamilyCarrierForTest::Public { aliases: 1 }, 3 * WIDTH + 2),
                (FamilyCarrierForTest::HiddenTransparent, 3 * WIDTH + 2),
            ] {
                let summary = family_authentication_summary(carrier, WIDTH, Some(omitted));
                let mut short = crate::interface::InterfaceConstraintBudget::with_limit(exact - 1);
                assert_eq!(
                    summary.authenticate(&mut TypeWorkBudget::default(), &mut short),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(short.used(), exact - 1);
                for _ in 0..2 {
                    let mut constraint =
                        crate::interface::InterfaceConstraintBudget::with_limit(exact);
                    assert_eq!(
                        summary.authenticate(&mut TypeWorkBudget::default(), &mut constraint),
                        Err(ResolvedBuildFailure::InvalidState),
                    );
                    assert_eq!(constraint.used(), exact);
                }
            }
        }

        const REVERSE_PRECHARGE_PREFIX: usize = 3 * WIDTH + 4;
        const REVERSE_EXACT: usize = REVERSE_PRECHARGE_PREFIX + WIDTH + 1;
        for constructor in [false, true] {
            let mut summary = family_authentication_summary(
                FamilyCarrierForTest::Public { aliases: 1 },
                WIDTH,
                None,
            );
            assert!(summary.remove_first_reverse_index_for_test(constructor));
            let mut short =
                crate::interface::InterfaceConstraintBudget::with_limit(REVERSE_EXACT - 1);
            assert_eq!(
                summary.authenticate(&mut TypeWorkBudget::default(), &mut short),
                Err(ResolvedBuildFailure::ConstraintResource),
            );
            assert_eq!(short.used(), REVERSE_PRECHARGE_PREFIX);
            for _ in 0..2 {
                let mut exact =
                    crate::interface::InterfaceConstraintBudget::with_limit(REVERSE_EXACT);
                assert_eq!(
                    summary.authenticate(&mut TypeWorkBudget::default(), &mut exact),
                    Err(ResolvedBuildFailure::InvalidState),
                );
                assert_eq!(exact.used(), REVERSE_EXACT);
            }
        }
    }

    #[test]
    fn nominal_identity_collection_has_exact_fallible_stack_and_index_work() {
        const DEPTH: usize = 32_768;
        const WIDTH: usize = 32_768;
        std::thread::Builder::new()
            .name("nominal-identity-collection".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                fn assert_exact(root: &Type, type_cells: usize, unique: usize, short_used: usize) {
                    let exact = type_cells
                        .checked_add(unique)
                        .expect("the collection formula should fit");
                    let mut short_output = HashSet::new();
                    let mut short = TypeWorkBudget::with_limit(exact - 1);
                    assert_eq!(
                        collect_nominal_identities(root, &mut short_output, &mut short),
                        Err(()),
                    );
                    assert_eq!(short.used(), short_used);
                    for _ in 0..2 {
                        let mut output = HashSet::new();
                        let mut budget = TypeWorkBudget::with_limit(exact);
                        collect_nominal_identities(root, &mut output, &mut budget)
                            .expect("the exact immutable type should remain reusable");
                        assert_eq!(budget.used(), exact);
                        assert_eq!(output.len(), unique);
                    }
                }

                let module = ModuleId::new(9_810);
                let repeated = NominalTypeId::new(module, 0);
                let mut deep = Type::Nominal(repeated);
                for _ in 0..DEPTH {
                    deep = Type::Application(Box::new(deep), Box::new(Type::Nominal(repeated)));
                }
                assert_exact(&deep, 2 * DEPTH + 1, 1, 2 * DEPTH + 1);
                discard_type_iteratively(deep);

                let mut deep_without_nominals = Type::Unit;
                for _ in 0..DEPTH {
                    deep_without_nominals =
                        Type::Forall(Box::new([]), Box::new(deep_without_nominals));
                }
                assert_exact(&deep_without_nominals, DEPTH + 1, 0, DEPTH);
                discard_type_iteratively(deep_without_nominals);

                let wide = Type::Tuple(
                    (0..WIDTH)
                        .map(|index| {
                            Type::Nominal(NominalTypeId::new(
                                module,
                                u32::try_from(index).expect("the wide identity should fit"),
                            ))
                        })
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                );
                assert_exact(&wide, WIDTH + 1, WIDTH, 2 * WIDTH);
                discard_type_iteratively(wide);

                let repeated_wide = Type::Tuple(
                    std::iter::repeat_n(Type::Nominal(repeated), WIDTH)
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                );
                assert_exact(&repeated_wide, WIDTH + 1, 1, WIDTH + 1);
                discard_type_iteratively(repeated_wide);

                let wide_without_nominals = Type::Tuple(
                    std::iter::repeat_n(Type::Unit, WIDTH)
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                );
                assert_exact(&wide_without_nominals, WIDTH + 1, 0, 1);
                discard_type_iteratively(wide_without_nominals);
            })
            .expect("the nominal-collection worker should spawn")
            .join()
            .expect("accepted and rejected collection staging must tear down iteratively");
    }

    #[test]
    fn withheld_constructor_counts_have_exact_shared_authentication_storage() {
        fn summary_with_withheld_families(
            width_per_owner: usize,
            shared_spelling: bool,
        ) -> ExportSummary {
            let source = SourceFile::new("withheld-family-authentication.ash", "family")
                .expect("the withheld-family source should fit");
            let span = source
                .span(ByteRange::new(0, 6).expect("the withheld range should be ordered"))
                .expect("the withheld span should fit");
            let module = ModuleId::new(9_820);
            let opaque = NominalTypeId::new(module, 0);
            let hidden = NominalTypeId::new(module, 1);
            let mut summary = ExportSummary::empty(module);
            summary.nominal_order.push("Opaque".to_owned());
            summary
                .nominal_names_by_id
                .insert(opaque, "Opaque".to_owned());
            summary.nominals.insert(
                "Opaque".to_owned(),
                ExportedType {
                    id: opaque,
                    parameter_count: 0,
                    constructor_count: width_per_owner,
                    parameters: Box::new([]),
                    constructors: Box::new([]),
                    access: ExportedTypeAccess::Opaque,
                    origin: Origin::Source(span),
                },
            );
            summary.hidden_nominal_order.push(hidden);
            summary.hidden_nominals.insert(
                hidden,
                ExportedHiddenType {
                    id: hidden,
                    parameter_count: 0,
                    constructor_count: width_per_owner,
                    parameters: Box::new([]),
                    constructors: Box::new([]),
                    access: ImportedTypeAccess::Hidden,
                    spelling: "Hidden".to_owned(),
                    display_is_private: true,
                    origin: Origin::Source(span),
                },
            );
            for (owner, kind, prefix) in [
                (opaque, WithheldExportKind::OpaqueConstructor, "OpaqueValue"),
                (hidden, WithheldExportKind::Private, "HiddenValue"),
            ] {
                for index in 0..width_per_owner {
                    let spelling = if shared_spelling {
                        "Seal".to_owned()
                    } else {
                        format!("{prefix}{index}")
                    };
                    let constructor_index = summary
                        .withheld
                        .entry(spelling.clone())
                        .or_default()
                        .insert_new(
                            WithheldNamespace::Constructor,
                            WithheldExport {
                                kind,
                                owner: Some(owner),
                                origin: Some(Origin::Source(span)),
                            },
                        );
                    summary.withheld_order.push(WithheldOrderEntry {
                        spelling,
                        namespace: WithheldNamespace::Constructor,
                        owner: Some(owner),
                        constructor_index,
                    });
                }
            }
            summary
        }

        const WIDTH_PER_OWNER: usize = 2;
        const OWNER_COUNT: usize = 2;
        const WITHHELD_COUNT: usize = OWNER_COUNT * WIDTH_PER_OWNER;
        // One fused public nominal name/order cell, one hidden nominal order cell,
        // One cell per withheld spelling bucket, two per entry (bijection +
        // count index), one canonical-carrier pre-scan plus two owner cells
        // (withheld relation + physical closure), and one public reverse index.
        const EXACT: usize = 2 + WITHHELD_COUNT + 2 * WITHHELD_COUNT + 3 * OWNER_COUNT + 1;
        let summary = summary_with_withheld_families(WIDTH_PER_OWNER, false);
        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(EXACT - 1);
        assert_eq!(
            summary.authenticate(&mut TypeWorkBudget::default(), &mut short),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(short.used(), EXACT - 1);
        for _ in 0..2 {
            let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(EXACT);
            summary
                .authenticate(&mut TypeWorkBudget::default(), &mut exact)
                .expect("the exact withheld families should remain reusable");
            assert_eq!(exact.used(), EXACT);
        }

        // Two owners may share one spelling bucket. The bucket coefficient is
        // therefore one, while both per-entry indexes and all canonical-owner
        // relations remain unchanged.
        const SHARED_WITHHELD_COUNT: usize = OWNER_COUNT;
        const SHARED_SPELLING_EXACT: usize =
            2 + 1 + 2 * SHARED_WITHHELD_COUNT + 3 * OWNER_COUNT + 1;
        let shared = summary_with_withheld_families(1, true);
        let mut shared_short =
            crate::interface::InterfaceConstraintBudget::with_limit(SHARED_SPELLING_EXACT - 1);
        assert_eq!(
            shared.authenticate(&mut TypeWorkBudget::default(), &mut shared_short),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(shared_short.used(), SHARED_SPELLING_EXACT - 1);
        for _ in 0..2 {
            let mut exact =
                crate::interface::InterfaceConstraintBudget::with_limit(SHARED_SPELLING_EXACT);
            shared
                .authenticate(&mut TypeWorkBudget::default(), &mut exact)
                .expect("the shared-spelling summary should remain reusable");
            assert_eq!(exact.used(), SHARED_SPELLING_EXACT);
        }

        let mut missing = summary_with_withheld_families(WIDTH_PER_OWNER, false);
        let removed = missing
            .withheld_order
            .pop()
            .expect("the malformed fixture should remove one family member");
        missing.withheld.remove(&removed.spelling);
        const MISSING_EXACT: usize = 2 + 3 * (WITHHELD_COUNT - 1) + 2 * OWNER_COUNT;
        const MISSING_SEMANTIC_PREFIX: usize = 2 + 3 * (WITHHELD_COUNT - 1) + OWNER_COUNT;
        let mut missing_short =
            crate::interface::InterfaceConstraintBudget::with_limit(MISSING_EXACT - 1);
        assert_eq!(
            missing.authenticate(&mut TypeWorkBudget::default(), &mut missing_short),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(missing_short.used(), MISSING_SEMANTIC_PREFIX);
        for _ in 0..2 {
            let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(MISSING_EXACT);
            assert_eq!(
                missing.authenticate(&mut TypeWorkBudget::default(), &mut exact),
                Err(ResolvedBuildFailure::InvalidState),
            );
            assert_eq!(exact.used(), MISSING_EXACT);
        }
    }

    #[derive(Clone, Copy, Debug)]
    enum InterfaceAuthenticationMutationForTest {
        None,
        MissingPublicName,
        BadPosition,
        BadMethodOwner,
    }

    fn interface_authentication_summary(
        mutation: InterfaceAuthenticationMutationForTest,
    ) -> ExportSummary {
        let source = SourceFile::new("interface-authentication.ash", "interfaces")
            .expect("the interface-authentication source should fit");
        let span = source
            .span(ByteRange::new(0, 10).expect("the interface range should be ordered"))
            .expect("the interface span should fit");
        let module = ModuleId::new(9_830);
        let hidden_module = ModuleId::new(9_831);
        let mut summary = ExportSummary::empty(module);
        let make_interface = |owner: ModuleId, index: u32, spelling: &str| {
            let id = InterfaceId::new(owner, index);
            let parameter = TypeVariableId::resolved(owner, index);
            CheckedInterfaceFact {
                id,
                spelling: spelling.to_owned(),
                parameter: ResolvedTypeVariable {
                    id: parameter,
                    spelling: "A".to_owned(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                },
                methods: Box::new([CheckedInterfaceMethodFact {
                    id: MethodId::new(id, 0),
                    spelling: format!("{spelling}Method"),
                    type_parameters: Box::new([]),
                    value_type: Type::Function(
                        Box::new(Type::Variable(parameter)),
                        Box::new(Type::Variable(parameter)),
                    ),
                    origin: Origin::Source(span),
                    span,
                }]),
                method_binder_authorities: Box::new([MethodBinderAuthority {
                    method: MethodId::new(id, 0),
                    parameters: Box::new([]),
                }]),
                origin: Origin::Source(span),
                span,
            }
        };
        summary.interfaces.push(make_interface(module, 0, "First"));
        summary.interfaces.push(make_interface(module, 1, "Second"));
        for (position, interface) in summary.interfaces.iter().enumerate() {
            summary.interface_positions.insert(interface.id, position);
        }
        summary
            .hidden_interfaces
            .push(make_interface(hidden_module, 0, "Hidden"));

        for (spelling, interface) in [
            ("First", summary.interfaces[0].id),
            ("FirstAlias", summary.interfaces[0].id),
            ("Second", summary.interfaces[1].id),
        ] {
            if matches!(
                mutation,
                InterfaceAuthenticationMutationForTest::MissingPublicName
            ) && spelling == "Second"
            {
                continue;
            }
            summary.interface_name_order.push(spelling.to_owned());
            summary
                .interface_names
                .insert(spelling.to_owned(), interface);
        }
        for (spelling, method) in [
            ("first", summary.interfaces[0].methods[0].id),
            ("second", summary.interfaces[1].methods[0].id),
        ] {
            summary.method_name_order.push(spelling.to_owned());
            summary.method_names.insert(spelling.to_owned(), method);
        }
        match mutation {
            InterfaceAuthenticationMutationForTest::BadPosition => {
                summary
                    .interface_positions
                    .insert(summary.interfaces[1].id, usize::MAX);
            }
            InterfaceAuthenticationMutationForTest::BadMethodOwner => {
                summary.method_names.insert(
                    "second".to_owned(),
                    MethodId::new(InterfaceId::new(hidden_module, 99), 0),
                );
            }
            InterfaceAuthenticationMutationForTest::None
            | InterfaceAuthenticationMutationForTest::MissingPublicName => {}
        }
        summary
    }

    #[test]
    fn interface_summary_indexes_have_exact_constraint_work_and_failure_precedence() {
        const PUBLIC: usize = 2;
        const HIDDEN: usize = 1;
        const NAMES: usize = 3;
        const METHODS: usize = 2;
        // The fused order/namespace indexes cost N+M. ConstraintWork then owns
        // I+H fact slots and private method-authority rows, N named aliases, I
        // public reverse relations, and M method-owner relations. Each
        // method's free-variable closure, outer Function shape, and Kind are
        // authenticated on TypeWork.
        const EXACT: usize =
            NAMES + METHODS + 2 * PUBLIC + HIDDEN + NAMES + METHODS + PUBLIC + HIDDEN;
        let summary =
            interface_authentication_summary(InterfaceAuthenticationMutationForTest::None);
        let mut measured = crate::interface::InterfaceConstraintBudget::default();
        summary
            .authenticate(&mut TypeWorkBudget::default(), &mut measured)
            .expect("the unbounded interface summary should authenticate");
        assert_eq!(measured.used(), EXACT);
        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(EXACT - 1);
        assert_eq!(
            summary.authenticate(&mut TypeWorkBudget::default(), &mut short),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(short.used(), EXACT - (PUBLIC + HIDDEN + 1));
        for _ in 0..2 {
            let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(EXACT);
            summary
                .authenticate(&mut TypeWorkBudget::default(), &mut exact)
                .expect("the exact interface summary should remain reusable");
            assert_eq!(exact.used(), EXACT);
        }

        for (mutation, exact, short_used) in [
            (InterfaceAuthenticationMutationForTest::BadPosition, 9, 8),
            (
                InterfaceAuthenticationMutationForTest::MissingPublicName,
                16,
                12,
            ),
            (
                InterfaceAuthenticationMutationForTest::BadMethodOwner,
                18,
                14,
            ),
        ] {
            let summary = interface_authentication_summary(mutation);
            let mut short = crate::interface::InterfaceConstraintBudget::with_limit(exact - 1);
            assert_eq!(
                summary.authenticate(&mut TypeWorkBudget::default(), &mut short),
                Err(ResolvedBuildFailure::ConstraintResource),
            );
            assert_eq!(short.used(), short_used, "{mutation:?}");
            for _ in 0..2 {
                let mut exact_budget =
                    crate::interface::InterfaceConstraintBudget::with_limit(exact);
                assert_eq!(
                    summary.authenticate(&mut TypeWorkBudget::default(), &mut exact_budget),
                    Err(ResolvedBuildFailure::InvalidState),
                    "{mutation:?}",
                );
                assert_eq!(exact_budget.used(), exact);
            }
        }
    }

    fn interface_summary_with_duplicate_global_requirements() -> ExportSummary {
        let mut summary =
            interface_authentication_summary(InterfaceAuthenticationMutationForTest::None);
        let binder = BinderId::resolved(summary.module, 0);
        let interface = summary.interfaces[0].id;
        let span = summary.interfaces[0].span;
        let requirement = |declaration| CheckedRequirement {
            id: RequirementId::new(
                crate::interface::RequirementOwner::Global(binder),
                declaration,
            ),
            interface,
            argument: Type::Unit,
            origin: Origin::Source(span),
            span,
        };
        summary.term_order.push("duplicate".to_owned());
        summary.terms.insert(
            "duplicate".to_owned(),
            ExportedGlobal {
                binder,
                scheme: ConstrainedScheme {
                    type_parameters: Box::new([]),
                    requirements: Box::new([requirement(0), requirement(1)]),
                    value_type: Type::Unit,
                },
                origin: Origin::Source(span),
            },
        );
        summary
    }

    #[derive(Clone, Copy, Debug)]
    enum PolymorphicMethodSummaryMutationForTest {
        Missing,
        Extra,
        Duplicate,
        Reordered,
        WrongKind,
        WrongOwner,
        WrongOrigin,
        WrongSpelling,
        FreeBinder,
        NestedNonMethodScheme,
    }

    fn polymorphic_method_summary(
        mutation: Option<PolymorphicMethodSummaryMutationForTest>,
    ) -> ExportSummary {
        let source = SourceFile::new("method-summary.ash", "Functor F map A B")
            .expect("the method-summary source should fit");
        let interface_span = source
            .span(ByteRange::new(0, 7).expect("the interface range should be ordered"))
            .expect("the interface span should fit");
        let method_span = source
            .span(ByteRange::new(10, 13).expect("the method range should be ordered"))
            .expect("the method span should fit");
        let first_span = source
            .span(ByteRange::new(14, 15).expect("the first binder range should be ordered"))
            .expect("the first binder span should fit");
        let second_span = source
            .span(ByteRange::new(16, 17).expect("the second binder range should be ordered"))
            .expect("the second binder span should fit");
        let module = ModuleId::new(9_832);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let first = TypeVariableId::resolved(module, 1);
        let second = TypeVariableId::resolved(module, 2);
        let apply = |function, argument| Type::Application(Box::new(function), Box::new(argument));
        let method_type = Type::Function(
            Box::new(Type::Tuple(
                vec![
                    Type::Function(
                        Box::new(Type::Variable(first)),
                        Box::new(Type::Variable(second)),
                    ),
                    apply(Type::Variable(interface_parameter), Type::Variable(first)),
                ]
                .into_boxed_slice(),
            )),
            Box::new(apply(
                Type::Variable(interface_parameter),
                Type::Variable(second),
            )),
        );
        let mut summary = ExportSummary::empty(module);
        summary.interfaces.push(CheckedInterfaceFact {
            id: interface,
            spelling: "Functor".to_owned(),
            parameter: ResolvedTypeVariable {
                id: interface_parameter,
                spelling: "F".to_owned(),
                kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                origin: Origin::Source(interface_span),
            },
            methods: Box::new([CheckedInterfaceMethodFact {
                id: method,
                spelling: "map".to_owned(),
                type_parameters: Box::new([
                    ResolvedTypeVariable {
                        id: first,
                        spelling: "A".to_owned(),
                        kind: Kind::Type,
                        origin: Origin::Source(first_span),
                    },
                    ResolvedTypeVariable {
                        id: second,
                        spelling: "B".to_owned(),
                        kind: Kind::Type,
                        origin: Origin::Source(second_span),
                    },
                ]),
                value_type: method_type,
                origin: Origin::Source(method_span),
                span: method_span,
            }]),
            method_binder_authorities: Box::new([MethodBinderAuthority {
                method,
                parameters: Box::new([
                    ResolvedTypeVariable {
                        id: first,
                        spelling: "A".to_owned(),
                        kind: Kind::Type,
                        origin: Origin::Source(first_span),
                    },
                    ResolvedTypeVariable {
                        id: second,
                        spelling: "B".to_owned(),
                        kind: Kind::Type,
                        origin: Origin::Source(second_span),
                    },
                ]),
            }]),
            origin: Origin::Source(interface_span),
            span: interface_span,
        });
        summary.interface_positions.insert(interface, 0);
        summary.interface_name_order.push("Functor".to_owned());
        summary
            .interface_names
            .insert("Functor".to_owned(), interface);
        summary.method_name_order.push("map".to_owned());
        summary.method_names.insert("map".to_owned(), method);
        let method = &mut summary.interfaces[0].methods[0];
        match mutation {
            None => {}
            Some(PolymorphicMethodSummaryMutationForTest::Missing) => {
                let mut parameters = std::mem::take(&mut method.type_parameters).into_vec();
                parameters.remove(0);
                method.type_parameters = parameters.into_boxed_slice();
            }
            Some(PolymorphicMethodSummaryMutationForTest::Extra) => {
                let mut parameters = std::mem::take(&mut method.type_parameters).into_vec();
                parameters.push(ResolvedTypeVariable {
                    id: TypeVariableId::resolved(module, 3),
                    spelling: "C".to_owned(),
                    kind: Kind::Type,
                    origin: Origin::Source(second_span),
                });
                method.type_parameters = parameters.into_boxed_slice();
            }
            Some(PolymorphicMethodSummaryMutationForTest::Duplicate) => {
                method.type_parameters[1].id = method.type_parameters[0].id;
            }
            Some(PolymorphicMethodSummaryMutationForTest::Reordered) => {
                method.type_parameters.swap(0, 1);
            }
            Some(PolymorphicMethodSummaryMutationForTest::WrongKind) => {
                method.type_parameters[0].kind =
                    Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
            }
            Some(PolymorphicMethodSummaryMutationForTest::WrongOwner) => {
                method.type_parameters[0].id =
                    TypeVariableId::resolved(ModuleId::new(u32::MAX - 1), 1);
            }
            Some(PolymorphicMethodSummaryMutationForTest::WrongOrigin) => {
                method.type_parameters[0].origin = Origin::Generated {
                    cause: Box::new(Origin::Source(first_span)),
                    reason: crate::source::GeneratedReason::ConstantFolding,
                };
            }
            Some(PolymorphicMethodSummaryMutationForTest::WrongSpelling) => {
                method.type_parameters[0].spelling = "Forged".to_owned();
            }
            Some(PolymorphicMethodSummaryMutationForTest::FreeBinder) => {
                discard_type_iteratively(std::mem::replace(
                    &mut method.value_type,
                    Type::Function(
                        Box::new(Type::Variable(TypeVariableId::resolved(module, 99))),
                        Box::new(Type::Unit),
                    ),
                ));
            }
            Some(PolymorphicMethodSummaryMutationForTest::NestedNonMethodScheme) => {
                let binder = BinderId::resolved(module, 0);
                summary.term_order.push("forged".to_owned());
                summary.terms.insert(
                    "forged".to_owned(),
                    ExportedGlobal {
                        binder,
                        scheme: ConstrainedScheme {
                            type_parameters: Box::new([]),
                            requirements: Box::new([]),
                            value_type: Type::Forall(
                                Box::new([(TypeVariableId::resolved(module, 98), Kind::Type)]),
                                Box::new(Type::Unit),
                            ),
                        },
                        origin: Origin::Source(interface_span),
                    },
                );
            }
        }
        summary
    }

    #[test]
    fn polymorphic_method_summary_rejects_complete_binder_tampering_matrix() {
        polymorphic_method_summary(None)
            .authenticate(
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            )
            .expect("the canonical polymorphic method summary should authenticate");

        for mutation in [
            PolymorphicMethodSummaryMutationForTest::Missing,
            PolymorphicMethodSummaryMutationForTest::Extra,
            PolymorphicMethodSummaryMutationForTest::Duplicate,
            PolymorphicMethodSummaryMutationForTest::Reordered,
            PolymorphicMethodSummaryMutationForTest::WrongKind,
            PolymorphicMethodSummaryMutationForTest::WrongOwner,
            PolymorphicMethodSummaryMutationForTest::WrongOrigin,
            PolymorphicMethodSummaryMutationForTest::WrongSpelling,
            PolymorphicMethodSummaryMutationForTest::FreeBinder,
            PolymorphicMethodSummaryMutationForTest::NestedNonMethodScheme,
        ] {
            assert_eq!(
                polymorphic_method_summary(Some(mutation)).authenticate(
                    &mut TypeWorkBudget::default(),
                    &mut crate::interface::InterfaceConstraintBudget::default(),
                ),
                Err(ResolvedBuildFailure::InvalidState),
                "{mutation:?}",
            );
        }
    }

    #[test]
    fn freeze_rejects_coherently_forged_checked_method_binder_before_publication() {
        let source = SourceFile::new("coherent-method-forgery.ash", "interface Boxed<I>")
            .expect("the coherent-forgery source should fit");
        let span = source
            .span(ByteRange::new(0, 18).expect("the coherent-forgery range should be ordered"))
            .expect("the coherent-forgery span should fit");
        let module = ModuleId::new(9_833);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let canonical = TypeVariableId::resolved(module, 1);
        let forged = TypeVariableId::resolved(module, 99);
        let resolved_interface = ResolvedInterfaceDeclaration {
            id: interface,
            public: true,
            spelling: "Boxed".to_owned(),
            parameter: ResolvedTypeVariable {
                id: interface_parameter,
                spelling: "I".to_owned(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
            methods: Box::new([ResolvedInterfaceMethod {
                id: method,
                spelling: "keep".to_owned(),
                annotation: ResolvedType {
                    ty: Type::Function(
                        Box::new(Type::Variable(canonical)),
                        Box::new(Type::Variable(interface_parameter)),
                    ),
                    provenance: ResolvedTypeProvenance::new(
                        vec![ResolvedTypeProvenanceNode::Fact(span)],
                        0,
                    ),
                    origin: Origin::Source(span),
                    span,
                },
                type_parameters: Box::new([ResolvedTypeVariable {
                    id: canonical,
                    spelling: "A".to_owned(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                }]),
                has_explicit_type_parameters: true,
                origin: Origin::Source(span),
                span,
            }]),
            origin: Origin::Source(span),
            span,
        };
        let forged_origin = Origin::Generated {
            cause: Box::new(Origin::Source(span)),
            reason: crate::source::GeneratedReason::ConstantFolding,
        };
        let checked = [CheckedInterfaceFact {
            id: interface,
            spelling: "Boxed".to_owned(),
            parameter: resolved_interface.parameter.clone(),
            methods: Box::new([CheckedInterfaceMethodFact {
                id: method,
                spelling: "keep".to_owned(),
                type_parameters: Box::new([ResolvedTypeVariable {
                    id: forged,
                    spelling: "Forged".to_owned(),
                    kind: Kind::Type,
                    origin: forged_origin,
                }]),
                value_type: Type::Function(
                    Box::new(Type::Variable(forged)),
                    Box::new(Type::Variable(interface_parameter)),
                ),
                origin: Origin::Source(span),
                span,
            }]),
            method_binder_authorities: Box::new([MethodBinderAuthority {
                method,
                parameters: Box::new([ResolvedTypeVariable {
                    id: canonical,
                    spelling: "A".to_owned(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                }]),
            }]),
            origin: Origin::Source(span),
            span,
        }];
        let mut export_candidate = ResolvedExportCandidate::default();
        export_candidate
            .try_insert_interface(
                "Boxed".to_owned(),
                CandidateInterface {
                    id: interface,
                    source: CandidateFactSource::Local,
                },
                &mut TypeWorkBudget::default(),
            )
            .expect("the interface export candidate should fit");
        export_candidate
            .try_insert_method(
                "keep".to_owned(),
                CandidateMethod {
                    id: method,
                    source: CandidateFactSource::Local,
                },
                &mut TypeWorkBudget::default(),
            )
            .expect("the method export candidate should fit");
        let resolved = ResolvedModule::new(ResolvedModuleParts {
            module,
            registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
            imported: ImportedFacts::default(),
            direct_dependencies: Vec::new(),
            declaration_order: vec![ResolvedDeclarationIndex::Interface(0)],
            interfaces: vec![resolved_interface],
            implementations: Vec::new(),
            definitions: Vec::new(),
            export_candidate,
            span,
        });

        assert_eq!(
            ExportSummary::freeze(
                &resolved,
                &[],
                &checked,
                &[],
                &[],
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            ),
            Err(ResolvedBuildFailure::InvalidState),
            "the checked mirror must not mint its own method-binder authority",
        );
    }

    #[test]
    fn method_binder_authority_retention_has_exact_independent_ledgers() {
        // One private row is graph storage. Each of the two binder copies owns
        // one record plus one `Type` Kind node in TypeWork.
        const EXACT_CONSTRAINT_WORK: usize = 1;
        const EXACT_TYPE_WORK: usize = 2 * (1 + 1);
        let summary = polymorphic_method_summary(None);

        assert_eq!(
            clone_method_binder_authority_rows(
                &summary.interfaces[0].method_binder_authorities,
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
                &mut crate::interface::InterfaceConstraintBudget::with_limit(
                    EXACT_CONSTRAINT_WORK - 1,
                ),
            ),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(
            clone_method_binder_authority_rows(
                &summary.interfaces[0].method_binder_authorities,
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1),
                &mut crate::interface::InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK,),
            ),
            Err(ResolvedBuildFailure::TypeResource),
        );
        let mut exact_type = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        let mut exact_constraint =
            crate::interface::InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let authorities = clone_method_binder_authority_rows(
            &summary.interfaces[0].method_binder_authorities,
            &mut exact_type,
            &mut exact_constraint,
        )
        .expect("the exact authority-retention ledgers should fit");
        assert_eq!(authorities.len(), 1);
        assert_eq!(authorities[0].parameters.len(), 2);
        assert_eq!(exact_type.used(), EXACT_TYPE_WORK);
        assert_eq!(exact_constraint.used(), EXACT_CONSTRAINT_WORK);
    }

    #[test]
    fn monomorphic_method_still_requires_one_private_authority_row() {
        let mut summary =
            interface_authentication_summary(InterfaceAuthenticationMutationForTest::None);
        assert!(
            summary.interfaces[0].methods[0]
                .type_parameters()
                .is_empty()
        );
        summary.interfaces[0].method_binder_authorities = Box::new([]);

        assert_eq!(
            summary.authenticate(
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            ),
            Err(ResolvedBuildFailure::InvalidState),
        );
    }

    #[test]
    fn private_method_authority_discards_deep_binder_origin_iteratively() {
        std::thread::Builder::new()
            .name("deep-private-method-authority-drop".to_owned())
            .stack_size(64 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_768;
                let source = SourceFile::new("deep-authority.ash", "authority")
                    .expect("the deep-authority source should fit");
                let module = ModuleId::new(9_834);
                drop(MethodBinderAuthority {
                    method: MethodId::new(InterfaceId::new(module, 0), 0),
                    parameters: Box::new([ResolvedTypeVariable {
                        id: TypeVariableId::resolved(module, 0),
                        spelling: "A".to_owned(),
                        kind: Kind::Type,
                        origin: generated_origin(&source, DEPTH),
                    }]),
                });
            })
            .expect("the deep private-authority drop thread should spawn")
            .join()
            .expect("private authority teardown should remain stack-safe");
    }

    #[test]
    fn raw_global_duplicate_requirements_reach_summary_admission_exactly_and_atomically() {
        // The interface carrier costs 18 cells. The global adds one expression,
        // canonical-global, and term-binder cell; six closed-type collection
        // cells; two first-group index cells; and two Unit comparison cells.
        const EXACT_CONSTRAINT_WORK: usize = 18 + 3 + 6 + 2 + 2;
        let summary = interface_summary_with_duplicate_global_requirements();

        let mut measured = crate::interface::InterfaceConstraintBudget::default();
        assert_eq!(
            summary.authenticate(&mut TypeWorkBudget::default(), &mut measured),
            Err(ResolvedBuildFailure::InvalidState),
        );
        assert_eq!(measured.used(), EXACT_CONSTRAINT_WORK);

        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(
            EXACT_CONSTRAINT_WORK.saturating_sub(1),
        );
        assert_eq!(
            summary.authenticate(&mut TypeWorkBudget::default(), &mut short),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(short.used(), EXACT_CONSTRAINT_WORK - 1);

        for _ in 0..2 {
            let mut exact =
                crate::interface::InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
            assert_eq!(
                summary.authenticate(&mut TypeWorkBudget::default(), &mut exact),
                Err(ResolvedBuildFailure::InvalidState),
            );
            assert_eq!(exact.used(), EXACT_CONSTRAINT_WORK);
        }
    }

    fn interface_summary_with_local_implementation(bad_position: bool) -> ExportSummary {
        let mut summary =
            interface_authentication_summary(InterfaceAuthenticationMutationForTest::None);
        let interface = &summary.interfaces[0];
        let id = ImplId::new(summary.module, 0);
        let method = interface.methods[0].id;
        let span = interface.span;
        summary
            .implementations
            .push(AuthorizedImplementationFact::local_for_test(
                CheckedImplementationFact {
                    id,
                    interface: interface.id,
                    head_parameters: Box::new([]),
                    argument: Type::Int,
                    prerequisites: Box::new([]),
                    methods: Box::new([CheckedImplementationMethodFact {
                        id: ImplMethodId::new(id, method),
                        method,
                        binder: BinderId::resolved(summary.module, 0),
                        scheme: ConstrainedScheme {
                            type_parameters: Box::new([]),
                            requirements: Box::new([]),
                            value_type: Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                        },
                        head_type_parameter_count: 0,
                        origin: Origin::Source(span),
                        span,
                    }]),
                    origin: Origin::Source(span),
                    span,
                },
            ));
        summary
            .implementation_positions
            .insert(id, if bad_position { usize::MAX } else { 0 });
        summary
    }

    #[test]
    fn implementation_summary_authentication_has_exact_independent_ledgers() {
        // The interface-only Constraint fixture costs 18. One implementation adds one
        // implementation-count scan, one G+M term-binder slot, one local
        // authorization method cell, two exact ground-head cells, ten fused
        // interface-method substitution cells, and two implementation-index
        // cells.
        const EXACT: usize = 18 + 1 + 1 + 1 + 2 + 10 + 2;
        const TYPE_WORK: usize = 58;
        let summary = interface_summary_with_local_implementation(false);
        let mut short_type = TypeWorkBudget::with_limit(TYPE_WORK);
        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(EXACT - 1);
        assert_eq!(
            summary.authenticate(&mut short_type, &mut short),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(short.used(), EXACT - 2);
        assert_eq!(short_type.used(), TYPE_WORK);

        let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
        let mut type_short_constraint =
            crate::interface::InterfaceConstraintBudget::with_limit(EXACT);
        assert_eq!(
            summary.authenticate(&mut type_short, &mut type_short_constraint),
            Err(ResolvedBuildFailure::TypeResource),
        );
        assert_eq!(type_short.used(), TYPE_WORK - 1);
        assert_eq!(
            type_short_constraint.used(),
            33,
            "Type failure follows every carrier comparison and precedes final index retention",
        );
        for _ in 0..2 {
            let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
            let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(EXACT);
            summary
                .authenticate(&mut type_work, &mut exact)
                .expect("the exact implementation summary should remain reusable");
            assert_eq!(exact.used(), EXACT);
            assert_eq!(type_work.used(), TYPE_WORK);
        }

        // Before method-shape checking, the two new aggregate cells and the
        // authorization cell are all charged. A malformed position then owns
        // InvalidState; one-short cannot reach that semantic check.
        const BAD_POSITION_EXACT: usize = 18 + 1 + 1 + 1;
        let malformed = interface_summary_with_local_implementation(true);
        let mut short =
            crate::interface::InterfaceConstraintBudget::with_limit(BAD_POSITION_EXACT - 1);
        assert_eq!(
            malformed.authenticate(&mut TypeWorkBudget::default(), &mut short),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(short.used(), BAD_POSITION_EXACT - 1);
        for _ in 0..2 {
            let mut exact =
                crate::interface::InterfaceConstraintBudget::with_limit(BAD_POSITION_EXACT);
            assert_eq!(
                malformed.authenticate(&mut TypeWorkBudget::default(), &mut exact),
                Err(ResolvedBuildFailure::InvalidState),
            );
            assert_eq!(exact.used(), BAD_POSITION_EXACT);
        }
    }

    #[derive(Clone, Copy)]
    enum SummaryAliasCarrierForTest {
        Nominal,
        Global,
        Constructor,
    }

    #[derive(Clone, Copy)]
    enum SummaryAliasConflictForTest {
        None,
        FirstField,
        LastField,
    }

    fn deep_alias_origin(span: Span, depth: usize) -> Origin {
        let mut origin = Origin::Source(span);
        for _ in 0..depth {
            origin = Origin::Generated {
                cause: Box::new(origin),
                reason: GeneratedReason::TypeChecking,
            };
        }
        origin
    }

    fn summary_with_public_aliases(
        carrier: SummaryAliasCarrierForTest,
        aliases: usize,
        conflict: SummaryAliasConflictForTest,
        depth: usize,
    ) -> ExportSummary {
        let source = SourceFile::new("summary-alias.ash", "first second")
            .expect("the summary-alias source should fit");
        let first_span = source
            .span(ByteRange::new(0, 5).expect("the first range should be ordered"))
            .expect("the first span should fit");
        let last_span = source
            .span(ByteRange::new(6, 12).expect("the last range should be ordered"))
            .expect("the last span should fit");
        let module = ModuleId::new(9_840);
        let parameter = TypeVariableId::resolved(module, 0);
        let nominal = NominalTypeId::new(module, 0);
        let constructor = ConstructorId::new(nominal, 0);
        let binder = BinderId::resolved(module, 0);
        let mut summary = ExportSummary::empty(module);
        let alias_origin = |index| {
            let span = if index == 1 && matches!(conflict, SummaryAliasConflictForTest::LastField) {
                last_span
            } else {
                first_span
            };
            deep_alias_origin(span, depth)
        };
        let parameter_for = |index| {
            if index == 1 && matches!(conflict, SummaryAliasConflictForTest::FirstField) {
                TypeVariableId::resolved(module, 1)
            } else {
                parameter
            }
        };

        match carrier {
            SummaryAliasCarrierForTest::Global => {
                for index in 0..aliases {
                    let spelling = format!("global{index}");
                    summary.term_order.push(spelling.clone());
                    summary.terms.insert(
                        spelling,
                        ExportedGlobal {
                            binder,
                            scheme: ConstrainedScheme {
                                type_parameters: Box::new([]),
                                requirements: Box::new([]),
                                value_type: if index == 1
                                    && matches!(conflict, SummaryAliasConflictForTest::FirstField)
                                {
                                    Type::Int
                                } else {
                                    Type::Unit
                                },
                            },
                            origin: alias_origin(index),
                        },
                    );
                }
            }
            SummaryAliasCarrierForTest::Nominal | SummaryAliasCarrierForTest::Constructor => {
                let nominal_aliases = if matches!(carrier, SummaryAliasCarrierForTest::Nominal) {
                    aliases
                } else {
                    1
                };
                for index in 0..nominal_aliases {
                    let spelling = format!("Nominal{index}");
                    let retained_parameter = parameter_for(index);
                    summary.nominal_order.push(spelling.clone());
                    summary.nominals.insert(
                        spelling.clone(),
                        ExportedType {
                            id: nominal,
                            parameter_count: 1,
                            constructor_count: 1,
                            parameters: Box::new([ResolvedTypeVariable {
                                id: retained_parameter,
                                spelling: "A".to_owned(),
                                kind: Kind::Type,
                                origin: Origin::Source(first_span),
                            }]),
                            constructors: Box::new([constructor]),
                            access: ExportedTypeAccess::Transparent,
                            origin: if matches!(carrier, SummaryAliasCarrierForTest::Nominal) {
                                alias_origin(index)
                            } else {
                                Origin::Source(first_span)
                            },
                        },
                    );
                    summary
                        .nominal_names_by_id
                        .entry(nominal)
                        .or_insert(spelling);
                }

                let constructor_aliases =
                    if matches!(carrier, SummaryAliasCarrierForTest::Constructor) {
                        aliases
                    } else {
                        1
                    };
                for index in 0..constructor_aliases {
                    let spelling = format!("Make{index}");
                    let retained_parameter = parameter_for(index);
                    summary.constructor_order.push(spelling.clone());
                    summary.constructors.insert(
                        spelling.clone(),
                        ExportedConstructor {
                            id: constructor,
                            spelling: "Make".to_owned(),
                            payload: None,
                            scheme: ConstrainedScheme {
                                type_parameters: Box::new([(retained_parameter, Kind::Type)]),
                                requirements: Box::new([]),
                                value_type: Type::Application(
                                    Box::new(Type::Nominal(nominal)),
                                    Box::new(Type::Variable(retained_parameter)),
                                ),
                            },
                            origin: if matches!(carrier, SummaryAliasCarrierForTest::Constructor) {
                                alias_origin(index)
                            } else {
                                Origin::Source(first_span)
                            },
                        },
                    );
                    summary
                        .constructor_names_by_id
                        .entry(constructor)
                        .or_insert(spelling);
                }
            }
        }
        summary
    }

    #[test]
    fn duplicate_public_summary_aliases_compare_only_on_constraint_work() {
        const DEPTH: usize = 32_768;
        std::thread::Builder::new()
            .name("duplicate-public-summary-aliases".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                // Global double: two fused order/collision cells + four canonical
                // and binder-index cells + two Unit-scheme cells + D+1 Origin
                // cells + two canonical Unit binder-scan cells = D+11.
                // Nominal double: four fused order/collision + two carrier + two
                // family + five parameter/mirror cells + D+1 Origin + one each for
                // withheld relation, physical fact, and closure + three
                // reverse-index cells = D+19.
                // Constructor double: three fused order/collision + one carrier + one
                // family + one withheld relation + two physical carriers +
                // ten scheme/mirror cells + D+1 Origin + one closure + three
                // reverse-index cells = D+23. The final three-cell reverse
                // batches explain the nominal/constructor D+16/D+20 C-short
                // prefixes.
                for (carrier, single_constraint, double_constraint, short_used, early, late) in [
                    (
                        SummaryAliasCarrierForTest::Global,
                        5,
                        DEPTH + 11,
                        DEPTH + 10,
                        8,
                        DEPTH + 9,
                    ),
                    (
                        SummaryAliasCarrierForTest::Nominal,
                        11,
                        DEPTH + 19,
                        DEPTH + 16,
                        8,
                        DEPTH + 11,
                    ),
                    (
                        SummaryAliasCarrierForTest::Constructor,
                        11,
                        DEPTH + 23,
                        DEPTH + 20,
                        11,
                        DEPTH + 19,
                    ),
                ] {
                    let single = summary_with_public_aliases(
                        carrier,
                        1,
                        SummaryAliasConflictForTest::None,
                        DEPTH,
                    );
                    let mut single_type = TypeWorkBudget::unbounded();
                    let mut single_graph = crate::interface::InterfaceConstraintBudget::default();
                    single
                        .authenticate(&mut single_type, &mut single_graph)
                        .expect("the defining alias fact should authenticate");
                    assert_eq!(single_graph.used(), single_constraint);
                    let retained_type_work = single_type.used();

                    let double = summary_with_public_aliases(
                        carrier,
                        2,
                        SummaryAliasConflictForTest::None,
                        DEPTH,
                    );
                    let mut short_type = TypeWorkBudget::with_limit(retained_type_work);
                    let mut short_graph = crate::interface::InterfaceConstraintBudget::with_limit(
                        double_constraint - 1,
                    );
                    assert_eq!(
                        double.authenticate(&mut short_type, &mut short_graph),
                        Err(ResolvedBuildFailure::ConstraintResource),
                    );
                    assert_eq!(short_graph.used(), short_used);
                    for _ in 0..2 {
                        let mut exact_type = TypeWorkBudget::with_limit(retained_type_work);
                        let mut exact_graph =
                            crate::interface::InterfaceConstraintBudget::with_limit(
                                double_constraint,
                            );
                        double
                            .authenticate(&mut exact_type, &mut exact_graph)
                            .expect("an identical alias should add no retained Type work");
                        assert_eq!(exact_type.used(), retained_type_work);
                        assert_eq!(exact_graph.used(), double_constraint);
                    }

                    for (conflict, exact) in [
                        (SummaryAliasConflictForTest::FirstField, early),
                        (SummaryAliasConflictForTest::LastField, late),
                    ] {
                        let conflicting = summary_with_public_aliases(carrier, 2, conflict, DEPTH);
                        let mut short_type = TypeWorkBudget::with_limit(retained_type_work);
                        let mut short_graph =
                            crate::interface::InterfaceConstraintBudget::with_limit(exact - 1);
                        assert_eq!(
                            conflicting.authenticate(&mut short_type, &mut short_graph),
                            Err(ResolvedBuildFailure::ConstraintResource),
                        );
                        assert_eq!(short_graph.used(), exact - 1);
                        for _ in 0..2 {
                            let mut exact_type = TypeWorkBudget::with_limit(retained_type_work);
                            let mut exact_graph =
                                crate::interface::InterfaceConstraintBudget::with_limit(exact);
                            assert_eq!(
                                conflicting.authenticate(&mut exact_type, &mut exact_graph),
                                Err(ResolvedBuildFailure::InvalidState),
                            );
                            assert_eq!(exact_graph.used(), exact);
                        }
                    }
                }
            })
            .expect("the duplicate-alias worker should spawn")
            .join()
            .expect("accepted and rejected deep aliases must tear down iteratively");
    }

    #[test]
    #[allow(clippy::borrowed_box)]
    fn linked_constructor_carriers_end_the_physical_summary_scheme_lifecycle() {
        // Exhaustive borrow destructures intentionally omit `..`: any new
        // post-check field must be classified here before the linked boundary
        // can acquire another independently retained constructor-scheme copy.
        fn group_fields(group: &ResolvedModuleGroup) {
            let ResolvedModuleGroup {
                module,
                direct_dependencies,
                declaration_order,
                interfaces,
                implementations,
                definitions,
                available_implementations,
                public_implementations,
                schemes,
                checked_interfaces,
                checked_implementations,
                interface_facts,
                implementation_facts,
                span,
            } = group;
            let _ = (
                module,
                direct_dependencies,
                declaration_order,
                interfaces,
                implementations,
                definitions,
                available_implementations,
                public_implementations,
                schemes,
                checked_interfaces,
                checked_implementations,
                interface_facts,
                implementation_facts,
                span,
            );
        }

        fn program_fields(program: &ResolvedModuleProgram) {
            let ResolvedModuleProgram {
                registry,
                groups,
                entry,
                result,
            } = program;
            let registry: &Arc<ResolvedRegistry> = registry;
            registry_fields(registry.as_ref());
            let groups: &Box<[ResolvedModuleGroup]> = groups;
            for group in groups {
                group_fields(group);
            }
            let _ = (registry, groups, entry, result);
        }

        fn linked_constructor_fields(constructor: &ResolvedConstructor) {
            let ResolvedConstructor {
                id,
                owner,
                spelling,
                payload,
                origin,
            } = constructor;
            let _ = (id, owner, spelling, payload, origin);
        }

        fn registry_fields(registry: &ResolvedRegistry) {
            let ResolvedRegistry {
                nominals,
                constructors,
                nominal_positions,
                constructor_positions,
                nominal_parameters,
                type_variables,
                global_parameter_rows,
                global_parameter_positions,
                abstract_nominal_names,
                abstract_nominal_kinds,
            } = registry;
            let global_parameter_rows: &Box<[ResolvedGlobalParameterRow]> = global_parameter_rows;
            for row in global_parameter_rows {
                let ResolvedGlobalParameterRow { owner, parameters } = row;
                let _ = (owner, parameters);
            }
            let constructors: &Box<[ResolvedConstructor]> = constructors;
            for constructor in constructors {
                linked_constructor_fields(constructor);
            }
            let _ = (
                nominals,
                constructors,
                nominal_positions,
                constructor_positions,
                nominal_parameters,
                type_variables,
                global_parameter_rows,
                global_parameter_positions,
                abstract_nominal_names,
                abstract_nominal_kinds,
            );
        }

        let _ = group_fields as fn(&ResolvedModuleGroup);
        let _ = program_fields as fn(&ResolvedModuleProgram);
        let _ = linked_constructor_fields as fn(&ResolvedConstructor);
        let _ = registry_fields as fn(&ResolvedRegistry);
    }

    fn deep_combined_registry_fixture(depth: usize) -> Vec<CheckedModule> {
        let source = SourceFile::new("deep-combined-registry.ash", "Deep")
            .expect("the deep combined fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the fixture range should be ordered"))
            .expect("the fixture span should fit");
        let module = ModuleId::new(9_700);
        let nominal = NominalTypeId::new(module, 0);
        let constructor = ConstructorId::new(nominal, 0);
        let parameter_id = TypeVariableId::resolved(module, 0);
        let mut kind = Kind::Type;
        let mut payload = Type::Variable(parameter_id);
        let mut origin = Origin::Source(span);
        for _ in 0..depth {
            kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
            payload = Type::Application(Box::new(payload), Box::new(Type::Unit));
            origin = Origin::Generated {
                cause: Box::new(origin),
                reason: crate::source::GeneratedReason::TypeChecking,
            };
        }
        let parameter = ResolvedTypeVariable {
            id: parameter_id,
            spelling: "F".to_owned(),
            kind,
            origin,
        };
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                spelling: "Deep".to_owned(),
                constructors: vec![constructor].into_boxed_slice(),
                origin: Origin::Source(span),
            }],
            vec![ResolvedConstructor {
                id: constructor,
                owner: nominal,
                spelling: "Make".to_owned(),
                payload: Some(payload),
                origin: Origin::Source(span),
            }],
        )
        .with_type_parameters(vec![(nominal, vec![parameter])]);
        vec![CheckedModule {
            module,
            registry: Arc::new(registry),
            direct_dependencies: Box::new([]),
            declaration_order: Box::new([]),
            interfaces: Box::new([]),
            implementations: Box::new([]),
            definitions: Box::new([]),
            available_implementations: Box::new([]),
            schemes: Vec::new(),
            checked_interfaces: Box::new([]),
            checked_implementations: Box::new([]),
            interface_facts: Box::new([]),
            implementation_facts: Box::new([]),
            exports: ExportSummary::empty(module),
            span,
        }]
    }

    #[test]
    fn combine_checked_deep_registry_has_exact_independent_ledgers_and_teardown() {
        const DEPTH: usize = 32_768;
        // ConstraintWork authenticates the one module, nominal family,
        // constructor inventory, binder-identity index, and the complete
        // record/Origin/Kind mirror. TypeWork retains both binder copies and
        // the constructor payload only after authentication succeeds.
        const CONSTRAINT_WORK: usize = 3 * DEPTH + 13;
        // The fixed eight cells retain the family-id slice, both nominal
        // staging/destination rows and positions, both constructor
        // carrier/position cells, and the canonical-variable staging slot.
        const TYPE_WORK: usize = 6 * DEPTH + 13;
        std::thread::Builder::new()
            .name("deep-combined-registry".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let modules = deep_combined_registry_fixture(DEPTH);

                let mut constraint_short =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
                let mut untouched_type = TypeWorkBudget::with_limit(TYPE_WORK);
                assert_eq!(
                    ResolvedRegistry::combine_checked(
                        &modules,
                        &mut untouched_type,
                        &mut constraint_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(
                    constraint_short.used(),
                    CONSTRAINT_WORK - 2,
                    "the final two-child Kind comparison charge is atomic",
                );
                assert_eq!(untouched_type.used(), 0);

                let mut exact_constraint =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
                let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
                assert_eq!(
                    ResolvedRegistry::combine_checked(
                        &modules,
                        &mut type_short,
                        &mut exact_constraint,
                    ),
                    Err(ResolvedBuildFailure::TypeResource),
                );
                assert_eq!(exact_constraint.used(), CONSTRAINT_WORK);
                assert_eq!(type_short.used(), 0);

                for _ in 0..2 {
                    let mut constraint =
                        crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
                    let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
                    let combined = ResolvedRegistry::combine_checked(
                        &modules,
                        &mut type_work,
                        &mut constraint,
                    )
                    .expect("the exact deep combined-registry budgets should fit");
                    assert_eq!(constraint.used(), CONSTRAINT_WORK);
                    assert_eq!(type_work.used(), TYPE_WORK);
                    let owner = NominalTypeId::new(ModuleId::new(9_700), 0);
                    let constructor = ConstructorId::new(owner, 0);
                    let parameter = TypeVariableId::resolved(ModuleId::new(9_700), 0);
                    assert_eq!(
                        combined
                            .nominal(owner)
                            .map(|nominal| nominal.constructors.as_ref()),
                        Some([constructor].as_slice()),
                    );
                    let payload = combined
                        .constructor(constructor)
                        .and_then(|constructor| constructor.payload.as_ref())
                        .expect("the deep constructor payload should be retained");
                    let mut payload_nodes = TypeWorkBudget::with_limit(2 * DEPTH + 1);
                    charge_type_cells(payload, &mut payload_nodes)
                        .expect("the retained payload should have the defining node count");
                    assert_eq!(payload_nodes.used(), 2 * DEPTH + 1);
                    let nominal_parameter = &combined
                        .nominal_parameters(owner)
                        .expect("the nominal parameter row should be retained")[0];
                    assert_eq!(nominal_parameter.id, parameter);
                    let canonical = combined
                        .type_variable(parameter)
                        .expect("the canonical nominal binder should be retained");
                    assert_eq!(canonical.id, parameter);
                    for retained_kind in [&nominal_parameter.kind, &canonical.kind] {
                        let mut kind_nodes = TypeWorkBudget::with_limit(2 * DEPTH + 1);
                        crate::types::charge_kind_nodes(retained_kind, &mut kind_nodes)
                            .expect("each retained Kind mirror should have the defining shape");
                        assert_eq!(kind_nodes.used(), 2 * DEPTH + 1);
                    }
                    combined.discard_iteratively();
                }
                drop(modules);
            })
            .expect("the deep combined-registry worker should spawn")
            .join()
            .expect("accepted and rejected combined registries must tear down iteratively");
    }

    fn wide_combined_registry_fixture(width: usize) -> Vec<CheckedModule> {
        assert_eq!(width % 4, 0);
        let owner_count = width / 4;
        let source = SourceFile::new("wide-combined-registry.ash", "Wide")
            .expect("the wide combined fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the fixture range should be ordered"))
            .expect("the fixture span should fit");
        let module = ModuleId::new(9_701);
        let nominal = NominalTypeId::new(module, 0);
        let constructor = ConstructorId::new(nominal, 0);
        let variable = |local: u32, spelling: &str| ResolvedTypeVariable {
            id: TypeVariableId::resolved(module, local),
            spelling: spelling.to_owned(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };

        let nominal_parameters = (0..owner_count)
            .map(|index| variable(u32::try_from(index).unwrap(), "P"))
            .collect::<Vec<_>>();
        let interface_parameters = (0..owner_count)
            .map(|index| variable(u32::try_from(owner_count + index).unwrap(), "I"))
            .collect::<Vec<_>>();
        let global_parameters = (0..owner_count)
            .map(|index| variable(u32::try_from(2 * owner_count + index).unwrap(), "G"))
            .collect::<Vec<_>>();
        let implementation_parameters = (0..owner_count)
            .map(|index| variable(u32::try_from(3 * owner_count + index).unwrap(), "H"))
            .collect::<Vec<_>>();

        let additional = interface_parameters
            .iter()
            .chain(global_parameters.iter())
            .chain(implementation_parameters.iter())
            .cloned()
            .collect::<Vec<_>>();
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                spelling: "Wide".to_owned(),
                constructors: vec![constructor].into_boxed_slice(),
                origin: Origin::Source(span),
            }],
            vec![ResolvedConstructor {
                id: constructor,
                owner: nominal,
                spelling: "Make".to_owned(),
                payload: None,
                origin: Origin::Source(span),
            }],
        )
        .with_type_parameters(vec![(nominal, nominal_parameters)])
        .with_additional_type_variables(additional);

        let interface_facts = interface_parameters
            .into_iter()
            .enumerate()
            .map(|(index, parameter)| {
                let id = InterfaceId::new(module, u32::try_from(index).unwrap());
                let method = MethodId::new(id, 0);
                CheckedInterfaceFact {
                    id,
                    spelling: format!("Interface{index}"),
                    methods: vec![CheckedInterfaceMethodFact {
                        id: method,
                        spelling: "method".to_owned(),
                        type_parameters: Box::new([]),
                        value_type: Type::Function(
                            Box::new(Type::Variable(parameter.id)),
                            Box::new(Type::Variable(parameter.id)),
                        ),
                        origin: Origin::Source(span),
                        span,
                    }]
                    .into_boxed_slice(),
                    method_binder_authorities: Box::new([MethodBinderAuthority {
                        method,
                        parameters: Box::new([]),
                    }]),
                    parameter,
                    origin: Origin::Source(span),
                    span,
                }
            })
            .collect::<Vec<_>>();
        let global_binder = BinderId::resolved(module, 0);
        let global_scheme = CheckedGlobalScheme {
            binder: global_binder,
            spelling: "wide".to_owned(),
            scheme: ConstrainedScheme {
                type_parameters: global_parameters
                    .iter()
                    .map(|parameter| (parameter.id, Kind::Type))
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
                requirements: Box::new([]),
                value_type: Type::Tuple(
                    global_parameters
                        .iter()
                        .map(|parameter| Type::Variable(parameter.id))
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                ),
            },
            origin: Origin::Source(span),
        };
        let implementation_id = ImplId::new(module, 0);
        let implementation_argument = Type::Tuple(
            implementation_parameters
                .iter()
                .map(|parameter| Type::Variable(parameter.id))
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        );
        let implementation_method = interface_facts[0].methods[0].id;
        let mut unbounded = TypeWorkBudget::unbounded();
        let method_domain = clone_type_with_budget(&implementation_argument, &mut unbounded)
            .expect("the wide method domain should fit");
        let method_codomain = clone_type_with_budget(&implementation_argument, &mut unbounded)
            .expect("the wide method codomain should fit");
        let implementation = CheckedImplementationFact {
            id: implementation_id,
            interface: interface_facts[0].id,
            head_parameters: implementation_parameters.into_boxed_slice(),
            argument: implementation_argument,
            prerequisites: Box::new([]),
            methods: Box::new([CheckedImplementationMethodFact {
                id: ImplMethodId::new(implementation_id, implementation_method),
                method: implementation_method,
                binder: BinderId::resolved(module, 1),
                scheme: ConstrainedScheme {
                    type_parameters: (0..owner_count)
                        .map(|index| {
                            (
                                TypeVariableId::resolved(
                                    module,
                                    u32::try_from(3 * owner_count + index).unwrap(),
                                ),
                                Kind::Type,
                            )
                        })
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                    requirements: Box::new([]),
                    value_type: Type::Function(Box::new(method_domain), Box::new(method_codomain)),
                },
                head_type_parameter_count: owner_count,
                origin: Origin::Source(span),
                span,
            }]),
            origin: Origin::Source(span),
            span,
        };
        vec![CheckedModule {
            module,
            registry: Arc::new(registry),
            direct_dependencies: Box::new([]),
            declaration_order: Box::new([]),
            interfaces: Box::new([]),
            implementations: Box::new([]),
            definitions: Box::new([]),
            available_implementations: Box::new([AvailableImplementation::local(
                implementation_id,
            )]),
            schemes: vec![global_scheme],
            checked_interfaces: Box::new([]),
            checked_implementations: Box::new([]),
            interface_facts: interface_facts.into_boxed_slice(),
            implementation_facts: vec![implementation].into_boxed_slice(),
            exports: ExportSummary::empty(module),
            span,
        }]
    }

    #[test]
    fn combine_checked_wide_registry_covers_every_binder_owner_with_exact_ledgers() {
        const WIDTH: usize = 32_768;
        const OWNER_COUNT: usize = WIDTH / 4;
        // ConstraintWork authenticates one module, one nominal family, one
        // constructor, every owner slot and canonical identity, and the
        // nominal/global/implementation mirrors. The interface carrier mirror
        // belongs to the consuming linked-evidence validator. TypeWork owns
        // only the canonical records plus the scalar global row. The fixed
        // final cell reserves the non-empty global-owner uniqueness index.
        const CONSTRAINT_WORK: usize = 13 * OWNER_COUNT + 12;
        // Five cells per owner retain the canonical-variable staging rows and
        // the scalar global-parameter identities. Nine fixed cells retain the
        // family, nominal, constructor, global-row, and row-index storage.
        const TYPE_WORK: usize = 15 * OWNER_COUNT + 9;
        std::thread::Builder::new()
            .name("wide-combined-registry".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let modules = wide_combined_registry_fixture(WIDTH);
                let mut constraint_short =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
                let mut untouched_type = TypeWorkBudget::with_limit(TYPE_WORK);
                assert_eq!(
                    ResolvedRegistry::combine_checked(
                        &modules,
                        &mut untouched_type,
                        &mut constraint_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(constraint_short.used(), CONSTRAINT_WORK - 1);
                assert_eq!(untouched_type.used(), 0);

                let mut constraint =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
                let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
                assert_eq!(
                    ResolvedRegistry::combine_checked(&modules, &mut type_short, &mut constraint,),
                    Err(ResolvedBuildFailure::TypeResource),
                );
                assert_eq!(constraint.used(), CONSTRAINT_WORK);
                assert_eq!(type_short.used(), 0);

                for _ in 0..2 {
                    let mut constraint =
                        crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
                    let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
                    let combined = ResolvedRegistry::combine_checked(
                        &modules,
                        &mut type_work,
                        &mut constraint,
                    )
                    .expect("the exact wide combined-registry budgets should fit");
                    assert_eq!(constraint.used(), CONSTRAINT_WORK);
                    assert_eq!(type_work.used(), TYPE_WORK);
                    let module = ModuleId::new(9_701);
                    let owner = NominalTypeId::new(module, 0);
                    let constructor = ConstructorId::new(owner, 0);
                    let parameters = combined
                        .nominal_parameters(owner)
                        .expect("the complete wide nominal row should be retained");
                    assert_eq!(parameters.len(), OWNER_COUNT);
                    let global_row = combined
                        .global_parameter_row(BinderId::resolved(module, 0))
                        .expect("the complete wide global row should be retained");
                    assert_eq!(global_row.parameters().len(), OWNER_COUNT);
                    assert_eq!(combined.type_variables.len(), WIDTH);
                    assert!(
                        parameters
                            .iter()
                            .all(|parameter| parameter.id.module() == Some(module)
                                && parameter.kind == Kind::Type),
                    );
                    assert!(
                        combined
                            .type_variables
                            .values()
                            .all(|parameter| parameter.id.module() == Some(module)
                                && parameter.kind == Kind::Type),
                    );
                    assert!(
                        combined
                            .constructor(constructor)
                            .is_some_and(|constructor| constructor.payload.is_none()),
                    );
                    combined.discard_iteratively();
                }
                drop(modules);
            })
            .expect("the wide combined-registry worker should spawn")
            .join()
            .expect("wide accepted and rejected registries must tear down iteratively");
    }

    #[test]
    fn combine_checked_prices_the_canonical_interface_kind_before_retention() {
        const CONSTRAINT_WORK: usize = 25;
        // The one-owner fixture normally costs 24 TypeWork cells. Replacing
        // the canonical interface Kind `Type` with `Type -> Type` adds two
        // retained Kind nodes even though the independently retained interface
        // carrier remains shallow for evidence validation to reject later.
        const TYPE_WORK: usize = 26;
        let mut modules = wide_combined_registry_fixture(4);
        let interface_parameter = modules[0].interface_facts[0].parameter.id;
        Arc::get_mut(&mut modules[0].registry)
            .expect("the canonical interface registry should be uniquely owned")
            .type_variables
            .get_mut(&interface_parameter)
            .expect("the canonical interface binder should exist")
            .kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));

        let mut constraint =
            crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
        let mut one_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
        assert_eq!(
            ResolvedRegistry::combine_checked(&modules, &mut one_short, &mut constraint),
            Err(ResolvedBuildFailure::TypeResource),
        );
        assert_eq!(constraint.used(), CONSTRAINT_WORK);
        assert_eq!(
            one_short.used(),
            0,
            "the aggregate TypeWork charge is atomic"
        );

        for _ in 0..2 {
            let mut constraint =
                crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
            let mut exact = TypeWorkBudget::with_limit(TYPE_WORK);
            let registry = ResolvedRegistry::combine_checked(&modules, &mut exact, &mut constraint)
                .expect("the canonical retained Kind should fit its exact TypeWork budget");
            assert_eq!(constraint.used(), CONSTRAINT_WORK);
            assert_eq!(exact.used(), TYPE_WORK);
            assert!(matches!(
                registry
                    .type_variable(interface_parameter)
                    .map(|parameter| &parameter.kind),
                Some(Kind::Arrow(_, _)),
            ));
            registry.discard_iteratively();
        }
    }

    #[test]
    fn combine_checked_charges_each_nominal_binder_before_rejecting_its_owner() {
        const WIDTH: usize = 32_768;
        // Structural admission costs nine fixed units. The canonical-ID index
        // costs WIDTH units. Each valid nominal mirror costs three comparison
        // units, while the final malformed binder is rejected after its one
        // base unit and before spelling, Origin, or Kind comparison.
        const CONSTRAINT_WORK: usize = 4 * WIDTH + 7;
        std::thread::Builder::new()
            .name("wide-malformed-combined-registry".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("wide-malformed-registry.ash", "Wide")
                    .expect("the wide malformed fixture source should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the fixture range should be ordered"))
                    .expect("the fixture span should fit");
                let module = ModuleId::new(9_703);
                let nominal = NominalTypeId::new(module, 0);
                let constructor = ConstructorId::new(nominal, 0);
                let parameters = (0..WIDTH)
                    .map(|index| ResolvedTypeVariable {
                        id: TypeVariableId::resolved(
                            module,
                            u32::try_from(index).expect("the binder identity should fit"),
                        ),
                        spelling: "P".to_owned(),
                        kind: Kind::Type,
                        origin: Origin::Source(span),
                    })
                    .collect::<Vec<_>>();
                let registry = ResolvedRegistry::new(
                    vec![ResolvedNominalType {
                        id: nominal,
                        spelling: "Wide".to_owned(),
                        constructors: Box::new([constructor]),
                        origin: Origin::Source(span),
                    }],
                    vec![ResolvedConstructor {
                        id: constructor,
                        owner: nominal,
                        spelling: "Make".to_owned(),
                        payload: None,
                        origin: Origin::Source(span),
                    }],
                )
                .with_type_parameters(vec![(nominal, parameters)]);
                let mut modules = vec![registry_only_checked_module(module, registry, span)];
                Arc::get_mut(&mut modules[0].registry)
                    .expect("the malformed registry should be uniquely owned")
                    .nominal_parameters
                    .get_mut(&nominal)
                    .expect("the nominal parameter row should exist")
                    .last_mut()
                    .expect("the wide row should be non-empty")
                    .id = TypeVariableId::resolved(ModuleId::new(99), 0);

                let mut exact =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
                let mut untouched_type = TypeWorkBudget::default();
                assert_eq!(
                    ResolvedRegistry::combine_checked(&modules, &mut untouched_type, &mut exact,),
                    Err(ResolvedBuildFailure::InvalidState),
                );
                assert_eq!(exact.used(), CONSTRAINT_WORK);
                assert_eq!(untouched_type.used(), 0);

                let mut one_short =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
                assert_eq!(
                    ResolvedRegistry::combine_checked(
                        &modules,
                        &mut TypeWorkBudget::default(),
                        &mut one_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(one_short.used(), CONSTRAINT_WORK - 1);
            })
            .expect("the wide malformed registry worker should start")
            .join()
            .expect("wide malformed admission and teardown must fit 256 KiB");
    }

    fn registry_only_checked_module(
        module: ModuleId,
        registry: ResolvedRegistry,
        span: Span,
    ) -> CheckedModule {
        CheckedModule {
            module,
            registry: Arc::new(registry),
            direct_dependencies: Box::new([]),
            declaration_order: Box::new([]),
            interfaces: Box::new([]),
            implementations: Box::new([]),
            definitions: Box::new([]),
            available_implementations: Box::new([]),
            schemes: Vec::new(),
            checked_interfaces: Box::new([]),
            checked_implementations: Box::new([]),
            interface_facts: Box::new([]),
            implementation_facts: Box::new([]),
            exports: ExportSummary::empty(module),
            span,
        }
    }

    fn global_parameter_row_fixture() -> Vec<CheckedModule> {
        fn parameter(module: ModuleId, local: u32, span: Span) -> ResolvedTypeVariable {
            ResolvedTypeVariable {
                id: TypeVariableId::resolved(module, local),
                spelling: format!("T{local}"),
                kind: Kind::Type,
                origin: Origin::Source(span),
            }
        }

        fn scheme(
            owner: BinderId,
            parameters: &[ResolvedTypeVariable],
            span: Span,
        ) -> CheckedGlobalScheme {
            CheckedGlobalScheme {
                binder: owner,
                spelling: format!("global{}", owner.local()),
                scheme: ConstrainedScheme {
                    type_parameters: parameters
                        .iter()
                        .map(|parameter| (parameter.id, Kind::Type))
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                    requirements: Box::new([]),
                    value_type: Type::Tuple(
                        parameters
                            .iter()
                            .map(|parameter| Type::Variable(parameter.id))
                            .collect::<Vec<_>>()
                            .into_boxed_slice(),
                    ),
                },
                origin: Origin::Source(span),
            }
        }

        let source = SourceFile::new("global-parameter-rows.ash", "rows")
            .expect("the global-row source should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the global-row range should be ordered"))
            .expect("the global-row span should fit");
        let first_module = ModuleId::new(9_704);
        let second_module = ModuleId::new(9_705);
        let first_parameters = [
            parameter(first_module, 0, span),
            parameter(first_module, 1, span),
        ];
        let second_parameters = [parameter(second_module, 0, span)];
        let first_registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_additional_type_variables(first_parameters.iter().cloned());
        let second_registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_additional_type_variables(second_parameters.iter().cloned());
        let mut first = registry_only_checked_module(first_module, first_registry, span);
        first.schemes = vec![
            scheme(BinderId::resolved(first_module, 0), &first_parameters, span),
            scheme(BinderId::resolved(first_module, 1), &[], span),
        ];
        let mut second = registry_only_checked_module(second_module, second_registry, span);
        second.schemes = vec![scheme(
            BinderId::resolved(second_module, 0),
            &second_parameters,
            span,
        )];
        vec![first, second]
    }

    #[test]
    fn combine_checked_retains_borrowed_global_parameter_rows_in_dependency_order() {
        const MODULES: usize = 2;
        const GLOBAL_SCHEMES: usize = 3;
        const GLOBAL_ROWS: usize = 2;
        const GLOBAL_PARAMETERS: usize = 3;
        const PREEXISTING_FIXED_CONSTRAINT_WORK: usize = 2 * MODULES + GLOBAL_SCHEMES;
        const GLOBAL_OWNER_UNIQUENESS_WORK: usize = GLOBAL_ROWS;
        const FIXED_CONSTRAINT_WORK: usize =
            PREEXISTING_FIXED_CONSTRAINT_WORK + GLOBAL_OWNER_UNIQUENESS_WORK;
        const TYPE_VARIABLE_UNIQUENESS_WORK: usize = GLOBAL_PARAMETERS;
        const GLOBAL_PARAMETER_VISIT_WORK: usize = GLOBAL_PARAMETERS;
        const CANONICAL_KIND_COMPARISON_WORK: usize = GLOBAL_PARAMETERS;
        const CONSTRAINT_WORK: usize = FIXED_CONSTRAINT_WORK
            + TYPE_VARIABLE_UNIQUENESS_WORK
            + GLOBAL_PARAMETER_VISIT_WORK
            + CANONICAL_KIND_COMPARISON_WORK;
        const PREEXISTING_RETENTION_TYPE_WORK: usize = 3 * GLOBAL_PARAMETERS;
        const ROW_RETENTION_TYPE_WORK: usize = 2 * GLOBAL_ROWS + GLOBAL_PARAMETERS;
        const TYPE_WORK: usize = PREEXISTING_RETENTION_TYPE_WORK + ROW_RETENTION_TYPE_WORK;

        let modules = global_parameter_row_fixture();
        let counts = checked_registry_counts(&modules).expect("the row counts should fit");
        assert_eq!(counts.global_rows, GLOBAL_ROWS);
        assert_eq!(counts.global_parameters, GLOBAL_PARAMETERS);
        assert_eq!(counts.fixed_constraint_work, FIXED_CONSTRAINT_WORK);
        assert_eq!(
            counts.fixed_constraint_work - PREEXISTING_FIXED_CONSTRAINT_WORK,
            GLOBAL_OWNER_UNIQUENESS_WORK,
            "each non-empty global scheme owns one pre-retention owner-uniqueness cell",
        );
        assert_eq!(
            counts.retention_type_work - PREEXISTING_RETENTION_TYPE_WORK,
            ROW_RETENTION_TYPE_WORK,
            "rows retain only one row slot, one owner index slot, and each scalar identity",
        );

        let mut constraint_short =
            crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
        let mut untouched_type = TypeWorkBudget::with_limit(TYPE_WORK);
        assert_eq!(
            ResolvedRegistry::combine_checked(&modules, &mut untouched_type, &mut constraint_short,),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(constraint_short.used(), CONSTRAINT_WORK - 1);
        assert_eq!(untouched_type.used(), 0);

        let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
        let mut exact_constraint =
            crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
        assert_eq!(
            ResolvedRegistry::combine_checked(&modules, &mut type_short, &mut exact_constraint,),
            Err(ResolvedBuildFailure::TypeResource),
        );
        assert_eq!(type_short.used(), 0, "the aggregate precharge is atomic");
        assert_eq!(exact_constraint.used(), CONSTRAINT_WORK);

        let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
        let mut constraint_work =
            crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
        let combined =
            ResolvedRegistry::combine_checked(&modules, &mut type_work, &mut constraint_work)
                .expect("the exact global-row budgets should fit");
        assert_eq!(type_work.used(), TYPE_WORK);
        assert_eq!(constraint_work.used(), CONSTRAINT_WORK);

        let first_owner = BinderId::resolved(ModuleId::new(9_704), 0);
        let empty_owner = BinderId::resolved(ModuleId::new(9_704), 1);
        let second_owner = BinderId::resolved(ModuleId::new(9_705), 0);
        let rows = combined.global_parameter_rows();
        assert_eq!(
            rows.iter()
                .map(ResolvedGlobalParameterRow::owner)
                .collect::<Vec<_>>(),
            [first_owner, second_owner],
        );
        assert_eq!(
            rows.iter()
                .map(ResolvedGlobalParameterRow::parameters)
                .collect::<Vec<_>>(),
            [
                [
                    TypeVariableId::resolved(ModuleId::new(9_704), 0),
                    TypeVariableId::resolved(ModuleId::new(9_704), 1),
                ]
                .as_slice(),
                [TypeVariableId::resolved(ModuleId::new(9_705), 0)].as_slice(),
            ],
        );
        assert_eq!(combined.global_parameter_row(first_owner), rows.first(),);
        assert_eq!(combined.global_parameter_row(second_owner), rows.get(1),);
        assert_eq!(combined.global_parameter_row(empty_owner), None);
    }

    #[test]
    fn combine_checked_excludes_non_global_and_empty_parameter_owners() {
        let mut modules = wide_combined_registry_fixture(8);
        let module = modules[0].module;
        let span = modules[0].span;
        let empty_owner = BinderId::resolved(module, 2);
        modules[0].schemes.push(CheckedGlobalScheme {
            binder: empty_owner,
            spelling: "empty".to_owned(),
            scheme: ConstrainedScheme::from_rank1_type(Type::Unit),
            origin: Origin::Source(span),
        });
        let combined = ResolvedRegistry::combine_checked(
            &modules,
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        )
        .expect("the exclusion fixture should combine");
        let rows = combined.global_parameter_rows();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].owner(), BinderId::resolved(module, 0));
        assert_eq!(
            rows[0].parameters(),
            [
                TypeVariableId::resolved(module, 4),
                TypeVariableId::resolved(module, 5),
            ],
        );
        assert_eq!(combined.global_parameter_row(empty_owner), None);
        for excluded in [
            TypeVariableId::resolved(module, 0),
            TypeVariableId::resolved(module, 1),
            TypeVariableId::resolved(module, 2),
            TypeVariableId::resolved(module, 3),
            TypeVariableId::resolved(module, 6),
            TypeVariableId::resolved(module, 7),
        ] {
            assert!(
                rows.iter().all(|row| !row.parameters().contains(&excluded)),
                "nominal, interface, and implementation-head parameters must not enter rows",
            );
        }
    }

    #[test]
    fn combine_checked_rejects_duplicate_global_parameter_row_owners_before_type_precharge() {
        std::thread::Builder::new()
            .name("duplicate-global-row-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut modules = global_parameter_row_fixture();
                let module = modules[0].module;
                let span = modules[0].span;
                let duplicate_owner = modules[0].schemes[0].binder;
                modules[0].schemes[1].binder = duplicate_owner;
                modules[0].schemes[1].scheme.type_parameters =
                    Box::new([(TypeVariableId::resolved(module, 2), Kind::Type)]);
                modules[0].schemes[1].scheme.value_type =
                    Type::Variable(TypeVariableId::resolved(module, 2));
                Arc::get_mut(&mut modules[0].registry)
                    .expect("the duplicate-owner registry should be unique")
                    .insert_type_variable(ResolvedTypeVariable {
                        id: TypeVariableId::resolved(module, 2),
                        spelling: "T2".to_owned(),
                        kind: Kind::Type,
                        origin: Origin::Source(span),
                    });

                let counts = checked_registry_counts(&modules)
                    .expect("the duplicate-owner aggregate counts should fit");
                assert_eq!(counts.global_rows, 3);
                assert_eq!(counts.fixed_constraint_work, 10);

                let mut type_work = TypeWorkBudget::default();
                let mut constraint_work = crate::interface::InterfaceConstraintBudget::default();
                assert_eq!(
                    ResolvedRegistry::combine_checked(
                        &modules,
                        &mut type_work,
                        &mut constraint_work,
                    ),
                    Err(ResolvedBuildFailure::InvalidState),
                );
                assert_eq!(type_work.used(), 0);
                assert_eq!(constraint_work.used(), counts.fixed_constraint_work);

                let mut untouched_type = TypeWorkBudget::default();
                let mut constraint_short = crate::interface::InterfaceConstraintBudget::with_limit(
                    counts.fixed_constraint_work - 1,
                );
                assert_eq!(
                    ResolvedRegistry::combine_checked(
                        &modules,
                        &mut untouched_type,
                        &mut constraint_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(constraint_short.used(), 0);
                assert_eq!(untouched_type.used(), 0);
                drop(modules);
            })
            .expect("the duplicate-owner worker should spawn")
            .join()
            .expect("rejected global-row owners must tear down on a small stack");
    }

    #[test]
    fn combine_checked_prevalidation_returns_a_borrowed_retention_witness() {
        const CONSTRAINT_WORK: usize = 18;
        let modules = global_parameter_row_fixture();
        let counts = checked_registry_counts(&modules).expect("the row counts should fit");
        let mut constraint_work =
            crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
        let witness: ValidatedCheckedRegistries<'_> =
            validate_checked_registries(&modules, &counts, &mut constraint_work)
                .expect("the exact prevalidation budget should produce row-retention authority");
        assert_eq!(constraint_work.used(), CONSTRAINT_WORK);
        assert_eq!(witness.modules().len(), modules.len());
    }

    fn empty_parameter_combined_registry_fixture(width: usize) -> Vec<CheckedModule> {
        let source = SourceFile::new("empty-combined-registry.ash", "Empty")
            .expect("the empty combined fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 5).expect("the fixture range should be ordered"))
            .expect("the fixture span should fit");
        let module = ModuleId::new(9_702);
        let nominal = NominalTypeId::new(module, 0);
        let family = (0..width)
            .map(|index| {
                ConstructorId::new(
                    nominal,
                    u32::try_from(index).expect("the constructor ordinal should fit"),
                )
            })
            .collect::<Vec<_>>();
        let constructors = family
            .iter()
            .enumerate()
            .map(|(index, id)| ResolvedConstructor {
                id: *id,
                owner: nominal,
                spelling: format!("Make{index}"),
                payload: None,
                origin: Origin::Source(span),
            })
            .collect::<Vec<_>>();
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                spelling: "Empty".to_owned(),
                constructors: family.into_boxed_slice(),
                origin: Origin::Source(span),
            }],
            constructors,
        )
        .with_type_parameters(vec![(nominal, Vec::new())]);
        vec![registry_only_checked_module(module, registry, span)]
    }

    #[test]
    fn combine_checked_wide_family_charges_membership_and_retention_indexes_exactly() {
        const WIDTH: usize = 32_768;
        // ConstraintWork: one module, nominal, and parameter row; WIDTH family
        // and constructor visits; then one module, nominal, WIDTH family, and
        // WIDTH constructor uniqueness cells.
        const CONSTRAINT_WORK: usize = 4 * WIDTH + 5;
        // TypeWork: WIDTH family-id cells, four nominal carrier/staging/index
        // cells, and two carrier/index cells per constructor.
        const TYPE_WORK: usize = 3 * WIDTH + 4;

        std::thread::Builder::new()
            .name("wide-combined-registry-family".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let modules = empty_parameter_combined_registry_fixture(WIDTH);
                let mut constraint_short =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
                let mut untouched_type = TypeWorkBudget::with_limit(TYPE_WORK);
                assert_eq!(
                    ResolvedRegistry::combine_checked(
                        &modules,
                        &mut untouched_type,
                        &mut constraint_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(constraint_short.used(), 0);
                assert_eq!(untouched_type.used(), 0);

                let mut constraint =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
                let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
                assert_eq!(
                    ResolvedRegistry::combine_checked(&modules, &mut type_short, &mut constraint,),
                    Err(ResolvedBuildFailure::TypeResource),
                );
                assert_eq!(constraint.used(), CONSTRAINT_WORK);
                assert_eq!(type_short.used(), 0);

                let mut constraint =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
                let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
                let combined =
                    ResolvedRegistry::combine_checked(&modules, &mut type_work, &mut constraint)
                        .expect("the exact wide family registry should combine");
                assert_eq!(constraint.used(), CONSTRAINT_WORK);
                assert_eq!(type_work.used(), TYPE_WORK);
                let owner = NominalTypeId::new(ModuleId::new(9_702), 0);
                assert_eq!(
                    combined
                        .nominal(owner)
                        .map(|nominal| nominal.constructors.len()),
                    Some(WIDTH),
                );
                combined.discard_iteratively();
            })
            .expect("the wide family registry worker should start")
            .join()
            .expect("wide family combination and teardown must fit 256 KiB");
    }

    #[test]
    fn combine_checked_rejects_registry_structure_and_owned_mirror_corruption_before_retention() {
        #[derive(Clone, Copy, Debug)]
        enum Mutation {
            ConstructorOwner,
            ConstructorIdentityOwner,
            FamilyOrdinal,
            FamilyOrder,
            NominalPosition,
            NominalPositionExtra,
            ConstructorPosition,
            ConstructorPositionExtra,
            MissingEmptyParameterRow,
            ExtraParameterRow,
            AbstractName,
            AbstractKind,
            CanonicalValueIdentity,
            MissingNominalCanonical,
            MissingInterfaceCanonical,
            MissingGlobalCanonical,
            MissingImplementationCanonical,
            ForeignZeroParameterGlobal,
            ForeignZeroHeadImplementation,
            ExtraCanonicalVariable,
            CanonicalMirrorSpelling,
            CanonicalMirrorOrigin,
            CanonicalMirrorKind,
            NominalMirrorSpelling,
            NominalMirrorOrigin,
            NominalMirrorKind,
            NominalParameterOwner,
            NominalParameterOrder,
            InterfaceParameterOwner,
            GlobalParameterOwner,
            DuplicateGlobalParameterIdentity,
            GeneratedGlobalParameterIdentity,
            NominalGlobalParameterIdentity,
            GlobalMirrorKind,
            ImplementationParameterOwner,
            ImplementationParameterOrder,
            ImplementationMirrorSpelling,
            ImplementationMirrorOrigin,
            ImplementationMirrorKind,
        }

        let mutations = [
            (Mutation::ConstructorOwner, 13, 0),
            (Mutation::ConstructorIdentityOwner, 13, 0),
            (Mutation::FamilyOrdinal, 13, 0),
            (Mutation::FamilyOrder, 13, 0),
            (Mutation::NominalPosition, 13, 0),
            (Mutation::NominalPositionExtra, 13, 0),
            (Mutation::ConstructorPosition, 13, 0),
            (Mutation::ConstructorPositionExtra, 13, 0),
            (Mutation::MissingEmptyParameterRow, 9, 0),
            (Mutation::ExtraParameterRow, 13, 0),
            (Mutation::AbstractName, 13, 0),
            (Mutation::AbstractKind, 13, 0),
            (Mutation::CanonicalValueIdentity, 18, 0),
            (Mutation::MissingNominalCanonical, 13, 0),
            (Mutation::MissingInterfaceCanonical, 13, 0),
            (Mutation::MissingGlobalCanonical, 13, 0),
            (Mutation::MissingImplementationCanonical, 13, 0),
            (Mutation::ForeignZeroParameterGlobal, 12, 0),
            (Mutation::ForeignZeroHeadImplementation, 13, 0),
            (Mutation::ExtraCanonicalVariable, 13, 0),
            (Mutation::CanonicalMirrorSpelling, 18, 0),
            (Mutation::CanonicalMirrorOrigin, 19, 0),
            (Mutation::CanonicalMirrorKind, 20, 0),
            (Mutation::NominalMirrorSpelling, 18, 0),
            (Mutation::NominalMirrorOrigin, 19, 0),
            (Mutation::NominalMirrorKind, 20, 0),
            (Mutation::NominalParameterOwner, 26, 0),
            (Mutation::NominalParameterOrder, 26, 0),
            (Mutation::InterfaceParameterOwner, 20, 0),
            (Mutation::GlobalParameterOwner, 31, 0),
            (Mutation::DuplicateGlobalParameterIdentity, 31, 0),
            (Mutation::GeneratedGlobalParameterIdentity, 21, 0),
            (Mutation::NominalGlobalParameterIdentity, 21, 0),
            (Mutation::GlobalMirrorKind, 22, 0),
            (Mutation::ImplementationParameterOwner, 36, 0),
            (Mutation::ImplementationParameterOrder, 36, 0),
            (Mutation::ImplementationMirrorSpelling, 23, 0),
            (Mutation::ImplementationMirrorOrigin, 24, 0),
            (Mutation::ImplementationMirrorKind, 25, 0),
        ];
        for (mutation, expected_constraint_work, expected_type_work) in mutations {
            let mut modules = match mutation {
                Mutation::FamilyOrder => empty_parameter_combined_registry_fixture(2),
                Mutation::MissingEmptyParameterRow => empty_parameter_combined_registry_fixture(1),
                Mutation::NominalParameterOwner
                | Mutation::NominalParameterOrder
                | Mutation::GlobalParameterOwner
                | Mutation::DuplicateGlobalParameterIdentity
                | Mutation::ImplementationParameterOwner
                | Mutation::ImplementationParameterOrder => wide_combined_registry_fixture(8),
                _ => wide_combined_registry_fixture(4),
            };
            let module = modules[0].module;
            let span = modules[0].span;
            let interface_parameter = modules[0]
                .interface_facts
                .first()
                .map(|interface| interface.parameter.id);
            let global_parameter = modules[0]
                .schemes
                .first()
                .and_then(|scheme| scheme.scheme.type_parameters.first())
                .map(|parameter| parameter.0);
            let implementation_parameter = modules[0]
                .implementation_facts
                .first()
                .and_then(|implementation| implementation.head_parameters.first())
                .map(|parameter| parameter.id);
            let registry = Arc::get_mut(&mut modules[0].registry)
                .expect("the mutation fixture registry should be uniquely owned");
            match mutation {
                Mutation::ConstructorOwner => {
                    registry.constructors[0].owner = NominalTypeId::new(ModuleId::new(99), 0);
                }
                Mutation::ConstructorIdentityOwner => {
                    registry.constructors[0].id =
                        ConstructorId::new(NominalTypeId::new(ModuleId::new(99), 0), 0);
                }
                Mutation::FamilyOrdinal => {
                    let owner = registry.nominals[0].id;
                    registry.nominals[0].constructors[0] = ConstructorId::new(owner, 1);
                }
                Mutation::FamilyOrder => registry.nominals[0].constructors.swap(0, 1),
                Mutation::NominalPosition => {
                    let id = registry.nominals[0].id;
                    registry.nominal_positions.insert(id, usize::MAX);
                }
                Mutation::NominalPositionExtra => {
                    registry
                        .nominal_positions
                        .insert(NominalTypeId::new(module, u32::MAX), 0);
                }
                Mutation::ConstructorPosition => {
                    let id = registry.constructors[0].id;
                    registry.constructor_positions.insert(id, usize::MAX);
                }
                Mutation::ConstructorPositionExtra => {
                    registry.constructor_positions.insert(
                        ConstructorId::new(NominalTypeId::new(module, u32::MAX), 0),
                        0,
                    );
                }
                Mutation::MissingEmptyParameterRow => {
                    let id = registry.nominals[0].id;
                    let removed = registry
                        .nominal_parameters
                        .remove(&id)
                        .expect("the valid fixture retains an explicit empty row");
                    discard_resolved_type_variables(removed);
                }
                Mutation::ExtraParameterRow => {
                    registry
                        .nominal_parameters
                        .insert(NominalTypeId::new(module, u32::MAX), Box::new([]));
                }
                Mutation::AbstractName => {
                    registry
                        .abstract_nominal_names
                        .insert(registry.nominals[0].id, "abstract".to_owned());
                }
                Mutation::AbstractKind => {
                    registry.abstract_nominal_kinds.insert(
                        registry.nominals[0].id,
                        NonMaterializedNominalKindFact {
                            kind: Kind::Type,
                            origin: span,
                        },
                    );
                }
                Mutation::CanonicalValueIdentity => {
                    let id = registry.nominal_parameters[&registry.nominals[0].id][0].id;
                    registry.type_variables.get_mut(&id).unwrap().id =
                        TypeVariableId::resolved(module, u32::MAX);
                }
                Mutation::MissingNominalCanonical => {
                    let id = registry.nominal_parameters[&registry.nominals[0].id][0].id;
                    let removed = registry
                        .type_variables
                        .remove(&id)
                        .expect("the nominal canonical binder should exist");
                    discard_resolved_type_variable(removed);
                }
                Mutation::MissingInterfaceCanonical => {
                    let removed = registry
                        .type_variables
                        .remove(&interface_parameter.expect("the fixture has an interface binder"))
                        .expect("the interface canonical binder should exist");
                    discard_resolved_type_variable(removed);
                }
                Mutation::MissingGlobalCanonical => {
                    let removed = registry
                        .type_variables
                        .remove(&global_parameter.expect("the fixture has a global binder"))
                        .expect("the global canonical binder should exist");
                    discard_resolved_type_variable(removed);
                }
                Mutation::MissingImplementationCanonical => {
                    let removed = registry
                        .type_variables
                        .remove(
                            &implementation_parameter
                                .expect("the fixture has an implementation binder"),
                        )
                        .expect("the implementation canonical binder should exist");
                    discard_resolved_type_variable(removed);
                }
                Mutation::ForeignZeroParameterGlobal => {
                    modules[0].schemes[0].binder = BinderId::resolved(ModuleId::new(99), 0);
                    modules[0].schemes[0].scheme.type_parameters = Box::new([]);
                }
                Mutation::ForeignZeroHeadImplementation => {
                    modules[0].implementation_facts[0].id = ImplId::new(ModuleId::new(99), 0);
                    modules[0].implementation_facts[0].head_parameters = Box::new([]);
                }
                Mutation::ExtraCanonicalVariable => {
                    let id = TypeVariableId::resolved(module, u32::MAX);
                    registry.type_variables.insert(
                        id,
                        ResolvedTypeVariable {
                            id,
                            spelling: "extra".to_owned(),
                            kind: Kind::Type,
                            origin: Origin::Source(span),
                        },
                    );
                }
                Mutation::CanonicalMirrorSpelling => {
                    let id = registry.nominal_parameters[&registry.nominals[0].id][0].id;
                    registry.type_variables.get_mut(&id).unwrap().spelling = "forged".to_owned();
                }
                Mutation::CanonicalMirrorOrigin => {
                    let id = registry.nominal_parameters[&registry.nominals[0].id][0].id;
                    registry.type_variables.get_mut(&id).unwrap().origin = Origin::Generated {
                        cause: Box::new(Origin::Source(span)),
                        reason: crate::source::GeneratedReason::TypeChecking,
                    };
                }
                Mutation::CanonicalMirrorKind => {
                    let id = registry.nominal_parameters[&registry.nominals[0].id][0].id;
                    registry.type_variables.get_mut(&id).unwrap().kind =
                        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
                }
                Mutation::NominalMirrorSpelling => {
                    registry
                        .nominal_parameters
                        .get_mut(&registry.nominals[0].id)
                        .unwrap()[0]
                        .spelling = "forged".to_owned();
                }
                Mutation::NominalMirrorOrigin => {
                    let parameter = &mut registry
                        .nominal_parameters
                        .get_mut(&registry.nominals[0].id)
                        .unwrap()[0];
                    parameter.origin = Origin::Generated {
                        cause: Box::new(Origin::Source(span)),
                        reason: crate::source::GeneratedReason::TypeChecking,
                    };
                }
                Mutation::NominalMirrorKind => {
                    registry
                        .nominal_parameters
                        .get_mut(&registry.nominals[0].id)
                        .unwrap()[0]
                        .kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
                }
                Mutation::NominalParameterOwner => {
                    registry
                        .nominal_parameters
                        .get_mut(&registry.nominals[0].id)
                        .unwrap()
                        .last_mut()
                        .unwrap()
                        .id = TypeVariableId::resolved(ModuleId::new(99), 0);
                }
                Mutation::NominalParameterOrder => {
                    let parameters = registry
                        .nominal_parameters
                        .get_mut(&registry.nominals[0].id)
                        .unwrap();
                    parameters[1].id = parameters[0].id;
                }
                Mutation::InterfaceParameterOwner => {
                    modules[0].interface_facts[0].parameter.id =
                        TypeVariableId::resolved(ModuleId::new(99), 0);
                }
                Mutation::GlobalParameterOwner => {
                    modules[0].schemes[0]
                        .scheme
                        .type_parameters
                        .last_mut()
                        .unwrap()
                        .0 = TypeVariableId::resolved(ModuleId::new(99), 0);
                }
                Mutation::DuplicateGlobalParameterIdentity => {
                    let parameters = &mut modules[0].schemes[0].scheme.type_parameters;
                    parameters[1].0 = parameters[0].0;
                }
                Mutation::GeneratedGlobalParameterIdentity => {
                    modules[0].schemes[0].scheme.type_parameters[0].0 =
                        TypeVariableId::generated(99);
                }
                Mutation::NominalGlobalParameterIdentity => {
                    modules[0].schemes[0].scheme.type_parameters[0].0 = registry
                        .nominal_parameters
                        .get(&registry.nominals[0].id)
                        .and_then(|parameters| parameters.first())
                        .expect("the fixture has a nominal parameter")
                        .id;
                }
                Mutation::GlobalMirrorKind => {
                    modules[0].schemes[0].scheme.type_parameters[0].1 =
                        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
                }
                Mutation::ImplementationParameterOwner => {
                    modules[0].implementation_facts[0]
                        .head_parameters
                        .last_mut()
                        .unwrap()
                        .id = TypeVariableId::resolved(ModuleId::new(99), 0);
                }
                Mutation::ImplementationParameterOrder => {
                    let parameters = &mut modules[0].implementation_facts[0].head_parameters;
                    parameters[1].id = parameters[0].id;
                }
                Mutation::ImplementationMirrorSpelling => {
                    modules[0].implementation_facts[0].head_parameters[0].spelling =
                        "forged".to_owned();
                }
                Mutation::ImplementationMirrorOrigin => {
                    modules[0].implementation_facts[0].head_parameters[0].origin =
                        Origin::Generated {
                            cause: Box::new(Origin::Source(span)),
                            reason: crate::source::GeneratedReason::TypeChecking,
                        };
                }
                Mutation::ImplementationMirrorKind => {
                    modules[0].implementation_facts[0].head_parameters[0].kind =
                        Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
                }
            }

            for _ in 0..2 {
                let mut type_work = TypeWorkBudget::with_limit(expected_type_work);
                let mut constraint_work = crate::interface::InterfaceConstraintBudget::default();
                assert_eq!(
                    ResolvedRegistry::combine_checked(
                        &modules,
                        &mut type_work,
                        &mut constraint_work,
                    ),
                    Err(ResolvedBuildFailure::InvalidState),
                    "{mutation:?}",
                );
                assert_eq!(type_work.used(), expected_type_work, "{mutation:?}");
                assert_eq!(
                    constraint_work.used(),
                    expected_constraint_work,
                    "{mutation:?}",
                );
            }
            let mut type_work = TypeWorkBudget::with_limit(expected_type_work);
            let mut constraint_work = crate::interface::InterfaceConstraintBudget::with_limit(
                expected_constraint_work - 1,
            );
            assert_eq!(
                ResolvedRegistry::combine_checked(&modules, &mut type_work, &mut constraint_work,),
                Err(ResolvedBuildFailure::ConstraintResource),
                "{mutation:?}",
            );
            assert_eq!(type_work.used(), 0, "{mutation:?}");
        }
    }

    #[test]
    fn body_free_summary_admission_has_exact_independent_limits_and_is_reusable() {
        const CONSTRAINT_WORK: usize = 5;
        const TYPE_WORK: usize = 5;
        let source = SourceFile::new("summary-admission.ash", "unit")
            .expect("the summary fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the summary range should be ordered"))
            .expect("the summary span should fit");
        let module = ModuleId::new(900);
        let summary = ExportSummary::test_fixture(
            module,
            vec![(
                "unit",
                BinderId::resolved(module, 0),
                Type::Unit,
                Origin::Source(span),
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );

        let mut constraint_short =
            crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
        assert_eq!(
            summary.authenticate(
                &mut TypeWorkBudget::with_limit(TYPE_WORK),
                &mut constraint_short,
            ),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(constraint_short.used(), CONSTRAINT_WORK - 1);

        let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
        assert_eq!(
            summary.authenticate(
                &mut type_short,
                &mut crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK),
            ),
            Err(ResolvedBuildFailure::TypeResource),
        );
        assert_eq!(type_short.used(), TYPE_WORK - 1);

        for _ in 0..2 {
            let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
            let mut constraint_work =
                crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
            summary
                .authenticate(&mut type_work, &mut constraint_work)
                .expect("the immutable summary should remain reusable after admission");
            assert_eq!(type_work.used(), TYPE_WORK);
            assert_eq!(constraint_work.used(), CONSTRAINT_WORK);
        }
    }

    #[test]
    fn deep_body_free_summary_admission_and_rejection_are_exact_and_stack_safe() {
        const DEPTH: usize = 32_768;
        const CONSTRAINT_WORK: usize = 4 * DEPTH + 5;
        const TYPE_WORK: usize = 9 * DEPTH + 5;

        std::thread::Builder::new()
            .name("deep-summary-admission".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-summary-admission.ash", "deep")
                    .expect("the deep summary fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the deep range should be ordered"))
                    .expect("the deep span should fit");
                let module = ModuleId::new(901);
                let deep_type = |mut leaf| {
                    for _ in 0..DEPTH {
                        leaf = Type::Function(Box::new(Type::Int), Box::new(leaf));
                    }
                    leaf
                };
                let summary = ExportSummary::test_fixture(
                    module,
                    vec![(
                        "deep",
                        BinderId::resolved(module, 0),
                        deep_type(Type::Unit),
                        Origin::Source(span),
                    )],
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                );

                let mut constraint_short =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
                assert_eq!(
                    summary.authenticate(
                        &mut TypeWorkBudget::with_limit(TYPE_WORK),
                        &mut constraint_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(constraint_short.used(), CONSTRAINT_WORK - 1);

                let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
                assert_eq!(
                    summary.authenticate(
                        &mut type_short,
                        &mut crate::interface::InterfaceConstraintBudget::with_limit(
                            CONSTRAINT_WORK,
                        ),
                    ),
                    Err(ResolvedBuildFailure::TypeResource),
                );
                assert_eq!(type_short.used(), TYPE_WORK - 1);

                let mut exact_type = TypeWorkBudget::with_limit(TYPE_WORK);
                let mut exact_constraint =
                    crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
                summary
                    .authenticate(&mut exact_type, &mut exact_constraint)
                    .expect("the exact deep summary should authenticate");
                assert_eq!(exact_type.used(), TYPE_WORK);
                assert_eq!(exact_constraint.used(), CONSTRAINT_WORK);

                let invalid = ExportSummary::test_fixture(
                    module,
                    vec![(
                        "deep",
                        BinderId::resolved(module, 0),
                        deep_type(Type::Variable(TypeVariableId::resolved(module, 9))),
                        Origin::Source(span),
                    )],
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                );
                assert_eq!(
                    invalid.authenticate(
                        &mut TypeWorkBudget::default(),
                        &mut crate::interface::InterfaceConstraintBudget::default(),
                    ),
                    Err(ResolvedBuildFailure::InvalidState),
                );
            })
            .expect("the deep summary worker should spawn")
            .join()
            .expect("accepted and rejected deep summaries must tear down iteratively");
    }

    #[test]
    fn summary_carrier_comparisons_are_constraint_only_exact_and_stack_safe() {
        const DEPTH: usize = 32_768;
        const MIRROR_WORK: usize = 2 * DEPTH + 2;
        const SUBSTITUTION_WORK: usize = 4 * DEPTH + 4;
        const METHOD_REQUIREMENT_WORK: usize = 5 * DEPTH + 4;

        std::thread::Builder::new()
            .name("deep-summary-carrier-comparison".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("summary-carrier-comparison.ash", "F")
                    .expect("the comparison source should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the comparison range should be ordered"))
                    .expect("the comparison span should fit");
                let module = ModuleId::new(9_702);
                let parameter_id = TypeVariableId::resolved(module, 0);
                let deep_kind = || {
                    let mut kind = Kind::Type;
                    for _ in 0..DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    kind
                };
                let scheme = ConstrainedScheme {
                    type_parameters: Box::new([(parameter_id, deep_kind())]),
                    requirements: Box::new([]),
                    value_type: Type::Unit,
                };
                let parameters = [ResolvedTypeVariable {
                    id: parameter_id,
                    spelling: "F".to_owned(),
                    kind: deep_kind(),
                    origin: Origin::Source(span),
                }];

                let mut mirror_short =
                    crate::interface::InterfaceConstraintBudget::with_limit(MIRROR_WORK - 1);
                assert_eq!(
                    authenticate_scheme_parameter_mirror(&scheme, &parameters, &mut mirror_short,),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(mirror_short.used(), MIRROR_WORK - 2);
                let mut mirror_exact =
                    crate::interface::InterfaceConstraintBudget::with_limit(MIRROR_WORK);
                authenticate_scheme_parameter_mirror(&scheme, &parameters, &mut mirror_exact)
                    .expect("the exact scheme-mirror comparison should fit");
                assert_eq!(mirror_exact.used(), MIRROR_WORK);

                let deep_type = |mut leaf| {
                    for _ in 0..DEPTH {
                        leaf = Type::Function(Box::new(Type::Int), Box::new(leaf));
                    }
                    leaf
                };
                let expected = deep_type(Type::Variable(parameter_id));
                let actual = deep_type(Type::Unit);
                let mut substitution_short =
                    crate::interface::InterfaceConstraintBudget::with_limit(SUBSTITUTION_WORK - 1);
                assert_eq!(
                    same_summary_type_after_single_substitution(
                        &expected,
                        parameter_id,
                        &Type::Unit,
                        &actual,
                        &mut substitution_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(substitution_short.used(), SUBSTITUTION_WORK - 1);
                let mut substitution_exact =
                    crate::interface::InterfaceConstraintBudget::with_limit(SUBSTITUTION_WORK);
                assert_eq!(
                    same_summary_type_after_single_substitution(
                        &expected,
                        parameter_id,
                        &Type::Unit,
                        &actual,
                        &mut substitution_exact,
                    ),
                    Ok(true),
                );
                assert_eq!(substitution_exact.used(), SUBSTITUTION_WORK);
                discard_type_iteratively(expected);
                discard_type_iteratively(actual);
                drop(scheme);
                drop(parameters);

                let deep_origin = || {
                    let mut origin = Origin::Source(span);
                    for _ in 0..DEPTH {
                        origin = Origin::Generated {
                            cause: Box::new(origin),
                            reason: GeneratedReason::TypeChecking,
                        };
                    }
                    origin
                };
                let requirement_id = RequirementId::new(
                    crate::interface::RequirementOwner::Global(BinderId::resolved(module, 0)),
                    0,
                );
                let interface = InterfaceId::new(module, 0);
                let method_requirement = CheckedRequirement {
                    id: requirement_id,
                    interface,
                    argument: deep_type(Type::Unit),
                    origin: deep_origin(),
                    span,
                };
                let prerequisite = CheckedRequirement {
                    id: requirement_id,
                    interface,
                    argument: deep_type(Type::Unit),
                    origin: deep_origin(),
                    span,
                };
                let mut requirement_short = crate::interface::InterfaceConstraintBudget::with_limit(
                    METHOD_REQUIREMENT_WORK - 1,
                );
                assert_eq!(
                    authenticate_method_requirement_mirror(
                        &method_requirement,
                        &prerequisite,
                        &mut requirement_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(requirement_short.used(), METHOD_REQUIREMENT_WORK - 1);
                let mut requirement_exact = crate::interface::InterfaceConstraintBudget::with_limit(
                    METHOD_REQUIREMENT_WORK,
                );
                authenticate_method_requirement_mirror(
                    &method_requirement,
                    &prerequisite,
                    &mut requirement_exact,
                )
                .expect("the exact method-requirement mirror should authenticate");
                assert_eq!(requirement_exact.used(), METHOD_REQUIREMENT_WORK);
            })
            .expect("the deep summary-comparison worker should start")
            .join()
            .expect("summary comparison success and rejection must fit 256 KiB");
    }

    #[test]
    fn summary_duplicate_indexes_are_linear_exact_and_stack_safe() {
        const WIDTH: usize = 32_768;
        std::thread::Builder::new()
            .name("wide-summary-duplicate-indexes".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("summary-duplicate-indexes.ash", "facts")
                    .expect("the duplicate-index source should fit");
                let span = source
                    .span(ByteRange::new(0, 5).expect("the duplicate-index range should order"))
                    .expect("the duplicate-index span should fit");
                let module = ModuleId::new(9_703);
                let global = BinderId::resolved(module, 0);
                let requirement = |index: usize, interface: InterfaceId| CheckedRequirement {
                    id: RequirementId::new(
                        crate::interface::RequirementOwner::Global(global),
                        u32::try_from(index).expect("the requirement ordinal should fit"),
                    ),
                    interface,
                    argument: Type::Unit,
                    origin: Origin::Source(span),
                    span,
                };
                let implementation =
                    |index: usize, interface: InterfaceId| CheckedImplementationFact {
                        id: ImplId::new(
                            module,
                            u32::try_from(index).expect("the implementation ordinal should fit"),
                        ),
                        interface,
                        head_parameters: Box::new([]),
                        argument: Type::Unit,
                        prerequisites: Box::new([]),
                        methods: Box::new([]),
                        origin: Origin::Source(span),
                        span,
                    };

                let distinct_requirements = (0..WIDTH)
                    .map(|index| {
                        requirement(
                            index,
                            InterfaceId::new(module, u32::try_from(index).unwrap()),
                        )
                    })
                    .collect::<Vec<_>>();
                let mut distinct_short =
                    crate::interface::InterfaceConstraintBudget::with_limit(2 * WIDTH - 1);
                assert_eq!(
                    authenticate_unique_summary_requirements(
                        &distinct_requirements,
                        &mut distinct_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(distinct_short.used(), 2 * WIDTH - 2);
                let mut distinct_exact =
                    crate::interface::InterfaceConstraintBudget::with_limit(2 * WIDTH);
                authenticate_unique_summary_requirements(
                    &distinct_requirements,
                    &mut distinct_exact,
                )
                .expect("the exact all-distinct requirement index should fit");
                assert_eq!(distinct_exact.used(), 2 * WIDTH);

                let mut late_requirements = distinct_requirements;
                late_requirements.push(requirement(WIDTH, InterfaceId::new(module, 0)));
                let requirement_conflict_work = 2 * WIDTH + 2;
                let mut requirement_short = crate::interface::InterfaceConstraintBudget::with_limit(
                    requirement_conflict_work - 1,
                );
                assert_eq!(
                    authenticate_unique_summary_requirements(
                        &late_requirements,
                        &mut requirement_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(requirement_short.used(), requirement_conflict_work - 1);
                let mut requirement_exact = crate::interface::InterfaceConstraintBudget::with_limit(
                    requirement_conflict_work,
                );
                assert_eq!(
                    authenticate_unique_summary_requirements(
                        &late_requirements,
                        &mut requirement_exact,
                    ),
                    Err(ResolvedBuildFailure::InvalidState),
                );
                assert_eq!(requirement_exact.used(), requirement_conflict_work);

                let distinct_implementations = (0..WIDTH)
                    .map(|index| {
                        implementation(
                            index,
                            InterfaceId::new(module, u32::try_from(index).unwrap()),
                        )
                    })
                    .collect::<Vec<_>>();
                let mut implementation_short =
                    crate::interface::InterfaceConstraintBudget::with_limit(2 * WIDTH - 1);
                assert_eq!(
                    authenticate_nonoverlapping_summary_implementations(
                        &distinct_implementations,
                        &mut implementation_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(implementation_short.used(), 2 * WIDTH - 2);
                let mut implementation_exact =
                    crate::interface::InterfaceConstraintBudget::with_limit(2 * WIDTH);
                authenticate_nonoverlapping_summary_implementations(
                    &distinct_implementations,
                    &mut implementation_exact,
                )
                .expect("the exact all-distinct implementation index should fit");
                assert_eq!(implementation_exact.used(), 2 * WIDTH);

                let mut late_implementations = distinct_implementations;
                late_implementations.push(implementation(WIDTH, InterfaceId::new(module, 0)));
                let overlap_work = 2 * WIDTH + 4;
                let mut overlap_short =
                    crate::interface::InterfaceConstraintBudget::with_limit(overlap_work - 1);
                assert_eq!(
                    authenticate_nonoverlapping_summary_implementations(
                        &late_implementations,
                        &mut overlap_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(overlap_short.used(), overlap_work - 1);
                let mut overlap_exact =
                    crate::interface::InterfaceConstraintBudget::with_limit(overlap_work);
                assert_eq!(
                    authenticate_nonoverlapping_summary_implementations(
                        &late_implementations,
                        &mut overlap_exact,
                    ),
                    Err(ResolvedBuildFailure::InvalidState),
                );
                assert_eq!(overlap_exact.used(), overlap_work);
            })
            .expect("the wide duplicate-index worker should start")
            .join()
            .expect("wide duplicate indexes must fit a 256 KiB stack");
    }

    #[test]
    fn duplicate_summary_fact_comparisons_are_constraint_only_exact_and_atomic() {
        let source = SourceFile::new("duplicate-facts.ash", "facts")
            .expect("the duplicate fact source should fit");
        let span = source
            .span(ByteRange::new(0, 5).expect("the duplicate range should be ordered"))
            .expect("the duplicate span should fit");
        let module = ModuleId::new(902);
        let parameter = TypeVariableId::resolved(module, 0);
        let binder = BinderId::resolved(module, 0);
        let nominal = NominalTypeId::new(module, 0);
        let constructor_id = ConstructorId::new(nominal, 0);
        let interface_id = InterfaceId::new(module, 0);
        let method_id = MethodId::new(interface_id, 0);
        let implementation_id = ImplId::new(module, 0);

        let value_type = || {
            Type::Function(
                Box::new(Type::Variable(parameter)),
                Box::new(Type::Variable(parameter)),
            )
        };
        let global_scheme = || ConstrainedScheme {
            type_parameters: Box::new([(parameter, Kind::Type)]),
            requirements: Box::new([]),
            value_type: value_type(),
        };
        let imported_global = ImportedGlobalScheme {
            binder,
            scheme: global_scheme(),
            origin: Origin::Source(span),
        };
        let mut exported_global = ExportedGlobal {
            binder,
            scheme: global_scheme(),
            origin: Origin::Source(span),
        };

        let constructor_scheme = || ConstrainedScheme {
            type_parameters: Box::new([(parameter, Kind::Type)]),
            requirements: Box::new([]),
            value_type: Type::Function(
                Box::new(Type::Variable(parameter)),
                Box::new(Type::Application(
                    Box::new(Type::Nominal(nominal)),
                    Box::new(Type::Variable(parameter)),
                )),
            ),
        };
        let imported_constructor = ImportedConstructorFact {
            id: constructor_id,
            spelling: "Wrap".to_owned(),
            payload: Some(Type::Variable(parameter)),
            scheme: constructor_scheme(),
            origin: Origin::Source(span),
        };
        let mut exported_constructor = ExportedConstructor {
            id: constructor_id,
            spelling: "Wrap".to_owned(),
            payload: Some(Type::Variable(parameter)),
            scheme: constructor_scheme(),
            origin: Origin::Source(span),
        };

        let interface_fact = || CheckedInterfaceFact {
            id: interface_id,
            spelling: "Observe".to_owned(),
            parameter: ResolvedTypeVariable {
                id: parameter,
                spelling: "A".to_owned(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
            methods: Box::new([CheckedInterfaceMethodFact {
                id: method_id,
                spelling: "observe".to_owned(),
                type_parameters: Box::new([]),
                value_type: value_type(),
                origin: Origin::Source(span),
                span,
            }]),
            method_binder_authorities: Box::new([MethodBinderAuthority {
                method: method_id,
                parameters: Box::new([]),
            }]),
            origin: Origin::Source(span),
            span,
        };
        let left_interface = interface_fact();
        let mut right_interface = interface_fact();

        let head_argument = || {
            Type::Application(
                Box::new(Type::Nominal(nominal)),
                Box::new(Type::Variable(parameter)),
            )
        };
        let implementation_fact = || CheckedImplementationFact {
            id: implementation_id,
            interface: interface_id,
            head_parameters: Box::new([ResolvedTypeVariable {
                id: parameter,
                spelling: "A".to_owned(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            }]),
            argument: head_argument(),
            prerequisites: Box::new([]),
            methods: Box::new([CheckedImplementationMethodFact {
                id: ImplMethodId::new(implementation_id, method_id),
                method: method_id,
                binder: BinderId::resolved(module, 1),
                scheme: ConstrainedScheme {
                    type_parameters: Box::new([(parameter, Kind::Type)]),
                    requirements: Box::new([]),
                    value_type: Type::Function(
                        Box::new(head_argument()),
                        Box::new(head_argument()),
                    ),
                },
                head_type_parameter_count: 1,
                origin: Origin::Source(span),
                span,
            }]),
            origin: Origin::Source(span),
            span,
        };
        let left_implementation = implementation_fact();
        let mut right_implementation = implementation_fact();

        let assert_exact = |expected,
                            compare: &mut dyn FnMut(
            &mut TypeWorkBudget,
            &mut crate::interface::InterfaceConstraintBudget,
        )
            -> Result<bool, ResolvedBuildFailure>| {
            let mut type_work = TypeWorkBudget::with_limit(0);
            let mut short = crate::interface::InterfaceConstraintBudget::with_limit(expected - 1);
            assert_eq!(
                compare(&mut type_work, &mut short),
                Err(ResolvedBuildFailure::ConstraintResource),
            );
            assert_eq!(type_work.used(), 0);
            assert_eq!(short.used(), expected - 1);

            let mut type_work = TypeWorkBudget::with_limit(0);
            let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(expected);
            assert_eq!(compare(&mut type_work, &mut exact), Ok(true));
            assert_eq!(type_work.used(), 0);
            assert_eq!(exact.used(), expected);
        };

        assert_exact(11, &mut |type_work, constraint_work| {
            same_imported_global_fact_with_budget(
                &imported_global,
                &exported_global,
                type_work,
                constraint_work,
            )
        });
        assert_exact(17, &mut |type_work, constraint_work| {
            same_imported_constructor_fact_with_budget(
                &imported_constructor,
                &exported_constructor,
                type_work,
                constraint_work,
            )
        });
        assert_exact(15, &mut |type_work, constraint_work| {
            same_checked_interface_fact_with_budget(
                &left_interface,
                &right_interface,
                type_work,
                constraint_work,
            )
        });
        assert_exact(30, &mut |type_work, constraint_work| {
            same_checked_implementation_fact_with_budget(
                &left_implementation,
                &right_implementation,
                type_work,
                constraint_work,
            )
        });

        exported_global.binder = BinderId::resolved(module, u32::MAX);
        exported_constructor.id = ConstructorId::new(nominal, u32::MAX);
        right_interface.id = InterfaceId::new(module, u32::MAX);
        right_implementation.id = ImplId::new(module, u32::MAX);
        let mut type_work = TypeWorkBudget::with_limit(0);
        let mut constraint_work = crate::interface::InterfaceConstraintBudget::with_limit(0);
        assert_eq!(
            same_imported_global_fact_with_budget(
                &imported_global,
                &exported_global,
                &mut type_work,
                &mut constraint_work,
            ),
            Ok(false),
        );
        assert_eq!(
            same_imported_constructor_fact_with_budget(
                &imported_constructor,
                &exported_constructor,
                &mut type_work,
                &mut constraint_work,
            ),
            Ok(false),
        );
        assert_eq!(
            same_checked_interface_fact_with_budget(
                &left_interface,
                &right_interface,
                &mut type_work,
                &mut constraint_work,
            ),
            Ok(false),
        );
        assert_eq!(
            same_checked_implementation_fact_with_budget(
                &left_implementation,
                &right_implementation,
                &mut type_work,
                &mut constraint_work,
            ),
            Ok(false),
        );
        assert_eq!(type_work.used(), 0);
        assert_eq!(constraint_work.used(), 0);
    }

    #[test]
    fn deep_duplicate_summary_comparison_is_reusable_and_stack_safe() {
        const DEPTH: usize = 32_768;
        const EXACT_CONSTRAINT_WORK: usize = DEPTH + 4;
        std::thread::Builder::new()
            .name("deep-duplicate-summary".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-duplicate.ash", "deep")
                    .expect("the deep duplicate source should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the deep range should be ordered"))
                    .expect("the deep span should fit");
                let module = ModuleId::new(903);
                let deep_origin = || {
                    let mut origin = Origin::Source(span);
                    for _ in 0..DEPTH {
                        origin = Origin::Generated {
                            cause: Box::new(origin),
                            reason: GeneratedReason::TypeChecking,
                        };
                    }
                    origin
                };
                let imported = ImportedGlobalScheme {
                    binder: BinderId::resolved(module, 0),
                    scheme: ConstrainedScheme::from_rank1_type(Type::Unit),
                    origin: deep_origin(),
                };
                let exported = ExportedGlobal {
                    binder: BinderId::resolved(module, 0),
                    scheme: ConstrainedScheme::from_rank1_type(Type::Unit),
                    origin: deep_origin(),
                };
                let mut type_work = TypeWorkBudget::with_limit(0);
                let mut short = crate::interface::InterfaceConstraintBudget::with_limit(
                    EXACT_CONSTRAINT_WORK - 1,
                );
                assert_eq!(
                    same_imported_global_fact_with_budget(
                        &imported,
                        &exported,
                        &mut type_work,
                        &mut short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(type_work.used(), 0);
                assert_eq!(short.used(), EXACT_CONSTRAINT_WORK - 1);
                for _ in 0..2 {
                    let mut type_work = TypeWorkBudget::with_limit(0);
                    let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(
                        EXACT_CONSTRAINT_WORK,
                    );
                    assert_eq!(
                        same_imported_global_fact_with_budget(
                            &imported,
                            &exported,
                            &mut type_work,
                            &mut exact,
                        ),
                        Ok(true),
                    );
                    assert_eq!(type_work.used(), 0);
                    assert_eq!(exact.used(), EXACT_CONSTRAINT_WORK);
                }
                discard_imported_global(imported);
                let ExportedGlobal { scheme, origin, .. } = exported;
                drop(scheme);
                discard_origin_iteratively(origin);
            })
            .expect("the deep duplicate worker should spawn")
            .join()
            .expect("accepted and rejected duplicate comparisons must tear down iteratively");
    }

    #[test]
    fn deep_duplicate_fact_kind_and_type_comparisons_are_exact_reusable_and_stack_safe() {
        const DEPTH: usize = 32_766;
        const KIND_CELLS: usize = 2 * DEPTH + 1;
        // Applying F to DEPTH Type arguments costs 4D+2 comparison cells.
        // One outer Function and a Unit -> Unit codomain add eight cells.
        const APPLIED_PARAMETER_CELLS: usize = 4 * DEPTH + 2;
        const PUBLIC_VALUE_CELLS: usize = APPLIED_PARAMETER_CELLS + 8;
        const CONSTRUCTOR_RESULT_CELLS: usize = 6;
        const CONSTRUCTOR_SCHEME_CELLS: usize =
            APPLIED_PARAMETER_CELLS + CONSTRUCTOR_RESULT_CELLS + 2;
        const GLOBAL_FIXED_CELLS: usize = 4;
        const CONSTRUCTOR_FIXED_CELLS: usize = 4;
        // Two private method-authority rows precede ordinary interface fact
        // comparison, one for each authenticated route.
        const INTERFACE_FIXED_CELLS: usize = 8;
        const GLOBAL_WORK: usize = GLOBAL_FIXED_CELLS + KIND_CELLS + PUBLIC_VALUE_CELLS;
        const CONSTRUCTOR_WORK: usize = CONSTRUCTOR_FIXED_CELLS
            + KIND_CELLS
            + CONSTRUCTOR_SCHEME_CELLS
            + APPLIED_PARAMETER_CELLS;
        const CONSTRUCTOR_SCHEME_MISMATCH_WORK: usize = CONSTRUCTOR_FIXED_CELLS + KIND_CELLS + 2;
        const INTERFACE_WORK: usize = INTERFACE_FIXED_CELLS + KIND_CELLS + PUBLIC_VALUE_CELLS;
        // The higher-kinded implementation retains two K_D mirrors. Its head
        // lift(F) is shallow, while use(lift(F)) -> (Unit -> Unit) owns 4D+14
        // Type cells after substituting the interface parameter.
        const IMPLEMENTATION_HEAD_TYPE_CELLS: usize = 6;
        const IMPLEMENTATION_METHOD_CELLS: usize = 4 * DEPTH + 14;
        const IMPLEMENTATION_FIXED_CELLS: usize = 8;
        const IMPLEMENTATION_WORK: usize = IMPLEMENTATION_FIXED_CELLS
            + 2 * KIND_CELLS
            + IMPLEMENTATION_HEAD_TYPE_CELLS
            + IMPLEMENTATION_METHOD_CELLS;

        std::thread::Builder::new()
            .name("deep-duplicate-fact-carriers".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-duplicate-carriers.ash", "deep")
                    .expect("the deep comparison source should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the deep range should be ordered"))
                    .expect("the deep span should fit");
                let module = ModuleId::new(904);
                let parameter = TypeVariableId::resolved(module, 0);
                let nominal = NominalTypeId::new(module, 0);
                let constructor = ConstructorId::new(nominal, 0);
                let interface = InterfaceId::new(module, 0);
                let method = MethodId::new(interface, 0);
                let implementation = ImplId::new(module, 0);
                let deep_kind = || {
                    let mut kind = Kind::Type;
                    for _ in 0..DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    kind
                };
                let applied_parameter = || {
                    let mut ty = Type::Variable(parameter);
                    for _ in 0..DEPTH {
                        ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
                    }
                    ty
                };
                let public_value_type = || {
                    Type::Function(
                        Box::new(applied_parameter()),
                        Box::new(Type::Function(Box::new(Type::Unit), Box::new(Type::Unit))),
                    )
                };
                let assert_exact =
                    |label: &str,
                     expected,
                     compare: &mut dyn FnMut(
                        &mut TypeWorkBudget,
                        &mut crate::interface::InterfaceConstraintBudget,
                    )
                        -> Result<bool, ResolvedBuildFailure>| {
                        let mut measured_type = TypeWorkBudget::with_limit(0);
                        let mut measured_constraint =
                            crate::interface::InterfaceConstraintBudget::default();
                        assert_eq!(
                            compare(&mut measured_type, &mut measured_constraint),
                            Ok(true),
                            "{label}",
                        );
                        assert_eq!(measured_type.used(), 0, "{label}");
                        assert_eq!(measured_constraint.used(), expected, "{label}");
                        let mut type_work = TypeWorkBudget::with_limit(0);
                        let mut short =
                            crate::interface::InterfaceConstraintBudget::with_limit(expected - 1);
                        assert_eq!(
                            compare(&mut type_work, &mut short),
                            Err(ResolvedBuildFailure::ConstraintResource),
                        );
                        assert_eq!(type_work.used(), 0);
                        assert_eq!(short.used(), expected - 1);
                        for _ in 0..2 {
                            let mut type_work = TypeWorkBudget::with_limit(0);
                            let mut exact =
                                crate::interface::InterfaceConstraintBudget::with_limit(expected);
                            assert_eq!(compare(&mut type_work, &mut exact), Ok(true));
                            assert_eq!(type_work.used(), 0);
                            assert_eq!(exact.used(), expected);
                        }
                    };

                let global_scheme = || ConstrainedScheme {
                    type_parameters: Box::new([(parameter, deep_kind())]),
                    requirements: Box::new([]),
                    value_type: public_value_type(),
                };
                let imported_global = ImportedGlobalScheme {
                    binder: BinderId::resolved(module, 0),
                    scheme: global_scheme(),
                    origin: Origin::Source(span),
                };
                let exported_global = ExportedGlobal {
                    binder: BinderId::resolved(module, 0),
                    scheme: global_scheme(),
                    origin: Origin::Source(span),
                };
                assert_exact("global", GLOBAL_WORK, &mut |type_work, constraint_work| {
                    same_imported_global_fact_with_budget(
                        &imported_global,
                        &exported_global,
                        type_work,
                        constraint_work,
                    )
                });
                discard_imported_global(imported_global);
                let ExportedGlobal { scheme, origin, .. } = exported_global;
                drop(scheme);
                discard_origin_iteratively(origin);

                let constructor_scheme = || ConstrainedScheme {
                    type_parameters: Box::new([(parameter, deep_kind())]),
                    requirements: Box::new([]),
                    value_type: Type::Function(
                        Box::new(applied_parameter()),
                        Box::new(Type::Application(
                            Box::new(Type::Nominal(nominal)),
                            Box::new(Type::Variable(parameter)),
                        )),
                    ),
                };
                let imported_constructor = ImportedConstructorFact {
                    id: constructor,
                    spelling: "Deep".to_owned(),
                    payload: Some(applied_parameter()),
                    scheme: constructor_scheme(),
                    origin: Origin::Source(span),
                };
                let mut exported_constructor = ExportedConstructor {
                    id: constructor,
                    spelling: "Deep".to_owned(),
                    payload: Some(applied_parameter()),
                    scheme: constructor_scheme(),
                    origin: Origin::Source(span),
                };
                assert_exact(
                    "constructor",
                    CONSTRUCTOR_WORK,
                    &mut |type_work, constraint_work| {
                        same_imported_constructor_fact_with_budget(
                            &imported_constructor,
                            &exported_constructor,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                discard_type_iteratively(std::mem::replace(
                    &mut exported_constructor.scheme.value_type,
                    Type::Unit,
                ));
                let mut type_work = TypeWorkBudget::with_limit(0);
                let mut prefix_short = crate::interface::InterfaceConstraintBudget::with_limit(
                    CONSTRUCTOR_SCHEME_MISMATCH_WORK - 1,
                );
                assert_eq!(
                    same_imported_constructor_fact_with_budget(
                        &imported_constructor,
                        &exported_constructor,
                        &mut type_work,
                        &mut prefix_short,
                    ),
                    Err(ResolvedBuildFailure::ConstraintResource),
                );
                assert_eq!(prefix_short.used(), CONSTRUCTOR_SCHEME_MISMATCH_WORK - 1);
                let mut prefix_exact = crate::interface::InterfaceConstraintBudget::with_limit(
                    CONSTRUCTOR_SCHEME_MISMATCH_WORK,
                );
                assert_eq!(
                    same_imported_constructor_fact_with_budget(
                        &imported_constructor,
                        &exported_constructor,
                        &mut TypeWorkBudget::with_limit(0),
                        &mut prefix_exact,
                    ),
                    Ok(false),
                    "the scheme mismatch must reject before the deep payload comparison",
                );
                assert_eq!(prefix_exact.used(), CONSTRUCTOR_SCHEME_MISMATCH_WORK);
                imported_constructor.discard_iteratively();
                exported_constructor.discard_iteratively();

                let interface_fact = || CheckedInterfaceFact {
                    id: interface,
                    spelling: "DeepInterface".to_owned(),
                    parameter: ResolvedTypeVariable {
                        id: parameter,
                        spelling: "F".to_owned(),
                        kind: deep_kind(),
                        origin: Origin::Source(span),
                    },
                    methods: Box::new([CheckedInterfaceMethodFact {
                        id: method,
                        spelling: "deep".to_owned(),
                        type_parameters: Box::new([]),
                        value_type: public_value_type(),
                        origin: Origin::Source(span),
                        span,
                    }]),
                    method_binder_authorities: Box::new([MethodBinderAuthority {
                        method,
                        parameters: Box::new([]),
                    }]),
                    origin: Origin::Source(span),
                    span,
                };
                let left_interface = interface_fact();
                let right_interface = interface_fact();
                assert_exact(
                    "interface",
                    INTERFACE_WORK,
                    &mut |type_work, constraint_work| {
                        same_checked_interface_fact_with_budget(
                            &left_interface,
                            &right_interface,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                drop(left_interface);
                drop(right_interface);

                let lifted_parameter = || {
                    Type::Application(
                        Box::new(Type::Nominal(nominal)),
                        Box::new(Type::Variable(parameter)),
                    )
                };
                let used_lifted_parameter = || {
                    let mut head = lifted_parameter();
                    for _ in 0..DEPTH {
                        head = Type::Application(Box::new(head), Box::new(Type::Unit));
                    }
                    head
                };
                let implementation_fact = || CheckedImplementationFact {
                    id: implementation,
                    interface,
                    head_parameters: Box::new([ResolvedTypeVariable {
                        id: parameter,
                        spelling: "F".to_owned(),
                        kind: deep_kind(),
                        origin: Origin::Source(span),
                    }]),
                    argument: lifted_parameter(),
                    prerequisites: Box::new([]),
                    methods: Box::new([CheckedImplementationMethodFact {
                        id: ImplMethodId::new(implementation, method),
                        method,
                        binder: BinderId::resolved(module, 1),
                        scheme: ConstrainedScheme {
                            type_parameters: Box::new([(parameter, deep_kind())]),
                            requirements: Box::new([]),
                            value_type: Type::Function(
                                Box::new(used_lifted_parameter()),
                                Box::new(Type::Function(
                                    Box::new(Type::Unit),
                                    Box::new(Type::Unit),
                                )),
                            ),
                        },
                        head_type_parameter_count: 1,
                        origin: Origin::Source(span),
                        span,
                    }]),
                    origin: Origin::Source(span),
                    span,
                };
                let left_implementation = implementation_fact();
                let right_implementation = implementation_fact();
                assert_exact(
                    "implementation",
                    IMPLEMENTATION_WORK,
                    &mut |type_work, constraint_work| {
                        same_checked_implementation_fact_with_budget(
                            &left_implementation,
                            &right_implementation,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                drop(left_implementation);
                drop(right_implementation);
            })
            .expect("the deep carrier worker should spawn")
            .join()
            .expect("all deep comparison carriers must tear down iteratively");
    }

    #[test]
    fn wide_duplicate_fact_metadata_comparisons_are_exact_reusable_and_stack_safe() {
        const WIDTH: usize = 32_768;
        const GLOBAL_FIXED_CELLS: usize = 8;
        const GLOBAL_REQUIREMENT_CELLS: usize = 5;
        const INTERFACE_FIXED_CELLS: usize = 5;
        // Each method costs its two private authority rows plus the predecessor
        // eight-cell checked mirror comparison.
        const INTERFACE_METHOD_CELLS: usize = 10;
        const PREREQUISITE_IMPLEMENTATION_FIXED_CELLS: usize = 30;
        const METHOD_IMPLEMENTATION_FIXED_CELLS: usize = 4;
        const IMPLEMENTATION_MEMBER_CELLS: usize = 8;
        const GLOBAL_WORK: usize = GLOBAL_FIXED_CELLS + GLOBAL_REQUIREMENT_CELLS * WIDTH;
        const INTERFACE_WORK: usize = INTERFACE_FIXED_CELLS + INTERFACE_METHOD_CELLS * WIDTH;
        const PREREQUISITE_IMPLEMENTATION_WORK: usize =
            PREREQUISITE_IMPLEMENTATION_FIXED_CELLS + IMPLEMENTATION_MEMBER_CELLS * WIDTH;
        const METHOD_IMPLEMENTATION_WORK: usize =
            METHOD_IMPLEMENTATION_FIXED_CELLS + IMPLEMENTATION_MEMBER_CELLS * WIDTH;
        const GLOBAL_FIRST_ARGUMENT_MISMATCH_WORK: usize = WIDTH + 6;
        const INTERFACE_FIRST_METHOD_MISMATCH_WORK: usize = 3 * WIDTH + 5;
        const PREREQUISITE_TOP_MISMATCH_WORK: usize = WIDTH + 13;
        const PREREQUISITE_METHOD_MISMATCH_WORK: usize = 4 * WIDTH + 17;
        const IMPLEMENTATION_FIRST_METHOD_MISMATCH_WORK: usize = WIDTH + 4;

        std::thread::Builder::new()
            .name("wide-duplicate-fact-carriers".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("wide-duplicate-carriers.ash", "wide")
                    .expect("the wide comparison source should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the wide range should be ordered"))
                    .expect("the wide span should fit");
                let module = ModuleId::new(905);
                let binder = BinderId::resolved(module, 0);
                let parameter = TypeVariableId::resolved(module, 0);
                let nominal = NominalTypeId::new(module, 0);
                let interface = InterfaceId::new(module, 0);
                let implementation = ImplId::new(module, 0);
                let function_type = || Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
                let head_type = || {
                    Type::Application(
                        Box::new(Type::Nominal(nominal)),
                        Box::new(Type::Variable(parameter)),
                    )
                };
                let assert_exact =
                    |label: &str,
                     expected,
                     compare: &mut dyn FnMut(
                        &mut TypeWorkBudget,
                        &mut crate::interface::InterfaceConstraintBudget,
                    )
                        -> Result<bool, ResolvedBuildFailure>| {
                        let mut type_work = TypeWorkBudget::with_limit(0);
                        let mut short =
                            crate::interface::InterfaceConstraintBudget::with_limit(expected - 1);
                        assert_eq!(
                            compare(&mut type_work, &mut short),
                            Err(ResolvedBuildFailure::ConstraintResource),
                            "{label}",
                        );
                        assert_eq!(type_work.used(), 0, "{label}");
                        assert_eq!(short.used(), expected - 1, "{label}");
                        for _ in 0..2 {
                            let mut type_work = TypeWorkBudget::with_limit(0);
                            let mut exact =
                                crate::interface::InterfaceConstraintBudget::with_limit(expected);
                            assert_eq!(compare(&mut type_work, &mut exact), Ok(true), "{label}",);
                            assert_eq!(type_work.used(), 0, "{label}");
                            assert_eq!(exact.used(), expected, "{label}");
                        }
                    };
                let assert_prefix =
                    |label: &str,
                     expected,
                     compare: &mut dyn FnMut(
                        &mut TypeWorkBudget,
                        &mut crate::interface::InterfaceConstraintBudget,
                    )
                        -> Result<bool, ResolvedBuildFailure>| {
                        let mut type_work = TypeWorkBudget::with_limit(0);
                        let mut short =
                            crate::interface::InterfaceConstraintBudget::with_limit(expected - 1);
                        assert_eq!(
                            compare(&mut type_work, &mut short),
                            Err(ResolvedBuildFailure::ConstraintResource),
                            "{label}",
                        );
                        assert_eq!(type_work.used(), 0, "{label}");
                        assert_eq!(short.used(), expected - 1, "{label}");
                        let mut type_work = TypeWorkBudget::with_limit(0);
                        let mut exact =
                            crate::interface::InterfaceConstraintBudget::with_limit(expected);
                        assert_eq!(compare(&mut type_work, &mut exact), Ok(false), "{label}",);
                        assert_eq!(type_work.used(), 0, "{label}");
                        assert_eq!(exact.used(), expected, "{label}");
                    };

                let requirements = |owner| {
                    let mut requirements = Vec::new();
                    requirements
                        .try_reserve(WIDTH)
                        .expect("the wide requirement fixture should fit");
                    for ordinal in 0..WIDTH {
                        requirements.push(CheckedRequirement {
                            id: RequirementId::new(owner, ordinal as u32),
                            interface: InterfaceId::new(module, ordinal as u32),
                            argument: Type::Unit,
                            origin: Origin::Source(span),
                            span,
                        });
                    }
                    requirements.into_boxed_slice()
                };
                let global_scheme = || ConstrainedScheme {
                    type_parameters: Box::new([]),
                    requirements: requirements(RequirementOwner::Global(binder)),
                    value_type: function_type(),
                };
                let imported_global = ImportedGlobalScheme {
                    binder,
                    scheme: global_scheme(),
                    origin: Origin::Source(span),
                };
                let mut exported_global = ExportedGlobal {
                    binder,
                    scheme: global_scheme(),
                    origin: Origin::Source(span),
                };
                assert_exact("global", GLOBAL_WORK, &mut |type_work, constraint_work| {
                    same_imported_global_fact_with_budget(
                        &imported_global,
                        &exported_global,
                        type_work,
                        constraint_work,
                    )
                });
                discard_type_iteratively(std::mem::replace(
                    &mut exported_global.scheme.requirements[0].argument,
                    Type::Bool,
                ));
                assert_prefix(
                    "global first requirement argument",
                    GLOBAL_FIRST_ARGUMENT_MISMATCH_WORK,
                    &mut |type_work, constraint_work| {
                        same_imported_global_fact_with_budget(
                            &imported_global,
                            &exported_global,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                discard_imported_global(imported_global);
                let ExportedGlobal { scheme, origin, .. } = exported_global;
                drop(scheme);
                discard_origin_iteratively(origin);

                let interface_fact = || {
                    let mut methods = Vec::new();
                    methods
                        .try_reserve(WIDTH)
                        .expect("the wide interface fixture should fit");
                    for ordinal in 0..WIDTH {
                        methods.push(CheckedInterfaceMethodFact {
                            id: MethodId::new(interface, ordinal as u32),
                            spelling: format!("method{ordinal}"),
                            type_parameters: Box::new([]),
                            value_type: Type::Function(
                                Box::new(Type::Variable(parameter)),
                                Box::new(Type::Variable(parameter)),
                            ),
                            origin: Origin::Source(span),
                            span,
                        });
                    }
                    let method_binder_authorities = methods
                        .iter()
                        .map(|method| MethodBinderAuthority {
                            method: method.id,
                            parameters: Box::new([]),
                        })
                        .collect::<Vec<_>>()
                        .into_boxed_slice();
                    CheckedInterfaceFact {
                        id: interface,
                        spelling: "Wide".to_owned(),
                        parameter: ResolvedTypeVariable {
                            id: parameter,
                            spelling: "A".to_owned(),
                            kind: Kind::Type,
                            origin: Origin::Source(span),
                        },
                        methods: methods.into_boxed_slice(),
                        method_binder_authorities,
                        origin: Origin::Source(span),
                        span,
                    }
                };
                let left_interface = interface_fact();
                let mut right_interface = interface_fact();
                assert_exact(
                    "interface",
                    INTERFACE_WORK,
                    &mut |type_work, constraint_work| {
                        same_checked_interface_fact_with_budget(
                            &left_interface,
                            &right_interface,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                right_interface.methods[0].id = MethodId::new(interface, u32::MAX);
                right_interface.method_binder_authorities[0].method =
                    MethodId::new(interface, u32::MAX);
                assert_prefix(
                    "interface first method identity",
                    INTERFACE_FIRST_METHOD_MISMATCH_WORK,
                    &mut |type_work, constraint_work| {
                        same_checked_interface_fact_with_budget(
                            &left_interface,
                            &right_interface,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                drop(left_interface);
                drop(right_interface);

                let implementation_requirements = || {
                    let mut requirements = Vec::new();
                    requirements
                        .try_reserve(WIDTH)
                        .expect("the wide implementation requirement fixture should fit");
                    for ordinal in 0..WIDTH {
                        requirements.push(CheckedRequirement {
                            id: RequirementId::new(
                                RequirementOwner::Impl(implementation),
                                ordinal as u32,
                            ),
                            interface: InterfaceId::new(module, ordinal as u32 + 1),
                            argument: Type::Variable(parameter),
                            origin: Origin::Source(span),
                            span,
                        });
                    }
                    requirements.into_boxed_slice()
                };
                let prerequisite_implementation = || {
                    let prerequisites = implementation_requirements();
                    let method_requirements = implementation_requirements();
                    CheckedImplementationFact {
                        id: implementation,
                        interface,
                        head_parameters: Box::new([ResolvedTypeVariable {
                            id: parameter,
                            spelling: "A".to_owned(),
                            kind: Kind::Type,
                            origin: Origin::Source(span),
                        }]),
                        argument: head_type(),
                        prerequisites,
                        methods: Box::new([CheckedImplementationMethodFact {
                            id: ImplMethodId::new(implementation, MethodId::new(interface, 0)),
                            method: MethodId::new(interface, 0),
                            binder: BinderId::resolved(module, 1),
                            scheme: ConstrainedScheme {
                                type_parameters: Box::new([(parameter, Kind::Type)]),
                                requirements: method_requirements,
                                value_type: Type::Function(
                                    Box::new(head_type()),
                                    Box::new(function_type()),
                                ),
                            },
                            head_type_parameter_count: 1,
                            origin: Origin::Source(span),
                            span,
                        }]),
                        origin: Origin::Source(span),
                        span,
                    }
                };
                let left_prerequisites = prerequisite_implementation();
                let mut right_prerequisites = prerequisite_implementation();
                assert_exact(
                    "implementation prerequisites",
                    PREREQUISITE_IMPLEMENTATION_WORK,
                    &mut |type_work, constraint_work| {
                        same_checked_implementation_fact_with_budget(
                            &left_prerequisites,
                            &right_prerequisites,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                let replacement_interface = InterfaceId::new(module, u32::MAX);
                right_prerequisites.prerequisites[0].interface = replacement_interface;
                right_prerequisites.methods[0].scheme.requirements[0].interface =
                    replacement_interface;
                assert_prefix(
                    "implementation top prerequisite before method mirror",
                    PREREQUISITE_TOP_MISMATCH_WORK,
                    &mut |type_work, constraint_work| {
                        same_checked_implementation_fact_with_budget(
                            &left_prerequisites,
                            &right_prerequisites,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                let original_interface = InterfaceId::new(module, 1);
                right_prerequisites.prerequisites[0].interface = original_interface;
                right_prerequisites.methods[0].scheme.requirements[0].interface =
                    replacement_interface;
                assert_prefix(
                    "implementation method requirement after top prerequisites",
                    PREREQUISITE_METHOD_MISMATCH_WORK,
                    &mut |type_work, constraint_work| {
                        same_checked_implementation_fact_with_budget(
                            &left_prerequisites,
                            &right_prerequisites,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                drop(left_prerequisites);
                drop(right_prerequisites);

                let method_implementation = || CheckedImplementationFact {
                    id: implementation,
                    interface,
                    head_parameters: Box::new([]),
                    argument: Type::Nominal(nominal),
                    prerequisites: Box::new([]),
                    methods: {
                        let mut prerequisites = Vec::new();
                        prerequisites
                            .try_reserve(WIDTH)
                            .expect("the wide implementation-method fixture should fit");
                        for ordinal in 0..WIDTH {
                            let method = MethodId::new(interface, ordinal as u32);
                            prerequisites.push(CheckedImplementationMethodFact {
                                id: ImplMethodId::new(implementation, method),
                                method,
                                binder: BinderId::resolved(module, ordinal as u32 + 1),
                                scheme: ConstrainedScheme {
                                    type_parameters: Box::new([]),
                                    requirements: Box::new([]),
                                    value_type: Type::Function(
                                        Box::new(Type::Nominal(nominal)),
                                        Box::new(Type::Unit),
                                    ),
                                },
                                head_type_parameter_count: 0,
                                origin: Origin::Source(span),
                                span,
                            });
                        }
                        prerequisites.into_boxed_slice()
                    },
                    origin: Origin::Source(span),
                    span,
                };
                let left_methods = method_implementation();
                let mut right_methods = method_implementation();
                assert_exact(
                    "implementation methods",
                    METHOD_IMPLEMENTATION_WORK,
                    &mut |type_work, constraint_work| {
                        same_checked_implementation_fact_with_budget(
                            &left_methods,
                            &right_methods,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                right_methods.methods[0].id =
                    ImplMethodId::new(implementation, MethodId::new(interface, u32::MAX));
                assert_prefix(
                    "implementation first method identity",
                    IMPLEMENTATION_FIRST_METHOD_MISMATCH_WORK,
                    &mut |type_work, constraint_work| {
                        same_checked_implementation_fact_with_budget(
                            &left_methods,
                            &right_methods,
                            type_work,
                            constraint_work,
                        )
                    },
                );
                drop(left_methods);
                drop(right_methods);
            })
            .expect("the wide carrier worker should spawn")
            .join()
            .expect("all wide comparison carriers must tear down iteratively");
    }
    use crate::interface::RequirementOwner;
    use crate::module::ModuleId;
    use crate::source::{ByteRange, GeneratedReason, SourceFile};

    fn application_type(depth: usize) -> Type {
        let mut ty = Type::Unit;
        for _ in 0..depth {
            ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
        }
        ty
    }

    fn generated_origin(source: &SourceFile, depth: usize) -> Origin {
        let span = source
            .span(ByteRange::new(0, 1).expect("the origin range should be ordered"))
            .expect("the origin range should belong to the fixture");
        let mut origin = Origin::Source(span);
        for _ in 0..depth {
            origin = Origin::Generated {
                cause: Box::new(origin),
                reason: GeneratedReason::TypeChecking,
            };
        }
        origin
    }

    #[test]
    fn duplicate_imported_global_is_dismantled_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("duplicate-imported-global".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("duplicate-global.ash", "x")
                    .expect("the imported-global fixture should fit");
                let binder = BinderId::resolved(ModuleId::new(90), 0);
                let mut imported = ImportedFacts::default();
                imported
                    .insert_global(
                        ImportedGlobalScheme {
                            binder,
                            scheme: ConstrainedScheme::from_rank1_type(application_type(DEPTH)),
                            origin: generated_origin(&source, DEPTH),
                        },
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
                imported
                    .insert_global(
                        ImportedGlobalScheme {
                            binder,
                            scheme: ConstrainedScheme::from_rank1_type(Type::Unit),
                            origin: generated_origin(&source, 0),
                        },
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
                assert_eq!(
                    imported
                        .global(binder)
                        .expect("the replacement global should remain")
                        .scheme
                        .value_type(),
                    &Type::Unit,
                );
            })
            .expect("the duplicate-global thread should start")
            .join()
            .expect("the displaced imported global must be dismantled iteratively");
    }

    #[test]
    fn imported_global_order_failure_dismantles_deep_input_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("rejected-imported-global-order".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("rejected-global.ash", "x")
                    .expect("the rejected-global fixture should fit");
                let binder = BinderId::resolved(ModuleId::new(91), 0);
                let mut imported = ImportedFacts::default();
                let mut budget = TypeWorkBudget::with_limit(0);
                assert_eq!(
                    imported.insert_global(
                        ImportedGlobalScheme {
                            binder,
                            scheme: ConstrainedScheme::from_rank1_type(application_type(DEPTH)),
                            origin: generated_origin(&source, DEPTH),
                        },
                        &mut budget,
                    ),
                    Err(())
                );
                assert!(imported.global(binder).is_none());
                assert_eq!(budget.used(), 0);
            })
            .expect("the rejected-global thread should start")
            .join()
            .expect("pre-insert failure must dismantle deep Type and Origin within 256 KiB");
    }

    #[test]
    fn duplicate_imported_constructor_is_dismantled_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("duplicate-imported-constructor".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("duplicate-constructor.ash", "x")
                    .expect("the imported-constructor fixture should fit");
                let constructor = ConstructorId::new(NominalTypeId::new(ModuleId::new(91), 0), 0);
                let mut imported = ImportedFacts::default();
                let mut budget = TypeWorkBudget::default();
                imported
                    .insert_constructor(
                        ImportedConstructorFact {
                            id: constructor,
                            spelling: "Deep".to_owned(),
                            payload: Some(application_type(DEPTH)),
                            scheme: ConstrainedScheme::from_rank1_type(Type::Function(
                                Box::new(application_type(DEPTH)),
                                Box::new(Type::Nominal(constructor.owner())),
                            )),
                            origin: generated_origin(&source, DEPTH),
                        },
                        &mut budget,
                    )
                    .expect("the first constructor should fit");
                imported
                    .insert_constructor(
                        ImportedConstructorFact {
                            id: constructor,
                            spelling: "Shallow".to_owned(),
                            payload: None,
                            scheme: ConstrainedScheme::from_rank1_type(Type::Nominal(
                                constructor.owner(),
                            )),
                            origin: generated_origin(&source, 0),
                        },
                        &mut budget,
                    )
                    .expect("a replacement needs no new map slot");
                let retained = imported
                    .constructors
                    .get(&constructor)
                    .expect("the replacement constructor should remain");
                assert_eq!(retained.spelling, "Shallow");
                assert!(retained.payload.is_none());
            })
            .expect("the duplicate-constructor thread should start")
            .join()
            .expect("the displaced imported constructor must be dismantled iteratively");
    }

    #[test]
    fn replaced_ordered_export_candidate_is_dismantled_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("replace-ordered-export".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("replace-ordered.ash", "x")
                    .expect("the ordered-export fixture should fit");
                let mut exports = ResolvedExportCandidate::default();
                let mut budget = TypeWorkBudget::default();
                exports
                    .try_insert_term(
                        "value".to_owned(),
                        CandidateGlobal {
                            binder: BinderId::resolved(ModuleId::new(92), 0),
                            source: CandidateFactSource::Imported,
                            origin: generated_origin(&source, DEPTH),
                        },
                        &mut budget,
                    )
                    .expect("the first export should fit");
                exports
                    .try_insert_term(
                        "value".to_owned(),
                        CandidateGlobal {
                            binder: BinderId::resolved(ModuleId::new(92), 1),
                            source: CandidateFactSource::Local,
                            origin: generated_origin(&source, 0),
                        },
                        &mut budget,
                    )
                    .expect("replacement should retain the existing order slot");
                assert_eq!(
                    exports.term("value").map(|candidate| candidate.binder),
                    Some(BinderId::resolved(ModuleId::new(92), 1)),
                );
            })
            .expect("the ordered-export replacement thread should start")
            .join()
            .expect("the displaced ordered export must be dismantled iteratively");
    }

    #[test]
    fn replaced_hidden_nominal_is_dismantled_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("replace-hidden-nominal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("replace-hidden.ash", "x")
                    .expect("the hidden-nominal fixture should fit");
                let id = NominalTypeId::new(ModuleId::new(93), 0);
                let mut exports = ResolvedExportCandidate::default();
                let mut budget = TypeWorkBudget::default();
                exports
                    .try_insert_hidden_nominal(
                        CandidateHiddenNominal {
                            id,
                            parameter_count: 0,
                            spelling: "Deep".to_owned(),
                            origin: generated_origin(&source, DEPTH),
                        },
                        &mut budget,
                    )
                    .expect("the first hidden nominal should fit");
                exports
                    .try_insert_hidden_nominal(
                        CandidateHiddenNominal {
                            id,
                            parameter_count: 1,
                            spelling: "Shallow".to_owned(),
                            origin: generated_origin(&source, 0),
                        },
                        &mut budget,
                    )
                    .expect("the hidden nominal should replace in place");
                assert_eq!(
                    exports
                        .hidden_nominal(id)
                        .map(|candidate| candidate.spelling.as_str()),
                    Some("Shallow"),
                );
            })
            .expect("the hidden-nominal replacement thread should start")
            .join()
            .expect("the displaced hidden nominal must be dismantled iteratively");
    }

    #[test]
    fn replaced_withheld_export_is_dismantled_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("replace-withheld-export".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("replace-withheld.ash", "x")
                    .expect("the withheld-export fixture should fit");
                let mut exports = ResolvedExportCandidate::default();
                let mut budget = TypeWorkBudget::default();
                exports
                    .try_insert_withheld(
                        WithheldNamespace::Term,
                        "hidden".to_owned(),
                        WithheldExport {
                            kind: WithheldExportKind::Private,
                            owner: None,
                            origin: Some(generated_origin(&source, DEPTH)),
                        },
                        &mut budget,
                    )
                    .expect("the first withheld export should fit");
                exports
                    .try_insert_withheld(
                        WithheldNamespace::Term,
                        "hidden".to_owned(),
                        WithheldExport {
                            kind: WithheldExportKind::Private,
                            owner: None,
                            origin: Some(generated_origin(&source, 0)),
                        },
                        &mut budget,
                    )
                    .expect("the withheld export should replace in place");
                assert!(exports.is_private("hidden"));
            })
            .expect("the withheld-export replacement thread should start")
            .join()
            .expect("the displaced withheld export must be dismantled iteratively");
    }

    #[test]
    fn resolved_application_rendering_parenthesizes_non_atomic_heads() {
        let source = SourceFile::new("resolved-application-display.ash", "A")
            .expect("the display fixture should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the display range should be ordered"))
            .expect("the display range should belong to the fixture");
        let parameter = TypeVariableId::new(0);
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_additional_type_variables([ResolvedTypeVariable {
                id: parameter,
                spelling: "A".into(),
                kind: crate::types::Kind::Type,
                origin: Origin::Source(span),
            }]);

        let function_head = Type::Application(
            Box::new(Type::Function(Box::new(Type::Int), Box::new(Type::Bool))),
            Box::new(Type::Unit),
        );
        assert_eq!(registry.display_type(&function_head), "(Int -> Bool)<Unit>");

        let quantified_head = Type::Application(
            Box::new(Type::Forall(
                vec![(parameter, crate::types::Kind::Type)].into_boxed_slice(),
                Box::new(Type::Variable(parameter)),
            )),
            Box::new(Type::Unit),
        );
        assert_eq!(
            registry.display_type(&quantified_head),
            "(forall A : Type. A)<Unit>"
        );
    }

    #[test]
    fn copied_fixed_kind_binder_storage_is_exact_and_atomic() {
        // One retained record plus the Arrow and its two Type leaves costs four units.
        const EXACT_WORK: usize = 4;
        let source = SourceFile::new("fixed-kind-copy.ash", "F")
            .expect("the fixed-kind copy fixture should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the binder range should be ordered"))
            .expect("the binder range should belong to the fixture");
        let owner = NominalTypeId::new(ModuleId::new(0), 0);
        let id = TypeVariableId::resolved(ModuleId::new(0), 0);
        let parameter = || ResolvedTypeVariable {
            id,
            spelling: "F".to_owned(),
            kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            origin: Origin::Source(span),
        };

        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert!(
            ResolvedRegistry::new(Vec::new(), Vec::new())
                .with_type_parameters_with_budget(vec![(owner, vec![parameter()])], &mut short,)
                .is_err(),
            "one missing kind-node unit must publish no registry",
        );
        assert_eq!(short.used(), EXACT_WORK - 1);

        let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_type_parameters_with_budget(vec![(owner, vec![parameter()])], &mut exact)
            .expect("the exact record-and-kind budget should publish the registry");
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(
            registry.type_variable(id).map(|binder| &binder.kind),
            Some(&parameter().kind)
        );
    }

    #[test]
    fn fixed_kind_binder_comparison_is_exact_and_stack_safe() {
        const DEPTH: usize = 32_768;
        const KIND_NODES: usize = 2 * DEPTH + 1;
        const EXACT_WORK: usize = 1 + KIND_NODES;

        std::thread::Builder::new()
            .name("deep-fixed-kind-binder-comparison".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-kind-comparison.ash", "F")
                    .expect("the comparison fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the binder range should be ordered"))
                    .expect("the binder range should belong to the fixture");
                let id = TypeVariableId::resolved(ModuleId::new(0), 0);
                let deep_kind = || {
                    let mut kind = Kind::Type;
                    for _ in 0..DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    kind
                };
                let left = [ResolvedTypeVariable {
                    id,
                    spelling: "F".to_owned(),
                    kind: deep_kind(),
                    origin: Origin::Source(span),
                }];
                let right = [ResolvedTypeVariable {
                    id,
                    spelling: "F".to_owned(),
                    kind: deep_kind(),
                    origin: Origin::Source(span),
                }];

                let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
                assert_eq!(
                    same_resolved_type_variables_with_budget(&left, &right, &mut short),
                    Err(()),
                );
                assert_eq!(short.used(), EXACT_WORK - 1);

                let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
                assert_eq!(
                    same_resolved_type_variables_with_budget(&left, &right, &mut exact),
                    Ok(true),
                );
                assert_eq!(exact.used(), EXACT_WORK);

                let mismatched = [ResolvedTypeVariable {
                    id,
                    spelling: "F".to_owned(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                }];
                let mut mismatch_exact = TypeWorkBudget::with_limit(2);
                assert_eq!(
                    same_resolved_type_variables_with_budget(
                        &left,
                        &mismatched,
                        &mut mismatch_exact,
                    ),
                    Ok(false),
                );
                assert_eq!(mismatch_exact.used(), 2);
            })
            .expect("the comparison thread should start")
            .join()
            .expect("deep fixed-kind comparison and teardown must remain stack-safe");
    }

    #[test]
    fn borrowed_nominal_merge_is_exact_constraint_only_on_duplicate_and_atomic() {
        // The absent path retains one nominal-map fact, one deterministic
        // order index, one binder record, and all three nodes in `Type -> Type`.
        const INSERT_TYPE_WORK: usize = 2 + 1 + 3;
        // The duplicate path validates one family header, then compares the
        // binder record, its Source Origin, all three Kind nodes, and the
        // nominal Source Origin. It retains nothing.
        const DUPLICATE_CONSTRAINT_WORK: usize = 1 + (1 + 1 + 3) + 1;
        let source = SourceFile::new("imported-nominal-kind.ash", "F")
            .expect("the imported nominal fixture should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the binder range should be ordered"))
            .expect("the binder range should belong to the fixture");
        let nominal = NominalTypeId::new(ModuleId::new(0), 0);
        let parameter = TypeVariableId::resolved(ModuleId::new(0), 0);
        let arrow = || Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let parameters = [ResolvedTypeVariable {
            id: parameter,
            spelling: "F".to_owned(),
            kind: arrow(),
            origin: Origin::Source(span),
        }];
        let candidate = || ImportedNominalFactRef {
            id: nominal,
            parameter_count: 1,
            constructor_count: 1,
            parameters: &parameters,
            constructors: &[],
            access: ImportedTypeAccess::Hidden,
            display_spelling: Some("Holder"),
            display_is_private: false,
            origin: &parameters[0].origin,
        };

        let mut imported = ImportedFacts::default();
        let mut insert_short_types = TypeWorkBudget::with_limit(INSERT_TYPE_WORK - 1);
        let mut insert_constraints = crate::interface::InterfaceConstraintBudget::with_limit(1);
        assert!(matches!(
            imported.prepare_nominal_merge(
                candidate(),
                &mut insert_short_types,
                &mut insert_constraints,
            ),
            Err(ImportedNominalMergeFailure::TypeResource),
        ));
        assert_eq!(
            insert_short_types.used(),
            0,
            "the aggregate retention charge is atomic"
        );
        assert!(imported.nominals().next().is_none());

        let mut insert_types = TypeWorkBudget::with_limit(INSERT_TYPE_WORK);
        let mut insert_constraints = crate::interface::InterfaceConstraintBudget::with_limit(1);
        let prepared = imported
            .prepare_nominal_merge(candidate(), &mut insert_types, &mut insert_constraints)
            .expect("the exact absent candidate should stage");
        imported
            .commit_nominal_merge(prepared)
            .expect("the staged absent candidate should publish");
        assert_eq!(insert_types.used(), INSERT_TYPE_WORK);
        assert_eq!(insert_constraints.used(), 1);

        let mut duplicate_short_types = TypeWorkBudget::with_limit(0);
        let mut duplicate_short_constraints =
            crate::interface::InterfaceConstraintBudget::with_limit(DUPLICATE_CONSTRAINT_WORK - 1);
        assert!(matches!(
            imported.prepare_nominal_merge(
                candidate(),
                &mut duplicate_short_types,
                &mut duplicate_short_constraints,
            ),
            Err(ImportedNominalMergeFailure::ConstraintResource),
        ));
        assert_eq!(duplicate_short_types.used(), 0);
        assert_eq!(
            duplicate_short_constraints.used(),
            DUPLICATE_CONSTRAINT_WORK - 1
        );
        assert_eq!(
            imported
                .nominals()
                .next()
                .map(|retained| &retained.parameters[0].kind),
            Some(&arrow()),
            "failed authentication must not mutate the retained route",
        );

        let mut duplicate_types = TypeWorkBudget::with_limit(0);
        let mut duplicate_constraints =
            crate::interface::InterfaceConstraintBudget::with_limit(DUPLICATE_CONSTRAINT_WORK);
        let prepared = imported
            .prepare_nominal_merge(
                candidate(),
                &mut duplicate_types,
                &mut duplicate_constraints,
            )
            .expect("the exact duplicate should compare without retention");
        imported
            .commit_nominal_merge(prepared)
            .expect("the exact duplicate should commit as a no-op");
        assert_eq!(duplicate_types.used(), 0);
        assert_eq!(duplicate_constraints.used(), DUPLICATE_CONSTRAINT_WORK);
    }

    #[test]
    fn borrowed_nominal_merge_promotes_only_after_exact_family_and_metadata_validation() {
        // One family header plus two owner/ordinal cells, then one binder
        // record, its Source Origin, the three-node Kind, and the defining
        // Source Origin.
        const PROMOTION_CONSTRAINT_WORK: usize = (1 + 2) + (1 + 1 + 3) + 1;
        const PROMOTION_TYPE_WORK: usize = 2;
        let source = SourceFile::new("nominal-promotion.ash", "F")
            .expect("the promotion fixture should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the parameter range should be ordered"))
            .expect("the parameter span should fit");
        let module = ModuleId::new(9_990);
        let nominal = NominalTypeId::new(module, 0);
        let parameter = [ResolvedTypeVariable {
            id: TypeVariableId::resolved(module, 0),
            spelling: "F".to_owned(),
            kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            origin: Origin::Source(span),
        }];
        let family = [
            ConstructorId::new(nominal, 0),
            ConstructorId::new(nominal, 1),
        ];
        let hidden = ImportedNominalFactRef {
            id: nominal,
            parameter_count: 1,
            constructor_count: 2,
            parameters: &parameter,
            constructors: &[],
            access: ImportedTypeAccess::Hidden,
            display_spelling: None,
            display_is_private: false,
            origin: &parameter[0].origin,
        };
        let transparent = ImportedNominalFactRef {
            constructors: &family,
            access: ImportedTypeAccess::Transparent,
            display_spelling: Some("Visible"),
            ..hidden
        };
        let mut imported = ImportedFacts::default();
        let mut initial_types = TypeWorkBudget::with_limit(2 + 1 + 3);
        let mut initial_constraints = crate::interface::InterfaceConstraintBudget::with_limit(1);
        let prepared = imported
            .prepare_nominal_merge(hidden, &mut initial_types, &mut initial_constraints)
            .expect("the hidden baseline should stage");
        imported
            .commit_nominal_merge(prepared)
            .expect("the hidden baseline should publish");

        let baseline = |imported: &ImportedFacts| {
            let fact = imported
                .nominal(nominal)
                .expect("the owner should remain retained");
            (
                fact.access,
                fact.constructors.to_vec(),
                fact.display_spelling.clone(),
            )
        };
        let hidden_snapshot = baseline(&imported);

        let mut constraint_short_types = TypeWorkBudget::with_limit(0);
        let mut constraint_short =
            crate::interface::InterfaceConstraintBudget::with_limit(PROMOTION_CONSTRAINT_WORK - 1);
        assert!(matches!(
            imported.prepare_nominal_merge(
                transparent,
                &mut constraint_short_types,
                &mut constraint_short,
            ),
            Err(ImportedNominalMergeFailure::ConstraintResource),
        ));
        assert_eq!(constraint_short_types.used(), 0);
        assert_eq!(baseline(&imported), hidden_snapshot);

        let mut type_short = TypeWorkBudget::with_limit(PROMOTION_TYPE_WORK - 1);
        let mut exact_constraints =
            crate::interface::InterfaceConstraintBudget::with_limit(PROMOTION_CONSTRAINT_WORK);
        assert!(matches!(
            imported.prepare_nominal_merge(transparent, &mut type_short, &mut exact_constraints,),
            Err(ImportedNominalMergeFailure::TypeResource),
        ));
        assert_eq!(type_short.used(), 0, "the family-copy charge is atomic");
        assert_eq!(baseline(&imported), hidden_snapshot);

        let mut exact_types = TypeWorkBudget::with_limit(PROMOTION_TYPE_WORK);
        let mut exact_constraints =
            crate::interface::InterfaceConstraintBudget::with_limit(PROMOTION_CONSTRAINT_WORK);
        let prepared = imported
            .prepare_nominal_merge(transparent, &mut exact_types, &mut exact_constraints)
            .expect("the exact promotion should stage");
        assert_eq!(
            baseline(&imported),
            hidden_snapshot,
            "staging must not publish"
        );
        imported
            .commit_nominal_merge(prepared)
            .expect("the exact promotion should publish");
        assert_eq!(exact_types.used(), PROMOTION_TYPE_WORK);
        assert_eq!(exact_constraints.used(), PROMOTION_CONSTRAINT_WORK);
        assert_eq!(
            baseline(&imported),
            (
                ImportedTypeAccess::Transparent,
                family.to_vec(),
                Some("Visible".to_owned()),
            ),
        );

        let alias = ImportedNominalFactRef {
            display_spelling: Some("Alias"),
            ..transparent
        };
        let mut alias_types = TypeWorkBudget::with_limit(0);
        let mut alias_constraints =
            crate::interface::InterfaceConstraintBudget::with_limit(PROMOTION_CONSTRAINT_WORK);
        let prepared = imported
            .prepare_nominal_merge(alias, &mut alias_types, &mut alias_constraints)
            .expect("public aliases may disagree without changing the defining fact");
        imported
            .commit_nominal_merge(prepared)
            .expect("the public alias should commit as a no-op");
        assert_eq!(alias_types.used(), 0);
        assert_eq!(baseline(&imported).2.as_deref(), Some("Visible"));
    }

    #[test]
    fn borrowed_nominal_merge_covers_access_display_and_metadata_conflict_matrix() {
        let source = SourceFile::new("nominal-merge-matrix.ash", "F other")
            .expect("the nominal merge source should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the primary range should be ordered"))
            .expect("the primary span should fit");
        let other_span = source
            .span(ByteRange::new(2, 7).expect("the alternate range should be ordered"))
            .expect("the alternate span should fit");
        let module = ModuleId::new(9_991);
        let nominal = NominalTypeId::new(module, 0);
        let family = [
            ConstructorId::new(nominal, 0),
            ConstructorId::new(nominal, 1),
        ];
        let empty_parameters: [ResolvedTypeVariable; 0] = [];
        let hidden = ImportedNominalFactRef {
            id: nominal,
            parameter_count: 0,
            constructor_count: family.len(),
            parameters: &empty_parameters,
            constructors: &[],
            access: ImportedTypeAccess::Hidden,
            display_spelling: None,
            display_is_private: false,
            origin: &Origin::Source(span),
        };
        let commit = |imported: &mut ImportedFacts,
                      candidate: ImportedNominalFactRef<'_>,
                      type_limit: usize,
                      constraint_limit: usize| {
            let mut type_work = TypeWorkBudget::with_limit(type_limit);
            let mut constraint_work =
                crate::interface::InterfaceConstraintBudget::with_limit(constraint_limit);
            let prepared = imported
                .prepare_nominal_merge(candidate, &mut type_work, &mut constraint_work)
                .expect("the exact nominal transition should stage");
            imported
                .commit_nominal_merge(prepared)
                .expect("the staged nominal transition should publish");
            assert_eq!(type_work.used(), type_limit);
            assert_eq!(constraint_work.used(), constraint_limit);
        };

        let mut imported = ImportedFacts::default();
        commit(&mut imported, hidden, 2, 1);
        let opaque = ImportedNominalFactRef {
            access: ImportedTypeAccess::Opaque,
            display_spelling: Some("Opaque"),
            ..hidden
        };
        commit(&mut imported, opaque, 0, 2);
        let retained = imported
            .nominal(nominal)
            .expect("the opaque route should merge");
        assert_eq!(retained.access, ImportedTypeAccess::Opaque);
        assert_eq!(retained.display_spelling.as_deref(), Some("Opaque"));
        assert!(retained.constructors.is_empty());

        let lower_alias = ImportedNominalFactRef {
            display_spelling: Some("Alias"),
            ..hidden
        };
        commit(&mut imported, lower_alias, 0, 2);
        let retained = imported
            .nominal(nominal)
            .expect("the lower route should remain");
        assert_eq!(retained.access, ImportedTypeAccess::Opaque);
        assert_eq!(retained.display_spelling.as_deref(), Some("Opaque"));

        let transparent = ImportedNominalFactRef {
            constructors: &family,
            access: ImportedTypeAccess::Transparent,
            display_spelling: Some("Visible"),
            ..hidden
        };
        commit(&mut imported, transparent, family.len(), 4);
        let retained = imported
            .nominal(nominal)
            .expect("the transparent route should promote");
        assert_eq!(retained.access, ImportedTypeAccess::Transparent);
        assert_eq!(retained.constructors.as_ref(), family);
        assert_eq!(retained.display_spelling.as_deref(), Some("Visible"));

        commit(&mut imported, opaque, 0, 2);
        let retained = imported
            .nominal(nominal)
            .expect("a later opaque route should be a no-op");
        assert_eq!(retained.access, ImportedTypeAccess::Transparent);
        assert_eq!(retained.constructors.as_ref(), family);
        assert_eq!(retained.display_spelling.as_deref(), Some("Visible"));

        let fill_nominal = NominalTypeId::new(module, 1);
        let fill_hidden = ImportedNominalFactRef {
            id: fill_nominal,
            ..hidden
        };
        let mut display_fill = ImportedFacts::default();
        commit(&mut display_fill, fill_hidden, 2, 1);
        commit(
            &mut display_fill,
            ImportedNominalFactRef {
                display_spelling: Some("Filled"),
                ..fill_hidden
            },
            0,
            2,
        );
        assert_eq!(
            display_fill
                .nominal(fill_nominal)
                .and_then(|fact| fact.display_spelling.as_deref()),
            Some("Filled"),
        );
        commit(
            &mut display_fill,
            ImportedNominalFactRef {
                display_spelling: Some("PublicAlias"),
                ..fill_hidden
            },
            0,
            2,
        );
        assert_eq!(
            display_fill
                .nominal(fill_nominal)
                .and_then(|fact| fact.display_spelling.as_deref()),
            Some("Filled"),
        );

        let private_nominal = NominalTypeId::new(module, 2);
        let private = ImportedNominalFactRef {
            id: private_nominal,
            display_spelling: Some("Secret"),
            display_is_private: true,
            ..hidden
        };
        let mut private_import = ImportedFacts::default();
        commit(&mut private_import, private, 2, 1);
        let private_alias = ImportedNominalFactRef {
            display_spelling: Some("Forged"),
            ..private
        };
        let mut private_short = crate::interface::InterfaceConstraintBudget::with_limit(1);
        assert!(matches!(
            private_import.validate_nominal_merge(private_alias, &mut private_short),
            Err(ImportedNominalMergeFailure::ConstraintResource),
        ));
        let mut private_exact = crate::interface::InterfaceConstraintBudget::with_limit(2);
        assert!(matches!(
            private_import.validate_nominal_merge(private_alias, &mut private_exact),
            Err(ImportedNominalMergeFailure::Conflict),
        ));
        assert_eq!(
            private_import
                .nominal(private_nominal)
                .and_then(|fact| fact.display_spelling.as_deref()),
            Some("Secret"),
        );

        let parameter_nominal = NominalTypeId::new(module, 3);
        let parameter_id = TypeVariableId::resolved(module, 0);
        let parameter_origin = Origin::Source(span);
        let parameter = [ResolvedTypeVariable {
            id: parameter_id,
            spelling: "F".to_owned(),
            kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            origin: parameter_origin.clone(),
        }];
        let parameterized = ImportedNominalFactRef {
            id: parameter_nominal,
            parameter_count: 1,
            constructor_count: 1,
            parameters: &parameter,
            constructors: &[],
            access: ImportedTypeAccess::Hidden,
            display_spelling: Some("Parameterized"),
            display_is_private: false,
            origin: &parameter_origin,
        };
        let mut parameter_import = ImportedFacts::default();
        commit(&mut parameter_import, parameterized, 6, 1);

        let assert_parameter_conflict =
            |candidate: ImportedNominalFactRef<'_>, exact_work: usize| {
                let mut short = crate::interface::InterfaceConstraintBudget::with_limit(
                    exact_work.saturating_sub(1),
                );
                assert!(matches!(
                    parameter_import.validate_nominal_merge(candidate, &mut short),
                    Err(ImportedNominalMergeFailure::ConstraintResource),
                ));
                let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(exact_work);
                assert!(matches!(
                    parameter_import.validate_nominal_merge(candidate, &mut exact),
                    Err(ImportedNominalMergeFailure::Conflict),
                ));
                assert_eq!(exact.used(), exact_work);
            };
        let wrong_id = [ResolvedTypeVariable {
            id: TypeVariableId::resolved(module, 1),
            spelling: "F".to_owned(),
            kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            origin: parameter_origin.clone(),
        }];
        assert_parameter_conflict(
            ImportedNominalFactRef {
                parameters: &wrong_id,
                ..parameterized
            },
            2,
        );
        let wrong_spelling = [ResolvedTypeVariable {
            spelling: "G".to_owned(),
            ..parameter[0].clone()
        }];
        assert_parameter_conflict(
            ImportedNominalFactRef {
                parameters: &wrong_spelling,
                ..parameterized
            },
            2,
        );
        let wrong_parameter_origin = [ResolvedTypeVariable {
            origin: Origin::Source(other_span),
            ..parameter[0].clone()
        }];
        assert_parameter_conflict(
            ImportedNominalFactRef {
                parameters: &wrong_parameter_origin,
                ..parameterized
            },
            3,
        );
        let wrong_kind = [ResolvedTypeVariable {
            kind: Kind::Type,
            ..parameter[0].clone()
        }];
        assert_parameter_conflict(
            ImportedNominalFactRef {
                parameters: &wrong_kind,
                ..parameterized
            },
            4,
        );
        assert_parameter_conflict(
            ImportedNominalFactRef {
                origin: &Origin::Source(other_span),
                ..parameterized
            },
            7,
        );

        for corrupt_family in [
            [
                ConstructorId::new(NominalTypeId::new(module, 99), 0),
                ConstructorId::new(nominal, 1),
            ],
            [
                ConstructorId::new(nominal, 1),
                ConstructorId::new(nominal, 0),
            ],
        ] {
            let candidate = ImportedNominalFactRef {
                constructors: &corrupt_family,
                ..transparent
            };
            let mut short = crate::interface::InterfaceConstraintBudget::with_limit(2);
            assert!(matches!(
                imported.validate_nominal_merge(candidate, &mut short),
                Err(ImportedNominalMergeFailure::ConstraintResource),
            ));
            assert_eq!(short.used(), 0, "the family-shape charge is atomic");
            let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(3);
            assert!(matches!(
                imported.validate_nominal_merge(candidate, &mut exact),
                Err(ImportedNominalMergeFailure::Conflict),
            ));
            assert_eq!(exact.used(), 3);
        }
    }

    #[test]
    fn abandoned_deep_borrowed_nominal_plan_drops_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        const RETENTION_TYPE_WORK: usize = 2 * DEPTH + 4;

        std::thread::Builder::new()
            .name("abandoned-deep-nominal-plan".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-nominal-plan.ash", "F")
                    .expect("the deep nominal-plan source should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the parameter range should be ordered"))
                    .expect("the parameter span should fit");
                let module = ModuleId::new(9_992);
                let nominal = NominalTypeId::new(module, 0);
                let mut kind = Kind::Type;
                for _ in 0..DEPTH {
                    kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                }
                let parameter = [ResolvedTypeVariable {
                    id: TypeVariableId::resolved(module, 0),
                    spelling: "F".to_owned(),
                    kind,
                    origin: Origin::Source(span),
                }];
                let candidate = ImportedNominalFactRef {
                    id: nominal,
                    parameter_count: 1,
                    constructor_count: 1,
                    parameters: &parameter,
                    constructors: &[],
                    access: ImportedTypeAccess::Hidden,
                    display_spelling: Some("Deep"),
                    display_is_private: false,
                    origin: &parameter[0].origin,
                };

                let mut imported = ImportedFacts::default();
                let mut short_types = TypeWorkBudget::with_limit(RETENTION_TYPE_WORK - 1);
                let mut short_constraints =
                    crate::interface::InterfaceConstraintBudget::with_limit(1);
                assert!(matches!(
                    imported.prepare_nominal_merge(
                        candidate,
                        &mut short_types,
                        &mut short_constraints,
                    ),
                    Err(ImportedNominalMergeFailure::TypeResource),
                ));
                assert_eq!(short_types.used(), 0);
                assert!(imported.nominals().next().is_none());

                for _ in 0..2 {
                    let mut exact_types = TypeWorkBudget::with_limit(RETENTION_TYPE_WORK);
                    let mut exact_constraints =
                        crate::interface::InterfaceConstraintBudget::with_limit(1);
                    let prepared = imported
                        .prepare_nominal_merge(candidate, &mut exact_types, &mut exact_constraints)
                        .expect("the exact deep borrowed plan should stage");
                    assert_eq!(exact_types.used(), RETENTION_TYPE_WORK);
                    assert!(imported.nominals().next().is_none());
                    drop(prepared);
                    assert!(imported.nominals().next().is_none());
                }
            })
            .expect("the deep nominal-plan worker should spawn")
            .join()
            .expect("abandoned deep Kind plans must dismantle iteratively");
    }

    #[test]
    fn checker_view_retains_abstract_kind_without_structural_visibility() {
        // One family mirror, one private sidecar record, plus the five nodes of
        // `(Type -> Type) -> Type` are the complete retention boundary.
        const EXACT_WORK: usize = 1 + 1 + 5;
        let source = SourceFile::new("abstract-kind-view.ash", "F")
            .expect("the abstract Kind fixture should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the binder range should be ordered"))
            .expect("the binder range should belong to the fixture");
        let module = ModuleId::new(810);
        let nominal = NominalTypeId::new(module, 0);
        let parameter = TypeVariableId::resolved(module, 0);
        let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let mut imported = ImportedFacts::default();
        imported
            .merge_nominal(
                ImportedNominalFact {
                    id: nominal,
                    parameter_count: 1,
                    constructor_count: 1,
                    parameters: Box::new([ResolvedTypeVariable {
                        id: parameter,
                        spelling: "F".to_owned(),
                        kind: function_kind.clone(),
                        origin: Origin::Source(span),
                    }]),
                    constructors: Box::new([]),
                    access: ImportedTypeAccess::Opaque,
                    display_spelling: Some("Abstract".to_owned()),
                    display_is_private: false,
                    origin: Origin::Source(span),
                },
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("the abstract nominal fixture should be unique");

        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert!(matches!(
            ResolvedRegistry::default().checker_view(&imported, &mut short),
            Err(ResolvedBuildFailure::TypeResource),
        ));
        assert_eq!(short.used(), EXACT_WORK - 1);
        assert_eq!(
            imported
                .nominal(nominal)
                .map(|fact| (&fact.parameters[0].kind, fact.access)),
            Some((&function_kind, ImportedTypeAccess::Opaque)),
            "failed sidecar construction must not mutate the source fact",
        );

        let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
        let view = ResolvedRegistry::default()
            .checker_view(&imported, &mut exact)
            .expect("one record plus every derived Kind node should fit exactly");
        assert_eq!(exact.used(), EXACT_WORK);
        let CanonicalNominalKind::Frozen { kind, origin } = view
            .nominal_kind(nominal)
            .expect("the checker view should expose one abstract Kind fact")
        else {
            panic!("the abstract nominal must not masquerade as a structural declaration");
        };
        assert_eq!(
            kind,
            &Kind::Arrow(Box::new(function_kind), Box::new(Kind::Type)),
        );
        assert_eq!(origin, span);
        assert!(view.nominal(nominal).is_none());
        assert!(view.nominal_parameters(nominal).is_none());
        assert!(view.canonical_nominal_parameters(nominal).is_none());
        assert!(view.constructor(ConstructorId::new(nominal, 0)).is_none());
        assert!(view.constructors().is_empty());
    }

    #[test]
    fn checker_view_abstract_kind_failure_and_drop_are_stack_safe() {
        const DEPTH: usize = 32_768;
        // The parameter has 2D+1 nodes. The nominal Kind retains that domain,
        // one Arrow, and one Type result, beside one family mirror and one
        // sidecar record.
        const DERIVED_KIND_NODES: usize = 2 * DEPTH + 3;
        const EXACT_WORK: usize = 1 + 1 + DERIVED_KIND_NODES;

        std::thread::Builder::new()
            .name("abstract-kind-sidecar".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-abstract-kind.ash", "F")
                    .expect("the deep abstract fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the binder range should be ordered"))
                    .expect("the binder range should belong to the fixture");
                let module = ModuleId::new(811);
                let nominal = NominalTypeId::new(module, 0);
                let mut parameter_kind = Kind::Type;
                for _ in 0..DEPTH {
                    parameter_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(parameter_kind));
                }
                let mut imported = ImportedFacts::default();
                imported
                    .merge_nominal(
                        ImportedNominalFact {
                            id: nominal,
                            parameter_count: 1,
                            constructor_count: 1,
                            parameters: Box::new([ResolvedTypeVariable {
                                id: TypeVariableId::resolved(module, 0),
                                spelling: "F".to_owned(),
                                kind: parameter_kind,
                                origin: Origin::Source(span),
                            }]),
                            constructors: Box::new([]),
                            access: ImportedTypeAccess::Hidden,
                            display_spelling: None,
                            display_is_private: true,
                            origin: Origin::Source(span),
                        },
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .expect("the deep abstract nominal should be unique");

                let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
                assert!(matches!(
                    ResolvedRegistry::default().checker_view(&imported, &mut short),
                    Err(ResolvedBuildFailure::TypeResource),
                ));
                assert_eq!(short.used(), EXACT_WORK - 1);

                let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
                let view = ResolvedRegistry::default()
                    .checker_view(&imported, &mut exact)
                    .expect("the exact deep sidecar should fit");
                assert_eq!(exact.used(), EXACT_WORK);
                let CanonicalNominalKind::Frozen { kind, .. } = view
                    .nominal_kind(nominal)
                    .expect("the deep abstract Kind should remain available")
                else {
                    panic!("the deep abstract nominal must use the frozen sidecar");
                };
                let mut node_budget = TypeWorkBudget::with_limit(DERIVED_KIND_NODES);
                crate::types::charge_kind_nodes(kind, &mut node_budget)
                    .expect("the retained Kind must have the published node count");
                assert_eq!(node_budget.used(), DERIVED_KIND_NODES);
            })
            .expect("the deep sidecar thread should start")
            .join()
            .expect("deep sidecar failure, success, and teardown must be stack-safe");
    }

    #[test]
    fn checker_view_interface_binder_has_an_exact_atomic_budget_and_preserves_source() {
        // One retained binder record and the three nodes of Type -> Type.
        const EXACT_WORK: usize = 1 + 3;

        let source = SourceFile::new("checker-interface-binder.ash", "Interface")
            .expect("the checker binder fixture should fit");
        let span = source
            .span(ByteRange::new(0, 9).expect("the checker binder range is ordered"))
            .expect("the checker binder span should fit");
        let module = ModuleId::new(813);
        let interface = InterfaceId::new(module, 0);
        let parameter = TypeVariableId::resolved(module, 0);
        let kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let mut imported = ImportedFacts::default();
        imported
            .reserve_interface()
            .expect("the imported interface slot should reserve");
        imported.insert_interface(
            CheckedInterfaceFact {
                id: interface,
                spelling: "Interface".into(),
                parameter: ResolvedTypeVariable {
                    id: parameter,
                    spelling: "F".into(),
                    kind: kind.clone(),
                    origin: Origin::Source(span),
                },
                methods: Box::new([]),
                method_binder_authorities: Box::new([]),
                origin: Origin::Source(span),
                span,
            },
            module,
            span,
            true,
        );

        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            ResolvedRegistry::default().checker_view(&imported, &mut short),
            Err(ResolvedBuildFailure::TypeResource)
        );
        assert_eq!(short.used(), EXACT_WORK - 1);
        assert_eq!(
            imported
                .interface(interface)
                .map(|fact| (&fact.parameter.kind, fact.parameter.id)),
            Some((&kind, parameter)),
            "failed checker-view construction must not mutate imported authority"
        );

        let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
        let view = ResolvedRegistry::default()
            .checker_view(&imported, &mut exact)
            .expect("the exact imported binder budget should fit");
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(exact.charge(1), Err(()));
        assert_eq!(
            view.type_variable(parameter).map(|fact| &fact.kind),
            Some(&kind)
        );
    }

    #[test]
    fn checker_view_implementation_head_binders_have_an_exact_atomic_budget() {
        const ORIGIN_DEPTH: usize = 32_768;
        // Each imported implementation-head binder costs one retained record
        // plus every copied Kind node: Σ(1 + |Kind_i|) = (1 + 3) + (1 + 5).
        const FIRST_KIND_NODES: usize = 3;
        const SECOND_KIND_NODES: usize = 5;
        const EXACT_WORK: usize = (1 + FIRST_KIND_NODES) + (1 + SECOND_KIND_NODES);

        std::thread::Builder::new()
            .name("checker-implementation-head-binders".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    SourceFile::new("checker-implementation-head.ash", "implementation F G")
                        .expect("the implementation-head fixture should fit");
                let implementation_span = source
                    .span(
                        ByteRange::new(0, 14).expect("the implementation range should be ordered"),
                    )
                    .expect("the implementation span should fit");
                let second_span = source
                    .span(ByteRange::new(17, 18).expect("the second binder range is ordered"))
                    .expect("the second binder span should fit");
                let module = ModuleId::new(818);
                let implementation = ImplId::new(module, 0);
                let interface = InterfaceId::new(module, 0);
                let first = TypeVariableId::resolved(module, 0);
                let second = TypeVariableId::resolved(module, 1);
                let first_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
                let second_kind = Kind::Arrow(
                    Box::new(Kind::Type),
                    Box::new(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))),
                );
                let first_origin = generated_origin(&source, ORIGIN_DEPTH);
                let first_origin_span = first_origin.primary_span();
                let mut imported = ImportedFacts::default();
                imported
                    .reserve_implementation()
                    .expect("one implementation slot should reserve");
                imported.insert_implementation(
                    CheckedImplementationFact {
                        id: implementation,
                        interface,
                        head_parameters: Box::new([
                            ResolvedTypeVariable {
                                id: first,
                                spelling: "F".into(),
                                kind: first_kind.clone(),
                                origin: first_origin,
                            },
                            ResolvedTypeVariable {
                                id: second,
                                spelling: "G".into(),
                                kind: second_kind.clone(),
                                origin: Origin::Source(second_span),
                            },
                        ]),
                        argument: Type::Variable(first),
                        prerequisites: Box::new([]),
                        methods: Box::new([]),
                        origin: Origin::Source(implementation_span),
                        span: implementation_span,
                    },
                    ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                        from: ModuleId::new(1),
                        to: module,
                        import_span: implementation_span,
                    }]),
                    None,
                );

                let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
                assert_eq!(
                    ResolvedRegistry::default().checker_view(&imported, &mut short),
                    Err(ResolvedBuildFailure::TypeResource)
                );
                assert_eq!(short.used(), EXACT_WORK - 1);
                let source_head = &imported
                    .implementation(implementation)
                    .expect("the source implementation should remain present")
                    .head_parameters;
                assert_eq!(
                    source_head
                        .iter()
                        .map(|parameter| (parameter.id, &parameter.kind))
                        .collect::<Vec<_>>(),
                    vec![(first, &first_kind), (second, &second_kind)],
                    "late checker-view failure must not mutate imported authority"
                );
                assert_eq!(source_head[0].origin.primary_span(), first_origin_span);

                let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
                let view = ResolvedRegistry::default()
                    .checker_view(&imported, &mut exact)
                    .expect("the exact implementation-head binder budget should fit");
                assert_eq!(exact.used(), EXACT_WORK);
                assert_eq!(exact.charge(1), Err(()));
                assert_eq!(
                    view.type_variable(first).map(|parameter| &parameter.kind),
                    Some(&first_kind)
                );
                assert_eq!(
                    view.type_variable(second).map(|parameter| &parameter.kind),
                    Some(&second_kind)
                );
                assert_eq!(
                    imported
                        .implementation(implementation)
                        .expect("the source implementation should remain present")
                        .head_parameters[0]
                        .origin
                        .primary_span(),
                    first_origin_span,
                    "successful checker-view construction must borrow immutable authority"
                );
            })
            .expect("the implementation-head checker worker should spawn")
            .join()
            .expect("late failure and implementation-head teardown must remain iterative");
    }

    #[test]
    fn checker_view_skips_only_the_authenticated_local_nominal_binder() {
        // The canonical nominal parameter is cloned into the retained owner
        // list (record + Kind), cloned once into the lookup map, recorded in
        // the nominal-ID set, routed once, and compared against the source map
        // mirror (record + Source Origin + Kind). It is not cloned a third time.
        const EXACT_WORK: usize = (1 + 3) + (1 + 3) + 1 + 1 + (1 + 1 + 3);

        let source = SourceFile::new("checker-local-nominal.ash", "Local")
            .expect("the local nominal fixture should fit");
        let span = source
            .span(ByteRange::new(0, 5).expect("the local nominal range is ordered"))
            .expect("the local nominal span should fit");
        let module = ModuleId::new(814);
        let nominal = NominalTypeId::new(module, 0);
        let parameter = TypeVariableId::resolved(module, 0);
        let kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                spelling: "Local".into(),
                constructors: Box::new([]),
                origin: Origin::Source(span),
            }],
            Vec::new(),
        )
        .with_type_parameters(vec![(
            nominal,
            vec![ResolvedTypeVariable {
                id: parameter,
                spelling: "F".into(),
                kind: kind.clone(),
                origin: Origin::Source(span),
            }],
        )]);

        let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            registry.checker_view(&ImportedFacts::default(), &mut short),
            Err(ResolvedBuildFailure::TypeResource)
        );
        let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
        let view = registry
            .checker_view(&ImportedFacts::default(), &mut exact)
            .expect("the exact local nominal authority budget should fit");
        assert_eq!(exact.used(), EXACT_WORK);
        assert_eq!(exact.charge(1), Err(()));
        assert_eq!(
            view.type_variable(parameter).map(|fact| &fact.kind),
            Some(&kind)
        );
    }

    #[test]
    fn checker_view_rejects_a_forged_local_nominal_binder_mirror() {
        let source = SourceFile::new("checker-forged-nominal.ash", "Local")
            .expect("the forged nominal fixture should fit");
        let span = source
            .span(ByteRange::new(0, 5).expect("the forged nominal range is ordered"))
            .expect("the forged nominal span should fit");
        let module = ModuleId::new(817);
        let nominal = NominalTypeId::new(module, 0);
        let parameter = TypeVariableId::resolved(module, 0);
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                spelling: "Local".into(),
                constructors: Box::new([]),
                origin: Origin::Source(span),
            }],
            Vec::new(),
        )
        .with_type_parameters(vec![(
            nominal,
            vec![ResolvedTypeVariable {
                id: parameter,
                spelling: "A".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            }],
        )])
        .with_additional_type_variables([ResolvedTypeVariable {
            id: parameter,
            spelling: "Forged".into(),
            kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            origin: Origin::Source(span),
        }]);

        assert_eq!(
            registry.checker_view(&ImportedFacts::default(), &mut TypeWorkBudget::default(),),
            Err(ResolvedBuildFailure::InvalidState)
        );
        assert_eq!(
            registry
                .nominal_parameters(nominal)
                .and_then(|parameters| parameters.first())
                .map(|canonical| (canonical.spelling.as_str(), &canonical.kind)),
            Some(("A", &Kind::Type))
        );
        assert_eq!(
            registry
                .type_variable(parameter)
                .map(|mirror| mirror.spelling.as_str()),
            Some("Forged"),
            "failed checker-view construction must leave source authority unchanged"
        );
    }

    #[test]
    fn checker_view_nominal_mirror_invalidity_precedes_later_type_resource_deterministically() {
        const INVALID_PRECEDENCE_WORK: usize = 7;
        let source = SourceFile::new("checker-order.ash", "Local extra")
            .expect("the checker-order fixture should fit");
        let span = source
            .span(ByteRange::new(0, 5).expect("the nominal range is ordered"))
            .expect("the nominal span should fit");
        let module = ModuleId::new(819);
        let nominal = NominalTypeId::new(module, 0);
        let nominal_parameter = TypeVariableId::resolved(module, 0);
        let later_parameter = TypeVariableId::resolved(module, 1);
        let registry = ResolvedRegistry::new(
            vec![ResolvedNominalType {
                id: nominal,
                spelling: "Local".into(),
                constructors: Box::new([]),
                origin: Origin::Source(span),
            }],
            Vec::new(),
        )
        .with_type_parameters(vec![(
            nominal,
            vec![ResolvedTypeVariable {
                id: nominal_parameter,
                spelling: "A".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            }],
        )])
        .with_additional_type_variables([
            ResolvedTypeVariable {
                id: nominal_parameter,
                spelling: "Forged".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            },
            ResolvedTypeVariable {
                id: later_parameter,
                spelling: "F".into(),
                kind: Kind::Arrow(
                    Box::new(Kind::Type),
                    Box::new(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))),
                ),
                origin: Origin::Source(span),
            },
        ]);

        for _ in 0..32 {
            let mut budget = TypeWorkBudget::with_limit(INVALID_PRECEDENCE_WORK);
            assert_eq!(
                registry.checker_view(&ImportedFacts::default(), &mut budget),
                Err(ResolvedBuildFailure::InvalidState),
            );
            assert_eq!(budget.used(), INVALID_PRECEDENCE_WORK);
        }
        assert_eq!(
            registry
                .type_variable(later_parameter)
                .map(|parameter| parameter.spelling.as_str()),
            Some("F"),
            "repeated failures must leave source authority immutable",
        );
    }

    #[test]
    fn checker_view_rejects_cross_owner_binder_collision_without_mutating_imports() {
        let source = SourceFile::new("checker-binder-collision.ash", "Interface impl")
            .expect("the checker collision fixture should fit");
        let interface_span = source
            .span(ByteRange::new(0, 9).expect("the interface range is ordered"))
            .expect("the interface span should fit");
        let implementation_span = source
            .span(ByteRange::new(10, 14).expect("the implementation range is ordered"))
            .expect("the implementation span should fit");
        let module = ModuleId::new(815);
        let interface = InterfaceId::new(module, 0);
        let implementation = ImplId::new(module, 0);
        let collision = TypeVariableId::resolved(module, 0);
        let mut imported = ImportedFacts::default();
        imported.reserve_interface().expect("one interface slot");
        imported.insert_interface(
            CheckedInterfaceFact {
                id: interface,
                spelling: "Interface".into(),
                parameter: ResolvedTypeVariable {
                    id: collision,
                    spelling: "A".into(),
                    kind: Kind::Type,
                    origin: Origin::Source(interface_span),
                },
                methods: Box::new([]),
                method_binder_authorities: Box::new([]),
                origin: Origin::Source(interface_span),
                span: interface_span,
            },
            module,
            interface_span,
            true,
        );
        imported
            .reserve_implementation()
            .expect("one implementation slot");
        imported.insert_implementation(
            CheckedImplementationFact {
                id: implementation,
                interface,
                head_parameters: Box::new([ResolvedTypeVariable {
                    id: collision,
                    spelling: "B".into(),
                    kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                    origin: Origin::Source(implementation_span),
                }]),
                argument: Type::Variable(collision),
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(implementation_span),
                span: implementation_span,
            },
            ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                from: ModuleId::new(1),
                to: module,
                import_span: implementation_span,
            }]),
            None,
        );

        assert_eq!(
            ResolvedRegistry::default().checker_view(&imported, &mut TypeWorkBudget::default()),
            Err(ResolvedBuildFailure::InvalidState)
        );
        assert_eq!(
            imported
                .interface(interface)
                .map(|fact| fact.parameter.spelling.as_str()),
            Some("A")
        );
        assert_eq!(
            imported
                .implementation(implementation)
                .and_then(|fact| fact.head_parameters.first())
                .map(|parameter| (parameter.id, parameter.spelling.as_str())),
            Some((collision, "B"))
        );
    }

    #[test]
    fn checker_view_constructor_clone_failure_discards_staged_deep_nominal_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("checker-staged-deep-nominal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("checker-staged-nominal.ash", "Deep")
                    .expect("the staged-nominal fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the nominal range should be ordered"))
                    .expect("the nominal range should belong to the fixture");
                let deep_origin_span = source
                    .span(ByteRange::new(0, 1).expect("the deep origin range should be ordered"))
                    .expect("the deep origin range should belong to the fixture");
                let module = ModuleId::new(818);
                let owner = NominalTypeId::new(module, 0);
                let constructor = ConstructorId::new(owner, 0);
                let registry = ResolvedRegistry::new(
                    vec![ResolvedNominalType {
                        id: owner,
                        spelling: "Deep".to_owned(),
                        constructors: Box::new([constructor]),
                        origin: generated_origin(&source, DEPTH),
                    }],
                    vec![ResolvedConstructor {
                        id: constructor,
                        owner,
                        spelling: "Deep".to_owned(),
                        payload: Some(application_type(DEPTH)),
                        origin: Origin::Source(span),
                    }],
                )
                .with_type_parameters(vec![(owner, Vec::new())]);

                let mut short = TypeWorkBudget::with_limit(0);
                assert_eq!(
                    registry.checker_view(&ImportedFacts::default(), &mut short),
                    Err(ResolvedBuildFailure::TypeResource),
                );
                assert_eq!(short.used(), 0);
                assert_eq!(
                    registry
                        .nominal(owner)
                        .map(|nominal| nominal.origin.primary_span()),
                    Some(deep_origin_span),
                    "failed checker-view staging must leave the defining registry immutable",
                );
            })
            .expect("the staged-nominal worker should spawn")
            .join()
            .expect("staged nominal teardown must remain iterative on constructor clone failure");
    }

    #[test]
    fn checker_view_imported_kind_failure_discards_staged_parameter_rows_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        // One family mirror, one local binder record and Kind node, then the
        // imported binder record. Its first Kind node is the one-short cell.
        const ONE_SHORT_WORK: usize = 2 + 2 + 1;

        std::thread::Builder::new()
            .name("checker-staged-parameter-row".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("checker-staged-parameter.ash", "Local Imported")
                    .expect("the staged-parameter fixture should fit");
                let local_span = source
                    .span(ByteRange::new(0, 5).expect("the local range should be ordered"))
                    .expect("the local range should belong to the fixture");
                let imported_span = source
                    .span(ByteRange::new(6, 14).expect("the imported range should be ordered"))
                    .expect("the imported range should belong to the fixture");
                let deep_origin_span = source
                    .span(ByteRange::new(0, 1).expect("the deep origin range should be ordered"))
                    .expect("the deep origin range should belong to the fixture");
                let local_module = ModuleId::new(819);
                let local_owner = NominalTypeId::new(local_module, 0);
                let local_parameter = TypeVariableId::resolved(local_module, 0);
                let registry = ResolvedRegistry::new(
                    vec![ResolvedNominalType {
                        id: local_owner,
                        spelling: "Local".to_owned(),
                        constructors: Box::new([]),
                        origin: Origin::Source(local_span),
                    }],
                    Vec::new(),
                )
                .with_type_parameters(vec![(
                    local_owner,
                    vec![ResolvedTypeVariable {
                        id: local_parameter,
                        spelling: "A".to_owned(),
                        kind: Kind::Type,
                        origin: generated_origin(&source, DEPTH),
                    }],
                )]);

                let imported_module = ModuleId::new(820);
                let imported_owner = NominalTypeId::new(imported_module, 0);
                let imported_parameter = TypeVariableId::resolved(imported_module, 0);
                let imported_constructor = ConstructorId::new(imported_owner, 0);
                let mut imported = ImportedFacts::default();
                imported
                    .insert_constructor(
                        ImportedConstructorFact {
                            id: imported_constructor,
                            spelling: "Imported".to_owned(),
                            payload: None,
                            scheme: ConstrainedScheme {
                                type_parameters: Box::new([(imported_parameter, Kind::Type)]),
                                requirements: Box::new([]),
                                value_type: Type::Application(
                                    Box::new(Type::Nominal(imported_owner)),
                                    Box::new(Type::Variable(imported_parameter)),
                                ),
                            },
                            origin: Origin::Source(imported_span),
                        },
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .expect("the imported constructor fixture should fit");
                imported
                    .merge_nominal(
                        ImportedNominalFact {
                            id: imported_owner,
                            parameter_count: 1,
                            constructor_count: 1,
                            parameters: Box::new([ResolvedTypeVariable {
                                id: imported_parameter,
                                spelling: "F".to_owned(),
                                kind: Kind::Type,
                                origin: Origin::Source(imported_span),
                            }]),
                            constructors: Box::new([imported_constructor]),
                            access: ImportedTypeAccess::Transparent,
                            display_spelling: Some("Imported".to_owned()),
                            display_is_private: false,
                            origin: Origin::Source(imported_span),
                        },
                        &mut TypeWorkBudget::unbounded(),
                    )
                    .expect("the imported nominal fixture should fit");

                let mut short = TypeWorkBudget::with_limit(ONE_SHORT_WORK);
                assert_eq!(
                    registry.checker_view(&imported, &mut short),
                    Err(ResolvedBuildFailure::TypeResource),
                );
                assert_eq!(short.used(), ONE_SHORT_WORK);
                assert_eq!(
                    registry
                        .nominal_parameters(local_owner)
                        .and_then(|parameters| parameters.first())
                        .map(|parameter| parameter.origin.primary_span()),
                    Some(deep_origin_span),
                    "late failure must leave the defining parameter row immutable",
                );
                assert!(imported.nominal(imported_owner).is_some());
            })
            .expect("the staged-parameter worker should spawn")
            .join()
            .expect("staged parameter-row teardown must remain iterative on Kind failure");
    }

    #[test]
    fn checker_view_late_binder_failure_discards_retained_deep_origin_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        // The first Type-kinded binder consumes one record plus one Kind node.
        const FIRST_BINDER_WORK: usize = 2;

        std::thread::Builder::new()
            .name("checker-deep-binder-failure".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("checker-deep-origin.ash", "First Second")
                    .expect("the deep checker fixture should fit");
                let first_span = source
                    .span(ByteRange::new(0, 5).expect("the first range is ordered"))
                    .expect("the first span should fit");
                let second_span = source
                    .span(ByteRange::new(6, 12).expect("the second range is ordered"))
                    .expect("the second span should fit");
                let deep_origin_span = source
                    .span(ByteRange::new(0, 1).expect("the deep origin range is ordered"))
                    .expect("the deep origin span should fit");
                let module = ModuleId::new(816);
                let mut imported = ImportedFacts::default();
                for (declaration, spelling, span, origin) in [
                    (0, "First", first_span, generated_origin(&source, DEPTH)),
                    (1, "Second", second_span, Origin::Source(second_span)),
                ] {
                    let interface = InterfaceId::new(module, declaration);
                    imported.reserve_interface().expect("one interface slot");
                    imported.insert_interface(
                        CheckedInterfaceFact {
                            id: interface,
                            spelling: spelling.into(),
                            parameter: ResolvedTypeVariable {
                                id: TypeVariableId::resolved(module, declaration),
                                spelling: "A".into(),
                                kind: Kind::Type,
                                origin,
                            },
                            methods: Box::new([]),
                            method_binder_authorities: Box::new([]),
                            origin: Origin::Source(span),
                            span,
                        },
                        module,
                        span,
                        true,
                    );
                }

                let mut budget = TypeWorkBudget::with_limit(FIRST_BINDER_WORK);
                assert_eq!(
                    ResolvedRegistry::default().checker_view(&imported, &mut budget),
                    Err(ResolvedBuildFailure::TypeResource)
                );
                assert_eq!(budget.used(), FIRST_BINDER_WORK);
                assert_eq!(
                    imported
                        .interface(InterfaceId::new(module, 0))
                        .map(|fact| fact.parameter.origin.primary_span()),
                    Some(deep_origin_span),
                    "late failure must leave source authority immutable"
                );
            })
            .expect("the deep checker failure worker should spawn")
            .join()
            .expect("late checker-view failure and teardown should remain iterative");
    }

    #[test]
    fn abstract_nominal_kind_publication_replaces_and_discards_old_facts_iteratively() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("replace-abstract-kind-sidecar".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("replace-abstract-kind.ash", "Old New")
                    .expect("the replacement fixture should fit");
                let old_span = source
                    .span(ByteRange::new(0, 3).expect("the old range should be ordered"))
                    .expect("the old span should belong to the fixture");
                let new_span = source
                    .span(ByteRange::new(4, 7).expect("the new range should be ordered"))
                    .expect("the new span should belong to the fixture");
                let module = ModuleId::new(812);
                let old = NominalTypeId::new(module, 0);
                let new = NominalTypeId::new(module, 1);
                let mut deep_kind = Kind::Type;
                for _ in 0..DEPTH {
                    deep_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(deep_kind));
                }

                let mut registry = ResolvedRegistry::default();
                registry.abstract_nominal_kinds.insert(
                    old,
                    NonMaterializedNominalKindFact {
                        kind: deep_kind,
                        origin: old_span,
                    },
                );
                let mut replacement = HashMap::new();
                replacement.insert(
                    new,
                    NonMaterializedNominalKindFact {
                        kind: Kind::Type,
                        origin: new_span,
                    },
                );

                let registry = registry.with_abstract_nominal_facts(HashMap::new(), replacement);
                assert!(
                    registry.nominal_kind(old).is_none(),
                    "publication must discard every fact from the displaced allocation",
                );
                assert!(matches!(
                    registry.nominal_kind(new),
                    Some(CanonicalNominalKind::Frozen {
                        kind: Kind::Type,
                        origin,
                    }) if origin == new_span
                ));
            })
            .expect("the replacement thread should start")
            .join()
            .expect("deep displaced Kind publication and teardown must remain stack-safe");
    }

    fn resolved_interface_with_annotation(
        module: ModuleId,
        span: Span,
        annotation: Type,
    ) -> ResolvedInterfaceDeclaration {
        let interface = InterfaceId::new(module, 0);
        ResolvedInterfaceDeclaration {
            id: interface,
            public: false,
            spelling: "Deep".into(),
            parameter: ResolvedTypeVariable {
                id: TypeVariableId::new(0),
                spelling: "A".into(),
                kind: crate::types::Kind::Type,
                origin: Origin::Source(span),
            },
            methods: vec![ResolvedInterfaceMethod {
                id: MethodId::new(interface, 0),
                spelling: "method".into(),
                annotation: ResolvedType {
                    ty: annotation,
                    provenance: ResolvedTypeProvenance::new(
                        vec![ResolvedTypeProvenanceNode::Fact(span)],
                        0,
                    ),
                    origin: Origin::Source(span),
                    span,
                },
                type_parameters: Box::new([]),
                has_explicit_type_parameters: false,
                origin: Origin::Source(span),
                span,
            }]
            .into_boxed_slice(),
            origin: Origin::Source(span),
            span,
        }
    }

    fn checked_module_with_interface(
        module: ModuleId,
        span: Span,
        interface: ResolvedInterfaceDeclaration,
        exports: ExportSummary,
    ) -> CheckedModule {
        let resolved = ResolvedModule::new(ResolvedModuleParts {
            module,
            registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
            imported: ImportedFacts::default(),
            direct_dependencies: Vec::new(),
            declaration_order: vec![ResolvedDeclarationIndex::Interface(0)],
            interfaces: vec![interface],
            implementations: Vec::new(),
            definitions: Vec::new(),
            export_candidate: ResolvedExportCandidate::default(),
            span,
        });
        CheckedModule::new(
            resolved,
            CheckedModuleParts {
                definitions: Box::new([]),
                implementations: Box::new([]),
                available_implementations: Box::new([]),
                schemes: Vec::new(),
                checked_interfaces: Box::new([]),
                checked_implementations: Box::new([]),
                interface_facts: Box::new([]),
                implementation_facts: Box::new([]),
                exports,
            },
        )
    }

    #[test]
    fn checked_and_group_interface_annotations_drop_iteratively_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("checked-module-interface-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-interface.ash", "method")
                    .expect("the interface fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 6).expect("the range should be ordered"))
                    .expect("the range should belong to the fixture");
                let module = ModuleId::new(82);

                let (exports, _) =
                    freeze_public_implementation_summary_with_limit(true, usize::MAX);
                let checked = checked_module_with_interface(
                    module,
                    span,
                    resolved_interface_with_annotation(module, span, application_type(DEPTH)),
                    exports.expect("the public summary fixture should freeze"),
                );
                assert!(
                    checked
                        .into_group(&mut crate::interface::InterfaceConstraintBudget::with_limit(0))
                        .is_err(),
                    "the deliberately short transition must drop its checked module",
                );

                let (exports, _) =
                    freeze_public_implementation_summary_with_limit(true, usize::MAX);
                let checked = checked_module_with_interface(
                    module,
                    span,
                    resolved_interface_with_annotation(module, span, application_type(DEPTH)),
                    exports.expect("the public summary fixture should freeze"),
                );
                let group = checked
                    .into_group(&mut crate::interface::InterfaceConstraintBudget::default())
                    .expect("the unbounded transition should retain the interface");
                drop(group);
            })
            .expect("the checked-module thread should start")
            .join()
            .expect("checked and grouped interfaces must dismantle types iteratively");
    }

    #[test]
    fn checked_module_moves_opaque_bodies_and_ordered_availability_into_group() {
        let source = SourceFile::new("checked-boundary.ash", "main")
            .expect("the checked-boundary fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the fixture range should be ordered"))
            .expect("the fixture range should belong to the source");
        let module = ModuleId::new(21);
        let binder = Binder {
            id: BinderId::resolved(module, 0),
            spelling: "main".into(),
            origin: Origin::Source(span),
        };
        let definition = CheckedDefinition::new(ResolvedDefinition {
            kind: ResolvedDefinitionKind::Equational(ResolvedEquationalGlobal {
                interface: ResolvedExternalInterface {
                    name: binder.clone(),
                    annotation: ResolvedType {
                        ty: Type::Unit,
                        provenance: ResolvedTypeProvenance::new(
                            vec![ResolvedTypeProvenanceNode::Fact(span)],
                            0,
                        ),
                        origin: Origin::Source(span),
                        span,
                    },
                    requirements: Box::new([]),
                    type_parameters: Box::new([]),
                    span,
                },
                equations: vec![ResolvedEquation {
                    name: ResolvedEquationHead {
                        binder: binder.id,
                        spelling: binder.spelling,
                        origin: Origin::Source(span),
                    },
                    patterns: Vec::new(),
                    body: ResolvedExpr {
                        kind: ResolvedExprKind::Unit,
                        span,
                    },
                    span,
                }],
            }),
            span,
        });
        let interface = InterfaceId::new(module, 0);
        let implementation_id = ImplId::new(module, 0);
        let implementation = CheckedImplementationBody::new(ResolvedImplementation {
            id: implementation_id,
            public: false,
            interface: ResolvedInterfaceOccurrence {
                id: interface,
                spelling: "Show".into(),
                origin: Origin::Source(span),
            },
            argument: ResolvedType {
                ty: Type::Unit,
                provenance: ResolvedTypeProvenance::new(
                    vec![ResolvedTypeProvenanceNode::Fact(span)],
                    0,
                ),
                origin: Origin::Source(span),
                span,
            },
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites: Box::new([]),
            method_groups: Box::new([]),
            span,
        });
        let imported_id = ImplId::new(ModuleId::new(20), 0);
        let authenticated_dependency = DirectDependencyRoute::new(ModuleId::new(19), span);
        let available = vec![
            AvailableImplementation::imported(
                imported_id,
                ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                    from: module,
                    to: ModuleId::new(20),
                    import_span: span,
                }]),
            ),
            AvailableImplementation::local(implementation_id),
        ]
        .into_boxed_slice();
        let resolved = ResolvedModule::new(ResolvedModuleParts {
            module,
            registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
            imported: ImportedFacts::default(),
            direct_dependencies: vec![authenticated_dependency],
            declaration_order: vec![
                ResolvedDeclarationIndex::Global(0),
                ResolvedDeclarationIndex::Implementation(0),
            ],
            interfaces: Vec::new(),
            implementations: Vec::new(),
            definitions: Vec::new(),
            export_candidate: ResolvedExportCandidate::default(),
            span,
        });
        let exports = ExportSummary {
            module,
            terms: HashMap::new(),
            term_order: Vec::new(),
            nominals: HashMap::new(),
            nominal_order: Vec::new(),
            nominal_names_by_id: HashMap::new(),
            constructors: HashMap::new(),
            constructor_order: Vec::new(),
            constructor_names_by_id: HashMap::new(),
            hidden_constructors: HashMap::new(),
            hidden_constructor_order: Vec::new(),
            interface_names: HashMap::new(),
            interface_name_order: Vec::new(),
            method_names: HashMap::new(),
            method_name_order: Vec::new(),
            interfaces: Vec::new(),
            interface_positions: HashMap::new(),
            hidden_interfaces: Vec::new(),
            implementations: Vec::new(),
            implementation_positions: HashMap::new(),
            hidden_nominals: HashMap::new(),
            hidden_nominal_order: Vec::new(),
            withheld: HashMap::new(),
            withheld_order: Vec::new(),
        };
        let checked = CheckedModule::new(
            resolved,
            CheckedModuleParts {
                definitions: vec![definition].into_boxed_slice(),
                implementations: vec![implementation].into_boxed_slice(),
                available_implementations: available,
                schemes: Vec::new(),
                checked_interfaces: Box::new([]),
                checked_implementations: Box::new([]),
                interface_facts: Box::new([]),
                implementation_facts: Box::new([]),
                exports,
            },
        );
        let definition_kind_address =
            checked.definitions()[0].kind() as *const ResolvedDefinitionKind;
        let implementation_address =
            checked.implementations()[0].source() as *const ResolvedImplementation;

        let group = checked
            .into_group(&mut crate::interface::InterfaceConstraintBudget::default())
            .expect("the checked module should retain its empty public authorization table");
        assert_eq!(group.direct_dependencies(), &[authenticated_dependency]);
        assert_ne!(
            group.direct_dependencies()[0].target(),
            match group.available_implementations()[0].route() {
                ImplementationRoute::DirectImport {
                    direct_dependency, ..
                } => direct_dependency,
                ImplementationRoute::Local => panic!("the test route should be imported"),
            },
            "the authenticated direct-edge input must remain independent of a forged available route",
        );
        let checked_definition_view: &[CheckedDefinition] = group.definitions();
        let checked_implementation_view: &[CheckedImplementationBody] = group.implementations();

        assert_eq!(checked_definition_view.len(), 1);
        assert_eq!(checked_implementation_view.len(), 1);
        assert_eq!(checked_definition_view[0].span(), span);
        assert!(matches!(
            checked_definition_view[0].kind(),
            ResolvedDefinitionKind::Equational(_)
        ));
        assert_eq!(
            checked_definition_view[0].kind() as *const ResolvedDefinitionKind,
            definition_kind_address
        );
        assert_eq!(
            checked_implementation_view[0].source() as *const ResolvedImplementation,
            implementation_address
        );
        assert_eq!(
            group
                .available_implementations()
                .iter()
                .map(|available| (available.id(), available.route()))
                .collect::<Vec<_>>(),
            vec![
                (
                    imported_id,
                    ImplementationRoute::DirectImport {
                        direct_dependency: ModuleId::new(20),
                        available_at: span,
                    },
                ),
                (implementation_id, ImplementationRoute::Local),
            ]
        );
    }

    #[test]
    fn raw_and_checked_body_owners_destroy_deep_source_iteratively() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                fn deep_expression(span: Span) -> ResolvedExpr {
                    let mut body = ResolvedExpr {
                        kind: ResolvedExprKind::Unit,
                        span,
                    };
                    for _ in 0..20_000 {
                        body = ResolvedExpr {
                            kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
                                function: Box::new(ResolvedExpr {
                                    kind: ResolvedExprKind::Unit,
                                    span,
                                }),
                                argument: Box::new(body),
                            }),
                            span,
                        };
                    }
                    body
                }

                let source = SourceFile::new("deep-checked-body.ash", "body")
                    .expect("the deep-body fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the fixture range should be ordered"))
                    .expect("the fixture range should belong to the source");
                let module = ModuleId::new(22);
                let binder_id = BinderId::resolved(module, 0);
                let raw_module = ResolvedModule::new(ResolvedModuleParts {
                    module,
                    registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
                    imported: ImportedFacts::default(),
                    direct_dependencies: Vec::new(),
                    declaration_order: vec![ResolvedDeclarationIndex::Global(0)],
                    interfaces: Vec::new(),
                    implementations: Vec::new(),
                    definitions: vec![ResolvedDefinition {
                        kind: ResolvedDefinitionKind::Equational(ResolvedEquationalGlobal {
                            interface: ResolvedExternalInterface {
                                name: Binder {
                                    id: binder_id,
                                    spelling: "raw_deep".into(),
                                    origin: Origin::Source(span),
                                },
                                annotation: ResolvedType {
                                    ty: Type::Unit,
                                    provenance: ResolvedTypeProvenance::new(
                                        vec![ResolvedTypeProvenanceNode::Fact(span)],
                                        0,
                                    ),
                                    origin: Origin::Source(span),
                                    span,
                                },
                                requirements: Box::new([]),
                                type_parameters: Box::new([]),
                                span,
                            },
                            equations: vec![ResolvedEquation {
                                name: ResolvedEquationHead {
                                    binder: binder_id,
                                    spelling: "raw_deep".into(),
                                    origin: Origin::Source(span),
                                },
                                patterns: Vec::new(),
                                body: deep_expression(span),
                                span,
                            }],
                        }),
                        span,
                    }],
                    export_candidate: ResolvedExportCandidate::default(),
                    span,
                });
                drop(raw_module);

                let definition = CheckedDefinition::new(ResolvedDefinition {
                    kind: ResolvedDefinitionKind::Equational(ResolvedEquationalGlobal {
                        interface: ResolvedExternalInterface {
                            name: Binder {
                                id: binder_id,
                                spelling: "deep".into(),
                                origin: Origin::Source(span),
                            },
                            annotation: ResolvedType {
                                ty: Type::Unit,
                                provenance: ResolvedTypeProvenance::new(
                                    vec![ResolvedTypeProvenanceNode::Fact(span)],
                                    0,
                                ),
                                origin: Origin::Source(span),
                                span,
                            },
                            requirements: Box::new([]),
                            type_parameters: Box::new([]),
                            span,
                        },
                        equations: vec![ResolvedEquation {
                            name: ResolvedEquationHead {
                                binder: binder_id,
                                spelling: "deep".into(),
                                origin: Origin::Source(span),
                            },
                            patterns: Vec::new(),
                            body: deep_expression(span),
                            span,
                        }],
                    }),
                    span,
                });
                drop(definition);

                let implementation_id = ImplId::new(module, 0);
                let implementation = CheckedImplementationBody::new(ResolvedImplementation {
                    id: implementation_id,
                    public: false,
                    interface: ResolvedInterfaceOccurrence {
                        id: InterfaceId::new(module, 0),
                        spelling: "Deep".into(),
                        origin: Origin::Source(span),
                    },
                    argument: ResolvedType {
                        ty: Type::Unit,
                        provenance: ResolvedTypeProvenance::new(
                            vec![ResolvedTypeProvenanceNode::Fact(span)],
                            0,
                        ),
                        origin: Origin::Source(span),
                        span,
                    },
                    head_parameters: Box::new([]),
                    prerequisite_only_parameters: Box::new([]),
                    prerequisites: Box::new([]),
                    method_groups: vec![ResolvedImplementationMethodGroup {
                        method: None,
                        identity: None,
                        binder: Binder {
                            id: BinderId::resolved(module, 1),
                            spelling: "method".into(),
                            origin: Origin::Source(span),
                        },
                        equations: vec![ResolvedEquation {
                            name: ResolvedEquationHead {
                                binder: BinderId::resolved(module, 1),
                                spelling: "method".into(),
                                origin: Origin::Source(span),
                            },
                            patterns: Vec::new(),
                            body: deep_expression(span),
                            span,
                        }]
                        .into_boxed_slice(),
                        span,
                    }]
                    .into_boxed_slice(),
                    span,
                });
                assert_eq!(implementation.id(), implementation_id);
                drop(implementation);
            })
            .expect("the small-stack checked-body thread should start")
            .join()
            .expect("raw and checked body teardown must remain iterative");
    }

    #[test]
    fn checked_impl_summary_clone_uses_its_exact_constraint_budget() {
        let source = SourceFile::new("checked-impl-summary.ash", "impl")
            .expect("the summary fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the summary range should be ordered"))
            .expect("the summary range should belong to the fixture");
        let module = ModuleId::new(8);
        let interface = InterfaceId::new(module, 0);
        let implementation = ImplId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let fact = CheckedImplementationFact {
            id: implementation,
            interface,
            head_parameters: Box::new([]),
            argument: Type::Int,
            prerequisites: Box::new([]),
            methods: vec![CheckedImplementationMethodFact {
                id: ImplMethodId::new(implementation, method),
                method,
                binder: BinderId::resolved(module, 0),
                scheme: ConstrainedScheme {
                    type_parameters: Box::new([]),
                    requirements: Box::new([]),
                    value_type: Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                },
                head_type_parameter_count: 0,
                origin: Origin::Source(span),
                span,
            }]
            .into_boxed_slice(),
            origin: Origin::Source(span),
            span,
        };

        let mut type_work = TypeWorkBudget::default();
        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(10);
        assert_eq!(
            clone_checked_implementation_fact(&fact, &mut type_work, &mut short),
            Err(ResolvedBuildFailure::ConstraintResource)
        );

        let mut type_work = TypeWorkBudget::default();
        let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(11);
        let cloned = clone_checked_implementation_fact(&fact, &mut type_work, &mut exact)
            .expect("the exact summary budget should clone the checked fact");
        assert_eq!(cloned, fact);
        assert_eq!(exact.used(), 11);
        assert_eq!(exact.charge(1), Err(()));
    }

    #[test]
    fn checked_impl_clone_late_argument_failure_dismantles_deep_head_parameter_provenance() {
        const DEPTH: usize = 32_768;
        const PARAMETER_TYPE_WORK: usize = 2;
        const EXACT_TYPE_WORK: usize = PARAMETER_TYPE_WORK + 1;

        std::thread::Builder::new()
            .name("checked-impl-deep-head-parameter-rejection".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("checked-impl-deep-head.ash", "impl")
                    .expect("the deep checked-implementation source should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the implementation range should be ordered"))
                    .expect("the implementation range should belong to the fixture");
                let module = ModuleId::new(8_001);
                let interface = InterfaceId::new(module, 0);
                let implementation = ImplId::new(module, 0);
                let parameter = TypeVariableId::resolved(module, 0);
                let fact = CheckedImplementationFact {
                    id: implementation,
                    interface,
                    head_parameters: Box::new([ResolvedTypeVariable {
                        id: parameter,
                        spelling: "A".to_owned(),
                        kind: Kind::Type,
                        origin: generated_origin(&source, DEPTH),
                    }]),
                    argument: Type::Unit,
                    prerequisites: Box::new([]),
                    methods: Box::new([]),
                    origin: Origin::Source(span),
                    span,
                };

                let mut short_type = TypeWorkBudget::with_limit(PARAMETER_TYPE_WORK);
                let mut short_constraint = crate::interface::InterfaceConstraintBudget::default();
                assert_eq!(
                    clone_checked_implementation_fact(
                        &fact,
                        &mut short_type,
                        &mut short_constraint,
                    ),
                    Err(ResolvedBuildFailure::TypeResource),
                    "the first argument clone cell must fail after the deep binder clone completes",
                );
                assert_eq!(short_type.used(), PARAMETER_TYPE_WORK);

                let mut exact_type = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
                let mut exact_constraint = crate::interface::InterfaceConstraintBudget::default();
                let cloned = clone_checked_implementation_fact(
                    &fact,
                    &mut exact_type,
                    &mut exact_constraint,
                )
                .expect("the immutable source fact must remain reusable at the exact boundary");
                assert_eq!(exact_type.used(), EXACT_TYPE_WORK);
                assert_eq!(cloned.head_parameters[0].id, parameter);
                drop(cloned);
                drop(fact);
            })
            .expect("the deep checked-implementation clone worker should spawn")
            .join()
            .expect("accepted and rejected head-parameter staging must tear down iteratively");
    }

    #[test]
    fn freeze_rejects_missing_local_hidden_nominal_before_cloning_deep_parameters() {
        const DEPTH: usize = 32_768;
        // Checked-global index + public order + one cloned nominal + collector
        // root and unique-identity index + hidden-candidate scan.
        const PRECLONE_TYPE_WORK: usize = 6;

        std::thread::Builder::new()
            .name("freeze-missing-local-hidden-nominal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("missing-hidden-nominal.ash", "expose")
                    .expect("the hidden-nominal freeze source should fit");
                let span = source
                    .span(ByteRange::new(0, 6).expect("the global range should be ordered"))
                    .expect("the global range should belong to the fixture");
                let module = ModuleId::new(8_002);
                let nominal = NominalTypeId::new(module, 0);
                let parameter_id = TypeVariableId::resolved(module, 0);
                let parameter = |origin| ResolvedTypeVariable {
                    id: parameter_id,
                    spelling: "A".to_owned(),
                    kind: Kind::Type,
                    origin,
                };
                let registry = ResolvedRegistry {
                    nominals: Box::new([]),
                    constructors: Box::new([]),
                    nominal_positions: HashMap::new(),
                    constructor_positions: HashMap::new(),
                    nominal_parameters: HashMap::from([(
                        nominal,
                        vec![parameter(generated_origin(&source, DEPTH))].into_boxed_slice(),
                    )]),
                    type_variables: HashMap::from([(
                        parameter_id,
                        parameter(generated_origin(&source, DEPTH)),
                    )]),
                    global_parameter_rows: Box::new([]),
                    global_parameter_positions: HashMap::new(),
                    abstract_nominal_names: HashMap::new(),
                    abstract_nominal_kinds: HashMap::new(),
                };
                let binder = BinderId::resolved(module, 0);
                let mut export_candidate = ResolvedExportCandidate::default();
                let mut candidate_work = TypeWorkBudget::default();
                export_candidate
                    .try_insert_term(
                        "expose".to_owned(),
                        CandidateGlobal {
                            binder,
                            source: CandidateFactSource::Local,
                            origin: Origin::Source(span),
                        },
                        &mut candidate_work,
                    )
                    .expect("the public term candidate should fit");
                export_candidate
                    .try_insert_hidden_nominal(
                        CandidateHiddenNominal {
                            id: nominal,
                            parameter_count: 1,
                            spelling: "Hidden".to_owned(),
                            origin: Origin::Source(span),
                        },
                        &mut candidate_work,
                    )
                    .expect("the hidden nominal candidate should fit");
                let resolved = ResolvedModule::new(ResolvedModuleParts {
                    module,
                    registry: Arc::new(registry),
                    imported: ImportedFacts::default(),
                    direct_dependencies: Vec::new(),
                    declaration_order: Vec::new(),
                    interfaces: Vec::new(),
                    implementations: Vec::new(),
                    definitions: Vec::new(),
                    export_candidate,
                    span,
                });
                let checked = [CheckedGlobalScheme {
                    binder,
                    spelling: "expose".to_owned(),
                    scheme: ConstrainedScheme {
                        type_parameters: Box::new([]),
                        requirements: Box::new([]),
                        value_type: Type::Nominal(nominal),
                    },
                    origin: Origin::Source(span),
                }];
                let mut type_work = TypeWorkBudget::default();
                let mut constraint_work = crate::interface::InterfaceConstraintBudget::default();
                assert_eq!(
                    ExportSummary::freeze(
                        &resolved,
                        &checked,
                        &[],
                        &[],
                        &[],
                        &mut type_work,
                        &mut constraint_work,
                    ),
                    Err(ResolvedBuildFailure::InvalidState),
                );
                assert_eq!(
                    type_work.used(),
                    PRECLONE_TYPE_WORK,
                    "missing local authority must reject before any parameter clone cell",
                );
                drop(resolved);
                drop(checked);
            })
            .expect("the missing hidden nominal freeze worker should spawn")
            .join()
            .expect("rejected deep hidden authority must tear down iteratively");
    }

    #[test]
    fn implementation_summary_storage_charges_before_both_reserves() {
        const RETAINED: usize = 4;
        const EXACT: usize = RETAINED * 2;

        let mut short_facts = Vec::new();
        let mut short_positions = HashMap::new();
        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(EXACT - 1);
        assert_eq!(
            reserve_summary_implementation_storage(
                &mut short_facts,
                &mut short_positions,
                RETAINED,
                &mut short,
            ),
            Err(ResolvedBuildFailure::ConstraintResource)
        );
        assert_eq!(short.used(), 0);
        assert_eq!(short_facts.capacity(), 0);
        assert_eq!(short_positions.capacity(), 0);

        let mut exact_facts = Vec::new();
        let mut exact_positions = HashMap::new();
        let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(EXACT);
        reserve_summary_implementation_storage(
            &mut exact_facts,
            &mut exact_positions,
            RETAINED,
            &mut exact,
        )
        .expect("the exact wrapper-and-index budget should reserve both stores");
        assert_eq!(exact.used(), EXACT);
        assert!(exact_facts.capacity() >= RETAINED);
        assert!(exact_positions.capacity() >= RETAINED);
        assert_eq!(exact.charge(1), Err(()));
    }

    fn freeze_public_implementation_summary_with_limit(
        retain_public_implementation: bool,
        limit: usize,
    ) -> (Result<ExportSummary, ResolvedBuildFailure>, usize) {
        let route_lengths: &[usize] = if retain_public_implementation {
            &[1]
        } else {
            &[]
        };
        freeze_public_implementation_summary_with_routes(route_lengths, limit)
    }

    fn freeze_public_implementation_summary_with_routes(
        route_lengths: &[usize],
        limit: usize,
    ) -> (Result<ExportSummary, ResolvedBuildFailure>, usize) {
        let source = SourceFile::new("public-implementation-summary.ash", "interface impl")
            .expect("the public implementation summary fixture should fit");
        let interface_span = source
            .span(ByteRange::new(0, 9).expect("the interface span should be ordered"))
            .expect("the interface span should belong to the fixture");
        let implementation_span = source
            .span(ByteRange::new(10, 14).expect("the implementation span should be ordered"))
            .expect("the implementation span should belong to the fixture");
        let defining = ModuleId::new(76);
        let facade = ModuleId::new(77);
        let interface = InterfaceId::new(defining, 0);
        let mut imported = ImportedFacts::default();
        imported
            .reserve_interface()
            .expect("one hidden interface slot should reserve");
        imported.insert_interface(
            CheckedInterfaceFact {
                id: interface,
                spelling: "Render".into(),
                parameter: ResolvedTypeVariable {
                    id: TypeVariableId::new(0),
                    spelling: "A".into(),
                    kind: crate::types::Kind::Type,
                    origin: Origin::Source(interface_span),
                },
                methods: Box::new([]),
                method_binder_authorities: Box::new([]),
                origin: Origin::Source(interface_span),
                span: interface_span,
            },
            defining,
            interface_span,
            true,
        );
        let mut direct_dependencies = Vec::new();
        for (index, route_length) in route_lengths.iter().copied().enumerate() {
            assert!(route_length > 0, "an imported route must contain one hop");
            let implementation = ImplId::new(
                defining,
                u32::try_from(index).expect("the fixture implementation identity should fit"),
            );
            let authorization = || {
                let mut hops = Vec::new();
                let mut from = facade;
                for hop_index in 0..route_length {
                    let to = if hop_index + 1 == route_length {
                        defining
                    } else {
                        ModuleId::new(
                            100 + u32::try_from(index * 16 + hop_index)
                                .expect("the fixture route identity should fit"),
                        )
                    };
                    hops.push(ImplementationRouteHop {
                        from,
                        to,
                        import_span: implementation_span,
                    });
                    from = to;
                }
                ImplementationAuthorization::from_hops(hops)
            };
            direct_dependencies.push(DirectDependencyRoute::new(
                authorization().hops()[0].to,
                implementation_span,
            ));
            imported
                .reserve_implementation()
                .expect("one imported implementation slot should reserve");
            imported
                .reserve_public_implementation()
                .expect("one public implementation slot should reserve");
            imported.insert_implementation(
                CheckedImplementationFact {
                    id: implementation,
                    interface,
                    head_parameters: Box::new([]),
                    argument: match index {
                        0 => Type::Int,
                        1 => Type::Bool,
                        2 => Type::Unit,
                        _ => Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice()),
                    },
                    prerequisites: Box::new([]),
                    methods: Box::new([]),
                    origin: Origin::Source(implementation_span),
                    span: implementation_span,
                },
                authorization(),
                Some(authorization()),
            );
            imported
                .mark_implementation_public(implementation)
                .expect("the imported implementation should become public");
        }
        let resolved = ResolvedModule::new(ResolvedModuleParts {
            module: facade,
            registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
            imported,
            direct_dependencies,
            declaration_order: Vec::new(),
            interfaces: Vec::new(),
            implementations: Vec::new(),
            definitions: Vec::new(),
            export_candidate: ResolvedExportCandidate::default(),
            span: implementation_span,
        });
        let mut type_work = TypeWorkBudget::default();
        let mut constraint_work = crate::interface::InterfaceConstraintBudget::with_limit(limit);
        let result = ExportSummary::freeze(
            &resolved,
            &[],
            &[],
            &[],
            &[],
            &mut type_work,
            &mut constraint_work,
        );
        (result, constraint_work.used())
    }

    #[test]
    fn public_implementation_summary_charges_storage_and_closure_inspection() {
        // Two public-implementation storage cells, one authorization-record
        // cell, two authorization-validity cells, three checked-fact clone
        // cells, one route-clone cell, and six retained/reference/hidden-
        // interface closure cells, including both transient hidden-identity
        // indexes. Authorization validity owns the route scan; the caller does
        // not charge those hops a second time.
        const EXACT_WORK: usize = 2 + 1 + 2 + 3 + 1 + 6;
        let (empty, empty_used) = freeze_public_implementation_summary_with_limit(false, 0);
        let empty = empty.expect("an unused imported interface should require no constraint work");
        assert_eq!(empty_used, 0);
        assert!(empty.implementations().next().is_none());
        assert!(empty.hidden_interfaces().next().is_none());

        let (short, short_used) =
            freeze_public_implementation_summary_with_limit(true, EXACT_WORK - 1);
        assert_eq!(short, Err(ResolvedBuildFailure::ConstraintResource));
        assert_eq!(short_used, EXACT_WORK - 1);

        let (exact, exact_used) = freeze_public_implementation_summary_with_limit(true, EXACT_WORK);
        let summary = exact
            .expect("the exact storage-and-closure budget should retain one public implementation");
        assert_eq!(exact_used, EXACT_WORK);
        assert_eq!(summary.implementations().count(), 1);
        assert_eq!(summary.hidden_interfaces().count(), 1);
    }

    #[test]
    fn linked_public_authorization_move_has_an_exact_preflight_budget() {
        const SUMMARY_FREEZE_WORK: usize = 2 + 1 + 2 + 3 + 1 + 6;
        let (short_summary, _) =
            freeze_public_implementation_summary_with_limit(true, SUMMARY_FREEZE_WORK);
        let mut short_summary = short_summary.expect("the public summary should freeze");
        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(2);
        assert_eq!(
            short_summary.take_public_implementation_authorizations(&mut short),
            Err(()),
        );
        assert_eq!(short.used(), 1, "the record visit precedes aggregate work");
        assert_eq!(
            short_summary.implementations().count(),
            1,
            "failed preflight must not drain the frozen summary",
        );

        let (exact_summary, _) =
            freeze_public_implementation_summary_with_limit(true, SUMMARY_FREEZE_WORK);
        let mut exact_summary = exact_summary.expect("the public summary should freeze");
        let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(3);
        let retained = exact_summary
            .take_public_implementation_authorizations(&mut exact)
            .expect("one record, one hop, and one storage slot should fit exactly");
        let [retained] = retained.as_ref() else {
            panic!("the linked table should retain one lightweight authorization");
        };
        assert_eq!(retained.authorization().hops().len(), 1);
        assert_eq!(exact.used(), 3);
        assert!(exact_summary.implementations().next().is_none());
    }

    #[test]
    fn linked_public_authorization_move_charges_two_records_plus_every_hop() {
        const ROUTE_LENGTHS: &[usize] = &[1, 2, 4, 7];
        const ENTRIES: usize = ROUTE_LENGTHS.len();
        const TOTAL_HOPS: usize = 1 + 2 + 4 + 7;
        const EXACT: usize = 2 * ENTRIES + TOTAL_HOPS;

        let (short_summary, _) =
            freeze_public_implementation_summary_with_routes(ROUTE_LENGTHS, usize::MAX);
        let mut short_summary = short_summary.expect("the varying-route summary should freeze");
        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(EXACT - 1);
        assert_eq!(
            short_summary.take_public_implementation_authorizations(&mut short),
            Err(()),
        );
        assert_eq!(short.used(), ENTRIES);
        assert_eq!(
            short_summary
                .implementations()
                .map(|implementation| implementation.authorization().hops().len())
                .collect::<Vec<_>>(),
            ROUTE_LENGTHS,
            "failed aggregate preflight must leave every summary route undrained",
        );

        let (exact_summary, _) =
            freeze_public_implementation_summary_with_routes(ROUTE_LENGTHS, usize::MAX);
        let mut exact_summary = exact_summary.expect("the varying-route summary should freeze");
        let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(EXACT);
        let retained = exact_summary
            .take_public_implementation_authorizations(&mut exact)
            .expect("two units per record plus every route hop should fit exactly");
        assert_eq!(exact.used(), EXACT);
        assert_eq!(exact.charge(1), Err(()));
        assert_eq!(
            retained
                .iter()
                .map(|authorization| authorization.authorization().hops().len())
                .collect::<Vec<_>>(),
            ROUTE_LENGTHS,
        );
        assert!(exact_summary.implementations().next().is_none());
    }

    fn freeze_transparent_constructor_aliases_with_limit(
        family_width: usize,
        alias_count: usize,
        limit: usize,
    ) -> (Result<ExportSummary, ResolvedBuildFailure>, usize) {
        let source = SourceFile::new("transparent-family-summary.ash", "constructor")
            .expect("the constructor-family fixture should fit");
        let span = source
            .span(ByteRange::new(0, 11).expect("the constructor span should be ordered"))
            .expect("the constructor span should belong to the fixture");
        let base = ModuleId::new(72);
        let facade = ModuleId::new(73);
        let nominal = NominalTypeId::new(base, 0);
        let constructors = (0..family_width)
            .map(|index| {
                ConstructorId::new(
                    nominal,
                    u32::try_from(index).expect("the family index should fit"),
                )
            })
            .collect::<Vec<_>>();
        let mut imported = ImportedFacts::default();
        imported
            .merge_nominal(
                ImportedNominalFact {
                    id: nominal,
                    parameter_count: 0,
                    constructor_count: constructors.len(),
                    parameters: Box::new([]),
                    constructors: constructors.clone().into_boxed_slice(),
                    access: ImportedTypeAccess::Transparent,
                    display_spelling: Some("Family".into()),
                    display_is_private: false,
                    origin: Origin::Source(span),
                },
                &mut TypeWorkBudget::default(),
            )
            .expect("the transparent nominal fixture should be unique");
        let mut constructor_work = TypeWorkBudget::default();
        for (index, constructor) in constructors.iter().copied().enumerate() {
            imported
                .insert_constructor(
                    ImportedConstructorFact {
                        id: constructor,
                        spelling: format!("Member{index}"),
                        payload: None,
                        scheme: ConstrainedScheme::from_rank1_type(Type::Nominal(nominal)),
                        origin: Origin::Source(span),
                    },
                    &mut constructor_work,
                )
                .expect("the imported constructor fixture should fit");
        }
        let mut export_candidate = ResolvedExportCandidate::default();
        let mut staging_work = TypeWorkBudget::default();
        for alias in 0..alias_count {
            export_candidate
                .try_insert_constructor(
                    format!("Alias{alias}"),
                    CandidateConstructor {
                        id: constructors[0],
                        source: CandidateFactSource::Imported,
                        origin: Origin::Source(span),
                    },
                    &mut staging_work,
                )
                .expect("the constructor alias fixture has an unbounded staging budget");
        }
        let resolved = ResolvedModule::new(ResolvedModuleParts {
            module: facade,
            registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
            imported,
            direct_dependencies: Vec::new(),
            declaration_order: Vec::new(),
            interfaces: Vec::new(),
            implementations: Vec::new(),
            definitions: Vec::new(),
            export_candidate,
            span,
        });
        let mut type_work = TypeWorkBudget::with_limit(limit);
        let result = ExportSummary::freeze(
            &resolved,
            &[],
            &[],
            &[],
            &[],
            &mut type_work,
            &mut crate::interface::InterfaceConstraintBudget::default(),
        );
        (result, type_work.used())
    }

    #[test]
    fn transparent_constructor_family_closure_scans_each_unique_owner_once() {
        const FAMILY_WIDTH: usize = 256;
        const ALIAS_COUNT: usize = 512;
        const UNIQUE_OWNER_WORK: usize = 2;
        const FAMILY_ENTRY_WORK: usize = 3 * FAMILY_WIDTH;
        // Public physical schemes cost one cell per alias; hidden siblings
        // retain their records and schemes; the referenced defining owner then
        // retains one complete hidden nominal family.
        const FULL_EXACT: usize = 2 * ALIAS_COUNT + 8 * FAMILY_WIDTH + 4;

        let traversal_exact = 2 * ALIAS_COUNT + UNIQUE_OWNER_WORK + 1 + FAMILY_ENTRY_WORK;
        let (traversal_short, traversal_short_used) =
            freeze_transparent_constructor_aliases_with_limit(
                FAMILY_WIDTH,
                ALIAS_COUNT,
                traversal_exact - 1,
            );
        assert_eq!(traversal_short, Err(ResolvedBuildFailure::TypeResource));
        assert_eq!(
            traversal_short_used,
            2 * ALIAS_COUNT + UNIQUE_OWNER_WORK + 1,
        );

        let (exact, exact_used) = freeze_transparent_constructor_aliases_with_limit(
            FAMILY_WIDTH,
            ALIAS_COUNT,
            FULL_EXACT,
        );
        let summary = exact.expect("the exact unique-family closure budget should freeze");
        assert_eq!(exact_used, FULL_EXACT);
        assert_eq!(summary.constructors.len(), ALIAS_COUNT);
        assert_eq!(summary.hidden_constructors.len(), FAMILY_WIDTH - 1);
    }

    #[test]
    fn freeze_local_implementation_filter_has_exact_constraint_precharge() {
        let source = SourceFile::new("local-implementation-filter.ash", "impl")
            .expect("the implementation-filter source should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the implementation range should be ordered"))
            .expect("the implementation span should fit");
        let module = ModuleId::new(9_850);
        let implementation = ResolvedImplementation {
            id: ImplId::new(module, 0),
            public: false,
            interface: ResolvedInterfaceOccurrence {
                id: InterfaceId::new(module, 0),
                spelling: "Local".to_owned(),
                origin: Origin::Source(span),
            },
            argument: ResolvedType {
                ty: Type::Unit,
                provenance: ResolvedTypeProvenance::new(
                    vec![ResolvedTypeProvenanceNode::Fact(span)],
                    0,
                ),
                origin: Origin::Source(span),
                span,
            },
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites: Box::new([]),
            method_groups: Box::new([]),
            span,
        };
        let resolved = ResolvedModule::new(ResolvedModuleParts {
            module,
            registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
            imported: ImportedFacts::default(),
            direct_dependencies: Vec::new(),
            declaration_order: Vec::new(),
            interfaces: Vec::new(),
            implementations: vec![implementation],
            definitions: Vec::new(),
            export_candidate: ResolvedExportCandidate::default(),
            span,
        });
        let admitted = [CheckedImplementation {
            source_index: 0,
            id: ImplId::new(module, 0),
            interface: InterfaceId::new(module, 0),
            methods: Box::new([]),
        }];
        let checked = [CheckedImplementationFact {
            id: ImplId::new(module, 0),
            interface: InterfaceId::new(module, 0),
            head_parameters: Box::new([]),
            argument: Type::Unit,
            prerequisites: Box::new([]),
            methods: Box::new([]),
            origin: Origin::Source(span),
            span,
        }];

        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(1);
        assert_eq!(
            ExportSummary::freeze(
                &resolved,
                &[],
                &[],
                &admitted,
                &checked,
                &mut TypeWorkBudget::default(),
                &mut short,
            ),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        assert_eq!(short.used(), 1);
        for _ in 0..2 {
            let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(2);
            let summary = ExportSummary::freeze(
                &resolved,
                &[],
                &[],
                &admitted,
                &checked,
                &mut TypeWorkBudget::default(),
                &mut exact,
            )
            .expect("one exact local implementation scan should freeze");
            assert_eq!(exact.used(), 2);
            assert!(summary.implementations().next().is_none());
        }
    }

    #[test]
    fn whole_freeze_nominal_collection_has_exact_transaction_boundary() {
        const DEPTH: usize = 32_768;
        const TYPE_CELLS: usize = 2 * DEPTH + 1;
        // One checked-global index and one public-order cell precede one full
        // scheme clone and one full nominal-identity traversal.
        const DEEP_EXACT: usize = 2 + 2 * TYPE_CELLS;
        std::thread::Builder::new()
            .name("whole-freeze-nominal-collection".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("whole-freeze-collection.ash", "value hidden")
                    .expect("the whole-freeze source should fit");
                let value_span = source
                    .span(ByteRange::new(0, 5).expect("the value range should be ordered"))
                    .expect("the value span should fit");
                let hidden_span = source
                    .span(ByteRange::new(6, 12).expect("the hidden range should be ordered"))
                    .expect("the hidden span should fit");
                let module = ModuleId::new(9_860);
                let binder = BinderId::resolved(module, 0);
                let mut export_candidate = ResolvedExportCandidate::default();
                export_candidate
                    .try_insert_term(
                        "value".to_owned(),
                        CandidateGlobal {
                            binder,
                            source: CandidateFactSource::Local,
                            origin: Origin::Source(value_span),
                        },
                        &mut TypeWorkBudget::default(),
                    )
                    .expect("the public value candidate should fit");
                let resolved = ResolvedModule::new(ResolvedModuleParts {
                    module,
                    registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
                    imported: ImportedFacts::default(),
                    direct_dependencies: Vec::new(),
                    declaration_order: Vec::new(),
                    interfaces: Vec::new(),
                    implementations: Vec::new(),
                    definitions: Vec::new(),
                    export_candidate,
                    span: value_span,
                });
                let mut deep = Type::Unit;
                for _ in 0..DEPTH {
                    deep = Type::Function(Box::new(Type::Unit), Box::new(deep));
                }
                let checked = [CheckedGlobalScheme {
                    binder,
                    spelling: "value".to_owned(),
                    scheme: ConstrainedScheme::from_rank1_type(deep),
                    origin: Origin::Source(value_span),
                }];

                let mut short = TypeWorkBudget::with_limit(DEEP_EXACT - 1);
                assert_eq!(
                    ExportSummary::freeze(
                        &resolved,
                        &checked,
                        &[],
                        &[],
                        &[],
                        &mut short,
                        &mut crate::interface::InterfaceConstraintBudget::default(),
                    ),
                    Err(ResolvedBuildFailure::TypeResource),
                );
                assert_eq!(
                    short.used(),
                    DEEP_EXACT - 2,
                    "the final two-child scheduling charge is atomic",
                );
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(DEEP_EXACT);
                    let summary = ExportSummary::freeze(
                        &resolved,
                        &checked,
                        &[],
                        &[],
                        &[],
                        &mut exact,
                        &mut crate::interface::InterfaceConstraintBudget::default(),
                    )
                    .expect("the immutable deep input should remain reusable");
                    assert_eq!(exact.used(), DEEP_EXACT);
                    assert!(summary.term("value").is_some());
                    assert!(summary.hidden_nominals().next().is_none());
                }

                let nominal = NominalTypeId::new(module, 0);
                let constructor = ConstructorId::new(nominal, 0);
                let registry = ResolvedRegistry::new(
                    vec![ResolvedNominalType {
                        id: nominal,
                        spelling: "Hidden".to_owned(),
                        constructors: Box::new([constructor]),
                        origin: Origin::Source(hidden_span),
                    }],
                    vec![ResolvedConstructor {
                        id: constructor,
                        owner: nominal,
                        spelling: "Hidden".to_owned(),
                        payload: None,
                        origin: Origin::Source(hidden_span),
                    }],
                )
                .with_type_parameters(vec![(nominal, Vec::new())]);
                let mut export_candidate = ResolvedExportCandidate::default();
                export_candidate
                    .try_insert_term(
                        "value".to_owned(),
                        CandidateGlobal {
                            binder,
                            source: CandidateFactSource::Local,
                            origin: Origin::Source(value_span),
                        },
                        &mut TypeWorkBudget::default(),
                    )
                    .expect("the nominal value candidate should fit");
                export_candidate
                    .try_insert_hidden_nominal(
                        CandidateHiddenNominal {
                            id: nominal,
                            parameter_count: 0,
                            spelling: "Hidden".to_owned(),
                            origin: Origin::Source(hidden_span),
                        },
                        &mut TypeWorkBudget::default(),
                    )
                    .expect("the hidden nominal candidate should fit");
                let resolved = ResolvedModule::new(ResolvedModuleParts {
                    module,
                    registry: Arc::new(registry),
                    imported: ImportedFacts::default(),
                    direct_dependencies: Vec::new(),
                    declaration_order: Vec::new(),
                    interfaces: Vec::new(),
                    implementations: Vec::new(),
                    definitions: Vec::new(),
                    export_candidate,
                    span: value_span,
                });
                let checked = [CheckedGlobalScheme {
                    binder,
                    spelling: "value".to_owned(),
                    scheme: ConstrainedScheme::from_rank1_type(Type::Nominal(nominal)),
                    origin: Origin::Source(value_span),
                }];
                // Prefix 3 = checked index + public order + one cloned nominal
                // cell. The collector's root task is the fourth cell; the
                // unique nominal index is the fifth and must fail atomically.
                let mut short = TypeWorkBudget::with_limit(4);
                assert_eq!(
                    ExportSummary::freeze(
                        &resolved,
                        &checked,
                        &[],
                        &[],
                        &[],
                        &mut short,
                        &mut crate::interface::InterfaceConstraintBudget::default(),
                    ),
                    Err(ResolvedBuildFailure::TypeResource),
                );
                assert_eq!(short.used(), 4);
                let mut record_short = TypeWorkBudget::with_limit(7);
                assert_eq!(
                    ExportSummary::freeze(
                        &resolved,
                        &checked,
                        &[],
                        &[],
                        &[],
                        &mut record_short,
                        &mut crate::interface::InterfaceConstraintBudget::default(),
                    ),
                    Err(ResolvedBuildFailure::TypeResource),
                );
                assert_eq!(
                    record_short.used(),
                    6,
                    "the two-cell hidden-record retention charge is atomic",
                );
                const NOMINAL_EXACT: usize = 8;
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(NOMINAL_EXACT);
                    let summary = ExportSummary::freeze(
                        &resolved,
                        &checked,
                        &[],
                        &[],
                        &[],
                        &mut exact,
                        &mut crate::interface::InterfaceConstraintBudget::default(),
                    )
                    .expect("the nominal input should remain reusable after U-short rejection");
                    assert_eq!(exact.used(), NOMINAL_EXACT);
                    let retained = summary
                        .hidden_nominals()
                        .next()
                        .expect("the exact freeze should publish the hidden identity");
                    assert_eq!(retained.id, nominal);
                    assert_eq!(retained.access, ImportedTypeAccess::Hidden);
                }
            })
            .expect("the whole-freeze worker should spawn")
            .join()
            .expect("accepted and rejected freeze staging must tear down iteratively");
    }

    fn freeze_shared_spelling_withheld_owners_with_limit(
        owner_count: usize,
        limit: usize,
    ) -> (Result<ExportSummary, ResolvedBuildFailure>, usize) {
        let source = SourceFile::new("shared-withheld-owners.ash", "Seal")
            .expect("the shared withheld-owner fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the constructor span should be ordered"))
            .expect("the constructor span should belong to the fixture");
        let defining = ModuleId::new(74);
        let facade = ModuleId::new(75);
        let mut export_candidate = ResolvedExportCandidate::default();
        let mut type_work = TypeWorkBudget::with_limit(limit);
        for index in 0..owner_count {
            let owner = NominalTypeId::new(
                defining,
                u32::try_from(index).expect("the owner index should fit"),
            );
            for _ in 0..2 {
                if export_candidate
                    .try_insert_withheld(
                        WithheldNamespace::Constructor,
                        "Seal".to_owned(),
                        WithheldExport {
                            kind: WithheldExportKind::OpaqueConstructor,
                            owner: Some(owner),
                            origin: Some(Origin::Source(span)),
                        },
                        &mut type_work,
                    )
                    .is_err()
                {
                    return (Err(ResolvedBuildFailure::TypeResource), type_work.used());
                }
            }
        }
        let resolved = ResolvedModule::new(ResolvedModuleParts {
            module: facade,
            registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
            imported: ImportedFacts::default(),
            direct_dependencies: Vec::new(),
            declaration_order: Vec::new(),
            interfaces: Vec::new(),
            implementations: Vec::new(),
            definitions: Vec::new(),
            export_candidate,
            span,
        });
        let result = ExportSummary::freeze(
            &resolved,
            &[],
            &[],
            &[],
            &[],
            &mut type_work,
            &mut crate::interface::InterfaceConstraintBudget::default(),
        );
        (result, type_work.used())
    }

    #[test]
    fn shared_constructor_spelling_owner_indexes_use_exact_linear_budget() {
        const OWNER_COUNT: usize = 1_024;
        const STAGING_WORK: usize = OWNER_COUNT * 3;
        const FREEZE_WORK: usize = OWNER_COUNT * 4;

        let (short, short_used) = freeze_shared_spelling_withheld_owners_with_limit(
            OWNER_COUNT,
            STAGING_WORK + FREEZE_WORK - 1,
        );
        assert_eq!(short, Err(ResolvedBuildFailure::TypeResource));
        assert_eq!(short_used, STAGING_WORK + OWNER_COUNT);

        let (exact, exact_used) = freeze_shared_spelling_withheld_owners_with_limit(
            OWNER_COUNT,
            STAGING_WORK + FREEZE_WORK,
        );
        let summary = exact.expect("the exact linear owner-index budget should freeze");
        assert_eq!(exact_used, STAGING_WORK + FREEZE_WORK);
        assert_eq!(summary.withheld_count(), OWNER_COUNT);
        assert_eq!(
            summary
                .withheld_export(WithheldNamespace::Constructor, "Seal")
                .and_then(|withheld| withheld.owner),
            Some(NominalTypeId::new(ModuleId::new(74), 0)),
        );
        let mut enumerated = 0;
        for (index, (namespace, spelling, withheld)) in summary.withheld().enumerate() {
            assert_eq!(namespace, WithheldNamespace::Constructor);
            assert_eq!(spelling, "Seal");
            assert_eq!(
                withheld.owner,
                Some(NominalTypeId::new(
                    ModuleId::new(74),
                    u32::try_from(index).expect("the retained owner index should fit"),
                )),
            );
            enumerated += 1;
        }
        assert_eq!(enumerated, OWNER_COUNT);
    }

    fn freeze_hidden_interface_summary_with_limit(
        limit: usize,
    ) -> (Result<ExportSummary, ResolvedBuildFailure>, usize) {
        let source = SourceFile::new("hidden-interface-summary.ash", "interface global")
            .expect("the hidden-interface summary fixture should fit");
        let interface_span = source
            .span(ByteRange::new(0, 9).expect("the interface span should be ordered"))
            .expect("the interface span should belong to the fixture");
        let global_span = source
            .span(ByteRange::new(10, 16).expect("the global span should be ordered"))
            .expect("the global span should belong to the fixture");
        let base = ModuleId::new(70);
        let middle = ModuleId::new(71);
        let interface = InterfaceId::new(base, 0);
        let method = MethodId::new(interface, 0);
        let binder = BinderId::resolved(middle, 0);
        let mut imported = ImportedFacts::default();
        imported
            .reserve_interface()
            .expect("one hidden interface slot should reserve");
        imported.insert_interface(
            CheckedInterfaceFact {
                id: interface,
                spelling: "Render".into(),
                parameter: ResolvedTypeVariable {
                    id: TypeVariableId::new(0),
                    spelling: "A".into(),
                    kind: crate::types::Kind::Type,
                    origin: Origin::Source(interface_span),
                },
                methods: vec![CheckedInterfaceMethodFact {
                    id: method,
                    spelling: "render".into(),
                    type_parameters: Box::new([]),
                    value_type: Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                    origin: Origin::Source(interface_span),
                    span: interface_span,
                }]
                .into_boxed_slice(),
                method_binder_authorities: Box::new([MethodBinderAuthority {
                    method,
                    parameters: Box::new([]),
                }]),
                origin: Origin::Source(interface_span),
                span: interface_span,
            },
            base,
            interface_span,
            true,
        );
        let mut export_candidate = ResolvedExportCandidate::default();
        export_candidate
            .try_insert_term(
                "apply".into(),
                CandidateGlobal {
                    binder,
                    source: CandidateFactSource::Local,
                    origin: Origin::Source(global_span),
                },
                &mut TypeWorkBudget::default(),
            )
            .expect("the export candidate fixture has an unbounded budget");
        let resolved = ResolvedModule::new(ResolvedModuleParts {
            module: middle,
            registry: Arc::new(ResolvedRegistry::new(Vec::new(), Vec::new())),
            imported,
            direct_dependencies: vec![DirectDependencyRoute::new(base, interface_span)],
            declaration_order: Vec::new(),
            interfaces: Vec::new(),
            implementations: Vec::new(),
            definitions: Vec::new(),
            export_candidate,
            span: global_span,
        });
        let checked_globals = [CheckedGlobalScheme {
            binder,
            spelling: "apply".into(),
            scheme: ConstrainedScheme {
                type_parameters: Box::new([]),
                requirements: vec![CheckedRequirement {
                    id: RequirementId::new(RequirementOwner::Global(binder), 0),
                    interface,
                    argument: Type::Int,
                    origin: Origin::Source(global_span),
                    span: global_span,
                }]
                .into_boxed_slice(),
                value_type: Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
            },
            origin: Origin::Source(global_span),
        }];
        let mut type_work = TypeWorkBudget::default();
        let mut constraint_work = crate::interface::InterfaceConstraintBudget::with_limit(limit);
        let result = ExportSummary::freeze(
            &resolved,
            &checked_globals,
            &[],
            &[],
            &[],
            &mut type_work,
            &mut constraint_work,
        );
        (result, constraint_work.used())
    }

    #[test]
    fn hidden_interface_summary_closure_uses_its_exact_constraint_budget() {
        let (short, short_used) = freeze_hidden_interface_summary_with_limit(16);
        assert_eq!(short, Err(ResolvedBuildFailure::ConstraintResource));
        assert_eq!(short_used, 16);

        let (exact, exact_used) = freeze_hidden_interface_summary_with_limit(17);
        let summary = exact.expect("the exact budget should retain one hidden interface fact");
        assert_eq!(exact_used, 17);
        assert!(summary.interface("Render").is_none());
        let hidden = summary
            .hidden_interfaces()
            .next()
            .expect("the foreign interface shape should remain in summary closure");
        assert_eq!(hidden.id.module(), ModuleId::new(70));
        assert!(summary.implementations().next().is_none());
    }

    #[test]
    fn public_interface_route_promotes_an_earlier_hidden_route_without_duplicating_the_fact() {
        let source = SourceFile::new("interface-route.ash", "hidden public")
            .expect("the route fixture should fit");
        let hidden_span = source
            .span(ByteRange::new(0, 6).expect("the hidden span should be ordered"))
            .expect("the hidden span should belong to the fixture");
        let public_span = source
            .span(ByteRange::new(7, 13).expect("the public span should be ordered"))
            .expect("the public span should belong to the fixture");
        let owner = ModuleId::new(80);
        let middle = ModuleId::new(81);
        let interface = InterfaceId::new(owner, 0);
        let mut imported = ImportedFacts::default();
        imported
            .reserve_interface()
            .expect("one imported interface slot should reserve");
        imported.insert_interface(
            CheckedInterfaceFact {
                id: interface,
                spelling: "Render".into(),
                parameter: ResolvedTypeVariable {
                    id: TypeVariableId::new(0),
                    spelling: "A".into(),
                    kind: crate::types::Kind::Type,
                    origin: Origin::Source(hidden_span),
                },
                methods: Box::new([]),
                method_binder_authorities: Box::new([]),
                origin: Origin::Source(hidden_span),
                span: hidden_span,
            },
            middle,
            hidden_span,
            false,
        );

        imported.merge_interface_route(interface, owner, public_span, true);

        let routes = imported.interface_imports().collect::<Vec<_>>();
        assert_eq!(routes.len(), 1);
        assert_eq!(routes[0].direct_dependency, owner);
        assert_eq!(routes[0].available_at, public_span);
        assert!(routes[0].publicly_available);
    }

    #[test]
    fn first_public_interface_route_survives_hidden_and_duplicate_public_routes() {
        let source = SourceFile::new("stable-interface-route.ash", "first hidden second")
            .expect("the stable-route fixture should fit");
        let first = source
            .span(ByteRange::new(0, 5).expect("the first span should be ordered"))
            .expect("the first span should belong to the fixture");
        let hidden = source
            .span(ByteRange::new(6, 12).expect("the hidden span should be ordered"))
            .expect("the hidden span should belong to the fixture");
        let second = source
            .span(ByteRange::new(13, 19).expect("the second span should be ordered"))
            .expect("the second span should belong to the fixture");
        let owner = ModuleId::new(82);
        let first_dependency = ModuleId::new(83);
        let interface = InterfaceId::new(owner, 0);
        let mut imported = ImportedFacts::default();
        imported
            .reserve_interface()
            .expect("one imported interface slot should reserve");
        imported.insert_interface(
            CheckedInterfaceFact {
                id: interface,
                spelling: "Render".into(),
                parameter: ResolvedTypeVariable {
                    id: TypeVariableId::new(0),
                    spelling: "A".into(),
                    kind: crate::types::Kind::Type,
                    origin: Origin::Source(first),
                },
                methods: Box::new([]),
                method_binder_authorities: Box::new([]),
                origin: Origin::Source(first),
                span: first,
            },
            first_dependency,
            first,
            true,
        );

        imported.merge_interface_route(interface, ModuleId::new(84), hidden, false);
        imported.merge_interface_route(interface, owner, second, true);

        let route = imported
            .interface_imports()
            .next()
            .expect("one deduplicated interface route should remain");
        assert_eq!(route.direct_dependency, first_dependency);
        assert_eq!(route.available_at, first);
        assert!(route.publicly_available);
    }

    #[test]
    fn imported_impl_identity_dedup_does_not_compare_deep_fact_payloads() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-imported-impl.ash", "impl")
                    .expect("the imported fact fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the fact range should be ordered"))
                    .expect("the fact range should belong to the fixture");
                let module = ModuleId::new(13);
                let implementation = ImplId::new(module, 0);
                let mut argument = Type::Int;
                for _ in 0..20_000 {
                    argument = Type::Function(Box::new(Type::Unit), Box::new(argument));
                }
                let mut imported = ImportedFacts::default();
                imported
                    .reserve_implementation()
                    .expect("one imported fact slot should reserve");
                imported.insert_implementation(
                    CheckedImplementationFact {
                        id: implementation,
                        interface: InterfaceId::new(module, 0),
                        head_parameters: Box::new([]),
                        argument,
                        prerequisites: Box::new([]),
                        methods: Box::new([]),
                        origin: Origin::Source(span),
                        span,
                    },
                    ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                        from: ModuleId::new(12),
                        to: module,
                        import_span: span,
                    }]),
                    None,
                );

                for _ in 0..2 {
                    assert_eq!(
                        imported.implementation(implementation).map(|fact| fact.id),
                        Some(implementation)
                    );
                }
                drop(imported);
            })
            .expect("the small-stack imported fact thread should start")
            .join()
            .expect("identity-only dedup and cleanup should remain iterative");
    }

    #[test]
    fn implementation_authorization_order_excludes_source_identity() {
        let first_source = SourceFile::new("first-route.ash", "abcdefgh")
            .expect("the first route source should fit");
        let second_source = SourceFile::new("second-route.ash", "abcdefgh")
            .expect("the second route source should fit");
        let span = |source: &SourceFile, start, end| {
            source
                .span(ByteRange::new(start, end).expect("the route range should be ordered"))
                .expect("the route range should fit its source")
        };
        let publisher = ModuleId::new(1);
        let middle = ModuleId::new(2);
        let owner = ModuleId::new(4);
        let rank = ImplementationRouteRank::new(0, 0, 0);
        let precedes = |candidate: &ImplementationAuthorization,
                        candidate_rank,
                        existing: &ImplementationAuthorization,
                        existing_rank| {
            candidate
                .candidate_precedes(
                    candidate_rank,
                    existing,
                    existing_rank,
                    &mut crate::interface::InterfaceConstraintBudget::default(),
                )
                .expect("the unbounded route comparison should fit")
        };
        let first = ImplementationAuthorization::from_hops(vec![
            ImplementationRouteHop {
                from: publisher,
                to: middle,
                import_span: span(&first_source, 0, 2),
            },
            ImplementationRouteHop {
                from: middle,
                to: owner,
                import_span: span(&first_source, 3, 5),
            },
        ]);
        let source_distinct_same_key = ImplementationAuthorization::from_hops(vec![
            ImplementationRouteHop {
                from: publisher,
                to: middle,
                import_span: span(&second_source, 0, 2),
            },
            ImplementationRouteHop {
                from: middle,
                to: owner,
                import_span: span(&second_source, 3, 5),
            },
        ]);
        assert!(!precedes(&first, rank, &source_distinct_same_key, rank));
        assert!(!precedes(&source_distinct_same_key, rank, &first, rank));

        let lexicographically_later = ImplementationAuthorization::from_hops(vec![
            ImplementationRouteHop {
                from: publisher,
                to: middle,
                import_span: span(&first_source, 0, 2),
            },
            ImplementationRouteHop {
                from: middle,
                to: ModuleId::new(5),
                import_span: span(&first_source, 3, 5),
            },
        ]);
        assert!(precedes(&first, rank, &lexicographically_later, rank));
        assert!(precedes(
            &lexicographically_later,
            ImplementationRouteRank::new(0, 0, 0),
            &first,
            ImplementationRouteRank::new(1, 0, 0),
        ));
        assert!(!precedes(
            &lexicographically_later,
            ImplementationRouteRank::new(0, 1, 0),
            &first,
            ImplementationRouteRank::new(0, 0, 0),
        ));
        assert!(precedes(
            &lexicographically_later,
            ImplementationRouteRank::new(0, 0, 0),
            &first,
            ImplementationRouteRank::new(0, 0, 1),
        ));
    }

    #[test]
    fn implementation_authorization_comparison_charges_each_visited_hop_pair() {
        const HOPS: usize = 3;
        let source = SourceFile::new("route-comparison.ash", "abcdefghijkl")
            .expect("the comparison source should fit");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("the route range should be ordered"))
                .expect("the route range should fit")
        };
        let rank = ImplementationRouteRank::new(0, 0, 0);
        let candidate = ImplementationAuthorization::from_hops(vec![
            ImplementationRouteHop {
                from: ModuleId::new(1),
                to: ModuleId::new(2),
                import_span: span(0, 2),
            },
            ImplementationRouteHop {
                from: ModuleId::new(2),
                to: ModuleId::new(3),
                import_span: span(3, 5),
            },
            ImplementationRouteHop {
                from: ModuleId::new(3),
                to: ModuleId::new(4),
                import_span: span(6, 8),
            },
        ]);
        let existing = ImplementationAuthorization::from_hops(vec![
            ImplementationRouteHop {
                from: ModuleId::new(1),
                to: ModuleId::new(2),
                import_span: span(0, 2),
            },
            ImplementationRouteHop {
                from: ModuleId::new(2),
                to: ModuleId::new(3),
                import_span: span(3, 5),
            },
            ImplementationRouteHop {
                from: ModuleId::new(3),
                to: ModuleId::new(4),
                import_span: span(9, 11),
            },
        ]);

        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(HOPS - 1);
        assert_eq!(
            candidate.candidate_precedes(rank, &existing, rank, &mut short),
            Err(())
        );
        assert_eq!(short.used(), HOPS - 1);

        let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(HOPS);
        assert_eq!(
            candidate.candidate_precedes(rank, &existing, rank, &mut exact),
            Ok(true)
        );
        assert_eq!(exact.used(), HOPS);
        assert_eq!(exact.charge(1), Err(()));

        let shorter = ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
            from: ModuleId::new(1),
            to: ModuleId::new(4),
            import_span: span(0, 2),
        }]);
        let mut fast = crate::interface::InterfaceConstraintBudget::with_limit(0);
        assert_eq!(
            shorter.candidate_precedes(rank, &existing, rank, &mut fast),
            Ok(true)
        );
        assert_eq!(
            existing.candidate_precedes(
                ImplementationRouteRank::new(0, 0, 0),
                &candidate,
                ImplementationRouteRank::new(1, 0, 0),
                &mut fast,
            ),
            Ok(true)
        );
        assert_eq!(fast.used(), 0);
    }

    #[test]
    fn implementation_authorization_prepend_has_an_exact_limit() {
        const SUFFIX_HOPS: usize = 3;
        const EXACT: usize = SUFFIX_HOPS + 1;

        let source = SourceFile::new("route-prepend.ash", "first suffix")
            .expect("the prepend source should fit");
        let first_span = source
            .span(ByteRange::new(0, 5).expect("the first-hop range should be ordered"))
            .expect("the first-hop range should fit");
        let suffix_span = source
            .span(ByteRange::new(6, 12).expect("the suffix range should be ordered"))
            .expect("the suffix range should fit");
        let suffix = ImplementationAuthorization::from_hops(vec![
            ImplementationRouteHop {
                from: ModuleId::new(2),
                to: ModuleId::new(3),
                import_span: suffix_span,
            },
            ImplementationRouteHop {
                from: ModuleId::new(3),
                to: ModuleId::new(4),
                import_span: suffix_span,
            },
            ImplementationRouteHop {
                from: ModuleId::new(4),
                to: ModuleId::new(5),
                import_span: suffix_span,
            },
        ]);

        let mut short = crate::interface::InterfaceConstraintBudget::with_limit(EXACT - 1);
        assert_eq!(
            ImplementationAuthorization::prepend(
                ModuleId::new(1),
                ModuleId::new(2),
                first_span,
                &suffix,
                &mut short,
            ),
            Err(()),
        );
        assert_eq!(short.used(), 0, "prepending must charge before allocation");
        assert_eq!(suffix.hops().len(), SUFFIX_HOPS);

        let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(EXACT);
        let prepended = ImplementationAuthorization::prepend(
            ModuleId::new(1),
            ModuleId::new(2),
            first_span,
            &suffix,
            &mut exact,
        )
        .expect("one new hop and the complete suffix should fit exactly");
        assert_eq!(exact.used(), EXACT);
        assert_eq!(exact.charge(1), Err(()));
        assert_eq!(prepended.hops().len(), EXACT);
        assert_eq!(
            prepended.hops()[0],
            ImplementationRouteHop {
                from: ModuleId::new(1),
                to: ModuleId::new(2),
                import_span: first_span,
            }
        );
        assert_eq!(&prepended.hops()[1..], suffix.hops());
    }

    #[test]
    fn implementation_authorization_clone_has_an_exact_flat_small_stack_boundary() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                const HOPS: usize = 20_000;
                let source = SourceFile::new("long-route.ash", "import")
                    .expect("the route source should fit");
                let span = source
                    .span(ByteRange::new(0, 6).expect("the route range should be ordered"))
                    .expect("the route range should fit");
                let mut hops = Vec::new();
                hops.try_reserve(HOPS)
                    .expect("the flat route should reserve");
                for index in 0..u32::try_from(HOPS).expect("the route width should fit") {
                    hops.push(ImplementationRouteHop {
                        from: ModuleId::new(index),
                        to: ModuleId::new(index + 1),
                        import_span: span,
                    });
                }
                let authorization = ImplementationAuthorization::from_hops(hops);

                let mut short = crate::interface::InterfaceConstraintBudget::with_limit(HOPS - 1);
                assert_eq!(authorization.clone_with_budget(&mut short), Err(()));
                assert_eq!(short.used(), 0);

                let mut exact = crate::interface::InterfaceConstraintBudget::with_limit(HOPS);
                let copied = authorization
                    .clone_with_budget(&mut exact)
                    .expect("the exact budget should copy every route hop");
                assert_eq!(exact.used(), HOPS);
                assert_eq!(copied.hops(), authorization.hops());
                drop(copied);
                drop(authorization);
            })
            .expect("the small-stack authorization thread should start")
            .join()
            .expect("flat authorization copying and destruction should fit the small stack");
    }

    #[test]
    fn binder_identities_separate_modules_and_generated_core() {
        let first = BinderId::resolved(ModuleId::new(0), 0);
        let second = BinderId::resolved(ModuleId::new(1), 0);
        let generated = BinderId::generated(0);

        assert_ne!(first, second);
        assert_ne!(first, generated);
        assert_eq!(first.module(), Some(ModuleId::new(0)));
        assert_eq!(generated.module(), None);
    }

    #[test]
    fn destroys_replaced_additional_type_variables_on_a_small_stack() {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(256 * 1024)
                .spawn_scoped(scope, move || {
                    let file = SourceFile::new("additional parameter", "parameter")
                        .expect("test source should fit");
                    let span = file
                        .span(ByteRange::new(0, 1).expect("ordered parameter range"))
                        .expect("parameter range should belong to source");
                    let mut origin = Origin::Source(span);
                    for index in 0..32_768 {
                        origin = if index % 2 == 0 {
                            Origin::Generated {
                                cause: Box::new(origin),
                                reason: GeneratedReason::TypeChecking,
                            }
                        } else {
                            Origin::Related {
                                primary: Box::new(origin),
                                related: vec![span],
                            }
                        };
                    }
                    let parameter = TypeVariableId::new(0);
                    let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
                        .with_additional_type_variables([
                            ResolvedTypeVariable {
                                id: parameter,
                                spelling: "A".into(),
                                kind: crate::types::Kind::Type,
                                origin,
                            },
                            ResolvedTypeVariable {
                                id: parameter,
                                spelling: "B".into(),
                                kind: crate::types::Kind::Type,
                                origin: Origin::Source(span),
                            },
                        ]);
                    assert_eq!(
                        registry
                            .type_variable(parameter)
                            .map(|parameter| parameter.spelling.as_str()),
                        Some("B")
                    );
                    drop(registry);
                })
                .expect("small-stack thread should start")
                .join()
                .expect("replaced additional parameter teardown must fit the small stack");
        });
    }

    #[test]
    fn destroys_replaced_nominal_type_variables_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("replace-nominal-parameters".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let file = SourceFile::new("nominal parameter", "parameter")
                    .expect("the nominal-parameter source should fit");
                let span = file
                    .span(ByteRange::new(0, 1).expect("the parameter range should be ordered"))
                    .expect("the parameter range should belong to the source");
                let owner = NominalTypeId::new(ModuleId::new(94), 0);
                let parameter = TypeVariableId::resolved(ModuleId::new(94), 0);
                let registry =
                    ResolvedRegistry::new(Vec::new(), Vec::new()).with_type_parameters(vec![
                        (
                            owner,
                            vec![ResolvedTypeVariable {
                                id: parameter,
                                spelling: "Deep".to_owned(),
                                kind: crate::types::Kind::Type,
                                origin: generated_origin(&file, DEPTH),
                            }],
                        ),
                        (
                            owner,
                            vec![ResolvedTypeVariable {
                                id: parameter,
                                spelling: "Shallow".to_owned(),
                                kind: crate::types::Kind::Type,
                                origin: Origin::Source(span),
                            }],
                        ),
                    ]);
                assert_eq!(
                    registry
                        .nominal_parameter_entries()
                        .find(|(candidate, _)| *candidate == owner)
                        .and_then(|(_, parameters)| parameters.first())
                        .map(|parameter| parameter.spelling.as_str()),
                    Some("Shallow"),
                );
            })
            .expect("the nominal-parameter replacement thread should start")
            .join()
            .expect("replaced nominal parameters must be dismantled iteratively");
    }

    #[test]
    fn nominal_parameter_rows_reject_late_type_work_and_preserve_source_order_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        // Two deep records cost 2D+2 each; the intervening Type-kinded record
        // costs two. The one-short failure is the final Kind leaf in row two.
        const EXACT_WORK: usize = 4 * DEPTH + 6;

        std::thread::Builder::new()
            .name("nominal-parameter-row-staging".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("parameter-row-staging.ash", "A B C")
                    .expect("the parameter-row fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the parameter range should be ordered"))
                    .expect("the parameter range should belong to the fixture");
                let module = ModuleId::new(9_703);
                let first_owner = NominalTypeId::new(module, 0);
                let second_owner = NominalTypeId::new(module, 1);
                let deep_kind = || {
                    let mut kind = Kind::Type;
                    for _ in 0..DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    kind
                };
                let parameters = || {
                    vec![
                        (
                            first_owner,
                            vec![
                                ResolvedTypeVariable {
                                    id: TypeVariableId::resolved(module, 0),
                                    spelling: "A".to_owned(),
                                    kind: deep_kind(),
                                    origin: generated_origin(&source, DEPTH),
                                },
                                ResolvedTypeVariable {
                                    id: TypeVariableId::resolved(module, 1),
                                    spelling: "B".to_owned(),
                                    kind: Kind::Type,
                                    origin: Origin::Source(span),
                                },
                            ],
                        ),
                        (
                            second_owner,
                            vec![ResolvedTypeVariable {
                                id: TypeVariableId::resolved(module, 2),
                                spelling: "C".to_owned(),
                                kind: deep_kind(),
                                origin: generated_origin(&source, DEPTH),
                            }],
                        ),
                    ]
                };

                let mut short = TypeWorkBudget::with_limit(EXACT_WORK - 1);
                assert!(
                    ResolvedRegistry::default()
                        .with_type_parameters_with_budget(parameters(), &mut short)
                        .is_err(),
                );
                assert_eq!(short.used(), EXACT_WORK - 1);

                let mut exact = TypeWorkBudget::with_limit(EXACT_WORK);
                let registry = ResolvedRegistry::default()
                    .with_type_parameters_with_budget(parameters(), &mut exact)
                    .expect("the exact parameter-row boundary should fit");
                assert_eq!(exact.used(), EXACT_WORK);
                assert_eq!(
                    registry
                        .nominal_parameters
                        .get(&first_owner)
                        .map(Box::as_ref)
                        .expect("the first row should be retained")
                        .iter()
                        .map(|parameter| parameter.id)
                        .collect::<Vec<_>>(),
                    vec![
                        TypeVariableId::resolved(module, 0),
                        TypeVariableId::resolved(module, 1),
                    ],
                    "each nominal row must preserve source binder order",
                );
                assert_eq!(
                    registry
                        .nominal_parameters
                        .get(&second_owner)
                        .map(Box::as_ref)
                        .and_then(|row| row.first())
                        .map(|parameter| parameter.id),
                    Some(TypeVariableId::resolved(module, 2)),
                );
                for local in 0..3 {
                    assert!(
                        registry
                            .type_variable(TypeVariableId::resolved(module, local))
                            .is_some(),
                    );
                }
                registry.discard_iteratively();
            })
            .expect("the parameter-row worker should spawn")
            .join()
            .expect("late rejection and accepted parameter rows must tear down iteratively");
    }

    #[test]
    fn combined_registry_count_overflow_uses_the_owning_ledger_reason() {
        let mut constraint_total = usize::MAX;
        assert_eq!(
            checked_accumulate(&mut constraint_total, 1),
            Err(ResolvedBuildFailure::ConstraintResource),
        );
        let mut type_total = usize::MAX;
        assert_eq!(
            type_accumulate(&mut type_total, 1),
            Err(ResolvedBuildFailure::TypeResource),
        );
    }
}
