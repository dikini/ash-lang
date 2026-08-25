//! Name-resolved, source-spanned syntax passed to typed elaboration.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::{
    integer::Integer,
    interface::{
        CheckedImplementation, CheckedInterface, CheckedRequirement, ConstrainedScheme,
        EvidenceSlot, ImplId, ImplMethodId, InterfaceId, MethodId, RequirementId,
    },
    module::ModuleId,
    source::{Origin, Span, discard_origin_iteratively},
    surface::SurfaceTypeVisibility,
    types::{
        ConstructorId, NominalTypeId, Type, TypeVariableId, TypeWorkBudget, clone_type_with_budget,
        discard_type_iteratively,
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
    pub(crate) fn new(parts: ResolvedModuleParts) -> Self {
        Self {
            module: parts.module,
            registry: parts.registry,
            imported: parts.imported,
            direct_dependencies: parts.direct_dependencies.into_boxed_slice(),
            declaration_order: parts.declaration_order.into_boxed_slice(),
            interfaces: parts.interfaces.into_boxed_slice(),
            implementations: parts.implementations.into_boxed_slice(),
            definitions: parts.definitions.into_boxed_slice(),
            export_candidate: parts.export_candidate,
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

/// How one implementation entered a checked module's effective environment.
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AvailableImplementation {
    id: ImplId,
    route: ImplementationRoute,
}

impl AvailableImplementation {
    pub(crate) const fn local(id: ImplId) -> Self {
        Self {
            id,
            route: ImplementationRoute::Local,
        }
    }

    pub(crate) const fn direct_import(
        id: ImplId,
        direct_dependency: ModuleId,
        available_at: Span,
    ) -> Self {
        Self {
            id,
            route: ImplementationRoute::DirectImport {
                direct_dependency,
                available_at,
            },
        }
    }

    /// Returns the stable implementation identity.
    #[must_use]
    pub const fn id(self) -> ImplId {
        self.id
    }

    /// Returns the local or first-direct-import availability route.
    #[must_use]
    pub const fn route(self) -> ImplementationRoute {
        self.route
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

    /// Returns the complete source span.
    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }

    pub(crate) fn into_group(mut self) -> ResolvedModuleGroup {
        ResolvedModuleGroup {
            module: self.module,
            direct_dependencies: std::mem::take(&mut self.direct_dependencies),
            declaration_order: std::mem::take(&mut self.declaration_order),
            interfaces: std::mem::take(&mut self.interfaces),
            implementations: std::mem::take(&mut self.implementations),
            definitions: std::mem::take(&mut self.definitions),
            available_implementations: std::mem::take(&mut self.available_implementations),
            schemes: std::mem::take(&mut self.schemes).into_boxed_slice(),
            checked_interfaces: std::mem::take(&mut self.checked_interfaces),
            checked_implementations: std::mem::take(&mut self.checked_implementations),
            interface_facts: std::mem::take(&mut self.interface_facts),
            implementation_facts: std::mem::take(&mut self.implementation_facts),
            span: self.span,
        }
    }
}

impl Drop for CheckedModule {
    fn drop(&mut self) {
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
        available.route = route;
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
    nominals: HashMap<NominalTypeId, ImportedNominalFact>,
    constructors: HashMap<ConstructorId, ImportedConstructorFact>,
    interfaces: Vec<ImportedInterfaceFact>,
    interface_positions: HashMap<InterfaceId, usize>,
    implementations: Vec<ImportedImplementationFact>,
    implementation_positions: HashMap<ImplId, usize>,
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

    /// Looks up one directly imported public implementation by semantic identity.
    #[must_use]
    pub fn implementation(&self, id: ImplId) -> Option<&CheckedImplementationFact> {
        Some(
            &self
                .implementations
                .get(*self.implementation_positions.get(&id)?)?
                .fact,
        )
    }

    pub(crate) fn globals(&self) -> impl Iterator<Item = &ImportedGlobalScheme> {
        self.globals.values()
    }

    pub(crate) fn interface_imports(&self) -> impl Iterator<Item = &ImportedInterfaceFact> {
        self.interfaces.iter()
    }

    pub(crate) fn nominals(&self) -> impl Iterator<Item = &ImportedNominalFact> {
        self.nominals.values()
    }

    pub(crate) fn implementations(&self) -> impl Iterator<Item = &ImportedImplementationFact> {
        self.implementations.iter()
    }

    pub(crate) fn contains_global(&self, id: BinderId) -> bool {
        self.globals.contains_key(&id)
    }

    pub(crate) fn insert_global(&mut self, fact: ImportedGlobalScheme) {
        self.globals.insert(fact.binder, fact);
    }

    pub(crate) fn merge_nominal(
        &mut self,
        mut fact: ImportedNominalFact,
    ) -> Result<(), ImportedNominalConflict> {
        let Some(existing) = self.nominals.get_mut(&fact.id) else {
            self.nominals.insert(fact.id, fact);
            return Ok(());
        };
        let constructor_conflict = !existing.constructors.is_empty()
            && !fact.constructors.is_empty()
            && existing.constructors != fact.constructors;
        if existing.parameter_count != fact.parameter_count
            || existing.parameters != fact.parameters
            || constructor_conflict
            || existing.display_is_private != fact.display_is_private
        {
            for parameter in fact.parameters.into_vec() {
                discard_origin_iteratively(parameter.origin);
            }
            discard_origin_iteratively(fact.origin);
            return Err(ImportedNominalConflict);
        }
        if fact.access.rank() > existing.access.rank() {
            existing.access = fact.access;
            if !fact.constructors.is_empty() {
                existing.constructors = std::mem::take(&mut fact.constructors);
            }
            if fact.display_spelling.is_some() {
                existing.display_spelling = fact.display_spelling.take();
            }
        } else if existing.display_spelling.is_none() {
            existing.display_spelling = fact.display_spelling.take();
        }
        for parameter in fact.parameters.into_vec() {
            discard_origin_iteratively(parameter.origin);
        }
        discard_origin_iteratively(fact.origin);
        Ok(())
    }

    pub(crate) fn contains_constructor(&self, id: ConstructorId) -> bool {
        self.constructors.contains_key(&id)
    }

    pub(crate) fn insert_constructor(&mut self, fact: ImportedConstructorFact) {
        self.constructors.insert(fact.id, fact);
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
        direct_dependency: ModuleId,
        available_at: Span,
    ) {
        let position = self.implementations.len();
        self.implementation_positions.insert(fact.id, position);
        self.implementations.push(ImportedImplementationFact {
            fact,
            direct_dependency,
            available_at,
        });
    }

    pub(crate) fn reserve_implementation(&mut self) -> Result<(), ()> {
        self.implementations.try_reserve(1).map_err(|_| ())?;
        self.implementation_positions.try_reserve(1).map_err(|_| ())
    }
}

impl Drop for ImportedFacts {
    fn drop(&mut self) {
        for (_, fact) in self.globals.drain() {
            drop(fact.scheme);
            discard_origin_iteratively(fact.origin);
        }
        for (_, fact) in self.nominals.drain() {
            for parameter in fact.parameters.into_vec() {
                discard_origin_iteratively(parameter.origin);
            }
            discard_origin_iteratively(fact.origin);
        }
        for (_, fact) in self.constructors.drain() {
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
    }
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
    /// Checked source value type before evidence lowering.
    pub value_type: Type,
    /// Causal method provenance.
    pub origin: Origin,
    /// Complete method-signature span.
    pub span: Span,
}

impl Drop for CheckedInterfaceMethodFact {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.value_type, Type::Unit));
        discard_origin_iteratively(std::mem::replace(
            &mut self.origin,
            Origin::Source(self.span),
        ));
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
    pub argument: Type,
    /// Ordered checked prerequisites.
    pub prerequisites: Box<[CheckedRequirement]>,
    /// Method mappings in interface declaration order.
    pub methods: Box<[CheckedImplementationMethodFact]>,
    /// Causal implementation provenance.
    pub origin: Origin,
    /// Complete implementation span.
    pub span: Span,
}

/// One checked implementation admitted through its first direct import edge.
#[derive(Debug, Eq, PartialEq)]
pub struct ImportedImplementationFact {
    /// Defining implementation fact retained without a body.
    pub fact: CheckedImplementationFact,
    /// Canonical direct dependency that published the implementation.
    pub direct_dependency: ModuleId,
    /// Direct import occurrence that first made the fact available.
    pub available_at: Span,
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
        methods.push(CheckedInterfaceMethodFact {
            id: method.id,
            spelling: method.spelling.clone(),
            value_type: clone_type_with_budget(&method.value_type, type_work)
                .map_err(|()| ResolvedBuildFailure::TypeResource)?,
            origin: method.origin.clone(),
            span: method.span,
        });
    }
    Ok(CheckedInterfaceFact {
        id: fact.id,
        spelling: fact.spelling.clone(),
        parameter: fact.parameter.clone(),
        methods: methods.into_boxed_slice(),
        origin: fact.origin.clone(),
        span: fact.span,
    })
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

    let mut head_parameters = Vec::new();
    head_parameters
        .try_reserve(fact.head_parameters.len())
        .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
    head_parameters.extend(fact.head_parameters.iter().cloned());

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
            origin: method.origin.clone(),
            span: method.span,
        });
    }

    Ok(CheckedImplementationFact {
        id: fact.id,
        interface: fact.interface,
        head_parameters: head_parameters.into_boxed_slice(),
        argument: clone_type_with_budget(&fact.argument, type_work)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?,
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

/// One imported nominal access fact.
#[derive(Debug, Eq, PartialEq)]
pub struct ImportedNominalFact {
    /// Stable defining nominal identity.
    pub id: NominalTypeId,
    /// Number of parameters of kind `Type`.
    pub parameter_count: usize,
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
pub(crate) struct ImportedNominalConflict;

/// One imported transparent constructor fact.
#[derive(Debug, Eq, PartialEq)]
pub struct ImportedConstructorFact {
    /// Stable defining constructor identity.
    pub id: ConstructorId,
    /// Defining source spelling retained for coverage diagnostics.
    pub spelling: String,
    /// Optional semantic payload type.
    pub payload: Option<Type>,
    /// Causal declaration provenance.
    pub origin: Origin,
}

/// Public local declarations selected by resolution but not yet type-checked.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResolvedExportCandidate {
    terms: HashMap<String, CandidateGlobal>,
    nominals: HashMap<String, CandidateNominal>,
    constructors: HashMap<String, CandidateConstructor>,
    hidden_nominals: HashMap<NominalTypeId, CandidateHiddenNominal>,
    withheld: HashMap<(String, WithheldNamespace), WithheldExport>,
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

    /// Looks up one private nominal retained only for checked public schemes.
    #[must_use]
    pub fn hidden_nominal(&self, id: NominalTypeId) -> Option<&CandidateHiddenNominal> {
        self.hidden_nominals.get(&id)
    }

    /// Reports whether one source spelling is withheld because it is private.
    #[must_use]
    pub fn is_private(&self, spelling: &str) -> bool {
        [
            WithheldNamespace::Term,
            WithheldNamespace::Nominal,
            WithheldNamespace::Constructor,
        ]
        .into_iter()
        .any(|namespace| {
            self.withheld
                .get(&(spelling.to_owned(), namespace))
                .is_some_and(|withheld| withheld.kind == WithheldExportKind::Private)
        })
    }

    /// Reports whether a constructor spelling is withheld by opacity.
    #[must_use]
    pub fn is_opaque_constructor(&self, spelling: &str) -> bool {
        self.withheld
            .get(&(spelling.to_owned(), WithheldNamespace::Constructor))
            .is_some_and(|withheld| withheld.kind == WithheldExportKind::OpaqueConstructor)
    }

    pub(crate) fn insert_term(&mut self, spelling: String, candidate: CandidateGlobal) {
        self.terms.insert(spelling, candidate);
    }

    pub(crate) fn insert_nominal(&mut self, spelling: String, candidate: CandidateNominal) {
        self.nominals.insert(spelling, candidate);
    }

    pub(crate) fn insert_constructor(&mut self, spelling: String, candidate: CandidateConstructor) {
        self.constructors.insert(spelling, candidate);
    }

    pub(crate) fn insert_hidden_nominal(&mut self, candidate: CandidateHiddenNominal) {
        self.hidden_nominals.insert(candidate.id, candidate);
    }

    pub(crate) fn insert_withheld(
        &mut self,
        namespace: WithheldNamespace,
        spelling: String,
        withheld: WithheldExport,
    ) {
        self.withheld.insert((spelling, namespace), withheld);
    }
}

impl Drop for ResolvedExportCandidate {
    fn drop(&mut self) {
        for (_, candidate) in self.terms.drain() {
            discard_origin_iteratively(candidate.origin);
        }
        for (_, candidate) in self.nominals.drain() {
            discard_origin_iteratively(candidate.origin);
        }
        for (_, candidate) in self.constructors.drain() {
            discard_origin_iteratively(candidate.origin);
        }
        for (_, candidate) in self.hidden_nominals.drain() {
            discard_origin_iteratively(candidate.origin);
        }
        for (_, withheld) in self.withheld.drain() {
            if let Some(origin) = withheld.origin {
                discard_origin_iteratively(origin);
            }
        }
    }
}

/// One unchecked public global selected by resolution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateGlobal {
    /// Stable local binder identity.
    pub binder: BinderId,
    /// Declaration provenance.
    pub origin: Origin,
}

/// One unchecked public nominal selected by resolution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateNominal {
    /// Stable nominal identity.
    pub id: NominalTypeId,
    /// Opaque or transparent source access.
    pub visibility: SurfaceTypeVisibility,
    /// Declaration provenance.
    pub origin: Origin,
}

/// One unchecked constructor of a public transparent nominal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateConstructor {
    /// Stable constructor identity.
    pub id: ConstructorId,
    /// Declaration provenance.
    pub origin: Origin,
}

/// One private nominal identity available for checked public schemes only.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateHiddenNominal {
    /// Stable nominal identity.
    pub id: NominalTypeId,
    /// Number of parameters of kind `Type`.
    pub parameter_count: usize,
    /// Display-only declaration spelling.
    pub spelling: String,
    /// Declaration provenance.
    pub origin: Origin,
}

/// Why one dependency spelling is withheld from source resolution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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

/// Diagnostic-only metadata for a withheld dependency spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct WithheldExport {
    pub(crate) kind: WithheldExportKind,
    pub(crate) origin: Option<Origin>,
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
    /// Number of parameters of kind `Type`.
    pub parameter_count: usize,
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
    /// Causal declaration provenance.
    pub origin: Origin,
}

/// Checked, body-free exports from one dependency module.
#[derive(Debug, Eq, PartialEq)]
pub struct ExportSummary {
    module: ModuleId,
    terms: HashMap<String, ExportedGlobal>,
    nominals: HashMap<String, ExportedType>,
    nominal_names_by_id: HashMap<NominalTypeId, String>,
    constructors: HashMap<String, ExportedConstructor>,
    constructor_names_by_id: HashMap<ConstructorId, String>,
    interface_names: HashMap<String, InterfaceId>,
    method_names: HashMap<String, MethodId>,
    interfaces: Vec<CheckedInterfaceFact>,
    interface_positions: HashMap<InterfaceId, usize>,
    hidden_interfaces: Vec<CheckedInterfaceFact>,
    implementations: Vec<CheckedImplementationFact>,
    implementation_positions: HashMap<ImplId, usize>,
    hidden_nominals: HashMap<NominalTypeId, ExportedHiddenType>,
    withheld: HashMap<(String, WithheldNamespace), WithheldExport>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ResolvedBuildFailure {
    InvalidState,
    TypeResource,
    ConstraintResource,
}

/// One hidden nominal fact retained by identity without a source name binding.
#[derive(Debug, Eq, PartialEq)]
pub struct ExportedHiddenType {
    /// Stable nominal identity from the defining module.
    pub id: NominalTypeId,
    /// Number of parameters of kind `Type`.
    pub parameter_count: usize,
    /// Ordered declaration parameters, preserving defining identities.
    pub parameters: Box<[ResolvedTypeVariable]>,
    /// Display-only declaration spelling.
    pub spelling: String,
    /// Whether the displayed declaration spelling is private at its definition.
    pub display_is_private: bool,
    /// Causal declaration provenance.
    pub origin: Origin,
}

impl ExportSummary {
    /// Returns the defining module identity.
    #[must_use]
    pub const fn module(&self) -> ModuleId {
        self.module
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
            nominals: HashMap::new(),
            nominal_names_by_id: HashMap::new(),
            constructors: HashMap::new(),
            constructor_names_by_id: HashMap::new(),
            interface_names: HashMap::new(),
            method_names: HashMap::new(),
            interfaces: Vec::new(),
            interface_positions: HashMap::new(),
            hidden_interfaces: Vec::new(),
            implementations: Vec::new(),
            implementation_positions: HashMap::new(),
            hidden_nominals: HashMap::new(),
            withheld: resolved.export_candidate.withheld.clone(),
        };
        for (spelling, candidate) in &resolved.export_candidate.terms {
            let scheme = checked_by_binder
                .get(&candidate.binder)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            summary.terms.insert(
                spelling.clone(),
                ExportedGlobal {
                    binder: scheme.binder,
                    scheme: scheme
                        .scheme
                        .clone_with_budget(type_work)
                        .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                    origin: scheme.origin.clone(),
                },
            );
        }

        constraint_work
            .charge(
                checked_interfaces
                    .len()
                    .saturating_add(checked_implementations.len()),
            )
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        if checked_interfaces.len() != resolved.interfaces.len()
            || admitted_implementations.len() != checked_implementations.len()
            || checked_implementations.len() != resolved.implementations.len()
        {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        summary
            .interfaces
            .try_reserve(checked_interfaces.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        summary
            .interface_positions
            .try_reserve(checked_interfaces.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        summary
            .interface_names
            .try_reserve(checked_interfaces.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        for (interface, checked) in resolved.interfaces.iter().zip(checked_interfaces) {
            if interface.id != checked.id
                || interface.spelling != checked.spelling
                || interface.methods.len() != checked.methods.len()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            if !interface.public {
                summary.withheld.insert(
                    (interface.spelling.clone(), WithheldNamespace::Nominal),
                    WithheldExport {
                        kind: WithheldExportKind::Private,
                        origin: Some(interface.origin.clone()),
                    },
                );
                for method in &interface.methods {
                    summary.withheld.insert(
                        (method.spelling.clone(), WithheldNamespace::Term),
                        WithheldExport {
                            kind: WithheldExportKind::Private,
                            origin: Some(method.origin.clone()),
                        },
                    );
                }
                continue;
            }

            summary
                .method_names
                .try_reserve(interface.methods.len())
                .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
            for (method, checked_method) in interface.methods.iter().zip(&checked.methods) {
                if method.id != checked_method.id || method.spelling != checked_method.spelling {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                if summary
                    .method_names
                    .insert(method.spelling.clone(), method.id)
                    .is_some()
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            }
            let fact = clone_checked_interface_fact(checked, type_work, constraint_work)?;
            let position = summary.interfaces.len();
            if summary
                .interface_names
                .insert(interface.spelling.clone(), interface.id)
                .is_some()
                || summary
                    .interface_positions
                    .insert(interface.id, position)
                    .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.interfaces.push(fact);
        }

        summary
            .implementations
            .try_reserve(checked_implementations.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
        summary
            .implementation_positions
            .try_reserve(checked_implementations.len())
            .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
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
            let position = summary.implementations.len();
            if summary
                .implementation_positions
                .insert(implementation.id, position)
                .is_some()
            {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            summary.implementations.push(fact);
        }

        constraint_work
            .charge(
                summary
                    .terms
                    .len()
                    .saturating_add(summary.implementations.len()),
            )
            .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
        let interface_reference_count = summary
            .terms
            .values()
            .map(|exported| exported.scheme.requirements.len())
            .chain(
                summary
                    .implementations
                    .iter()
                    .map(|implementation| implementation.prerequisites.len().saturating_add(1)),
            )
            .fold(0usize, usize::saturating_add);
        if interface_reference_count > 0 {
            constraint_work
                .charge(
                    interface_reference_count
                        .saturating_add(summary.terms.len())
                        .saturating_add(checked_globals.len()),
                )
                .map_err(|()| ResolvedBuildFailure::ConstraintResource)?;
            let mut exported_binders = HashSet::new();
            exported_binders
                .try_reserve(summary.terms.len())
                .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
            exported_binders.extend(summary.terms.values().map(|exported| exported.binder));
            let mut referenced_interfaces = HashSet::new();
            referenced_interfaces
                .try_reserve(interface_reference_count)
                .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
            let mut referenced_interface_order = Vec::new();
            referenced_interface_order
                .try_reserve(interface_reference_count)
                .map_err(|_| ResolvedBuildFailure::ConstraintResource)?;
            for checked in checked_globals {
                if !exported_binders.contains(&checked.binder) {
                    continue;
                }
                for requirement in &checked.scheme.requirements {
                    if referenced_interfaces.insert(requirement.interface) {
                        referenced_interface_order.push(requirement.interface);
                    }
                }
            }
            for implementation in &summary.implementations {
                if referenced_interfaces.insert(implementation.interface) {
                    referenced_interface_order.push(implementation.interface);
                }
                for prerequisite in &implementation.prerequisites {
                    if referenced_interfaces.insert(prerequisite.interface) {
                        referenced_interface_order.push(prerequisite.interface);
                    }
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
                if summary.interface_positions.contains_key(&interface) {
                    continue;
                }
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

        for (spelling, candidate) in &resolved.export_candidate.nominals {
            let parameters = resolved
                .registry
                .nominal_parameters(candidate.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            let parameter_count = parameters.len();
            let access = match candidate.visibility {
                SurfaceTypeVisibility::PublicOpaque => ExportedTypeAccess::Opaque,
                SurfaceTypeVisibility::PublicTransparent => ExportedTypeAccess::Transparent,
                SurfaceTypeVisibility::Private => {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
            };
            summary
                .nominal_names_by_id
                .insert(candidate.id, spelling.clone());
            summary.nominals.insert(
                spelling.clone(),
                ExportedType {
                    id: candidate.id,
                    parameter_count,
                    parameters: parameters.to_vec().into_boxed_slice(),
                    constructors: if access == ExportedTypeAccess::Transparent {
                        resolved
                            .registry
                            .nominal(candidate.id)
                            .ok_or(ResolvedBuildFailure::InvalidState)?
                            .constructors
                            .clone()
                    } else {
                        Vec::new().into_boxed_slice()
                    },
                    access,
                    origin: candidate.origin.clone(),
                },
            );
        }

        for (spelling, candidate) in &resolved.export_candidate.constructors {
            let constructor = resolved
                .registry
                .constructor(candidate.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?;
            summary
                .constructor_names_by_id
                .insert(candidate.id, spelling.clone());
            summary.constructors.insert(
                spelling.clone(),
                ExportedConstructor {
                    id: candidate.id,
                    spelling: constructor.spelling.clone(),
                    payload: constructor
                        .payload
                        .as_ref()
                        .map(|payload| clone_type_with_budget(payload, type_work))
                        .transpose()
                        .map_err(|()| ResolvedBuildFailure::TypeResource)?,
                    origin: candidate.origin.clone(),
                },
            );
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
                &implementation.argument,
                &mut referenced_nominals,
                type_work,
            )
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            for prerequisite in &implementation.prerequisites {
                collect_nominal_identities(
                    &prerequisite.argument,
                    &mut referenced_nominals,
                    type_work,
                )
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            }
            for method in &implementation.methods {
                collect_scheme_nominal_identities(
                    &method.scheme,
                    &mut referenced_nominals,
                    type_work,
                )
                .map_err(|()| ResolvedBuildFailure::TypeResource)?;
            }
        }

        for candidate in resolved.export_candidate.hidden_nominals.values() {
            if !referenced_nominals.contains(&candidate.id) {
                continue;
            }
            let parameters = resolved
                .registry
                .nominal_parameters(candidate.id)
                .ok_or(ResolvedBuildFailure::InvalidState)?
                .to_vec()
                .into_boxed_slice();
            summary.hidden_nominals.insert(
                candidate.id,
                ExportedHiddenType {
                    id: candidate.id,
                    parameter_count: candidate.parameter_count,
                    parameters,
                    spelling: candidate.spelling.clone(),
                    display_is_private: true,
                    origin: candidate.origin.clone(),
                },
            );
        }
        for imported in resolved.imported.nominals.values() {
            if !referenced_nominals.contains(&imported.id)
                || summary.nominal_names_by_id.contains_key(&imported.id)
                || summary.hidden_nominals.contains_key(&imported.id)
            {
                continue;
            }
            summary.hidden_nominals.insert(
                imported.id,
                ExportedHiddenType {
                    id: imported.id,
                    parameter_count: imported.parameter_count,
                    parameters: imported.parameters.to_vec().into_boxed_slice(),
                    spelling: imported
                        .display_spelling
                        .clone()
                        .unwrap_or_else(|| "hidden".to_owned()),
                    display_is_private: imported.display_is_private,
                    origin: imported.origin.clone(),
                },
            );
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

    pub(crate) fn implementations(&self) -> impl Iterator<Item = &CheckedImplementationFact> {
        self.implementations.iter()
    }

    pub(crate) fn interface_names(&self) -> impl Iterator<Item = (&str, InterfaceId)> {
        self.interface_names
            .iter()
            .map(|(spelling, id)| (spelling.as_str(), *id))
    }

    pub(crate) fn method_names(&self) -> impl Iterator<Item = (&str, MethodId)> {
        self.method_names
            .iter()
            .map(|(spelling, id)| (spelling.as_str(), *id))
    }

    pub(crate) fn terms(&self) -> impl Iterator<Item = (&str, &ExportedGlobal)> {
        self.terms
            .iter()
            .map(|(spelling, exported)| (spelling.as_str(), exported))
    }

    pub(crate) fn namespace_entry_count(&self) -> usize {
        self.terms
            .len()
            .saturating_add(self.nominals.len())
            .saturating_add(self.constructors.len())
            .saturating_add(self.interface_names.len())
            .saturating_add(self.method_names.len())
            .saturating_add(self.withheld.len())
    }

    pub(crate) fn withheld_count(&self) -> usize {
        self.withheld.len()
    }

    pub(crate) fn nominals(&self) -> impl Iterator<Item = (&str, &ExportedType)> {
        self.nominals
            .iter()
            .map(|(spelling, exported)| (spelling.as_str(), exported))
    }

    pub(crate) fn constructors(&self) -> impl Iterator<Item = (&str, &ExportedConstructor)> {
        self.constructors
            .iter()
            .map(|(spelling, exported)| (spelling.as_str(), exported))
    }

    pub(crate) fn withheld_export(
        &self,
        namespace: WithheldNamespace,
        spelling: &str,
    ) -> Option<&WithheldExport> {
        self.withheld.get(&(spelling.to_owned(), namespace))
    }

    pub(crate) fn withheld(
        &self,
    ) -> impl Iterator<Item = (WithheldNamespace, &str, &WithheldExport)> {
        self.withheld
            .iter()
            .map(|((spelling, namespace), withheld)| (*namespace, spelling.as_str(), withheld))
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
                parameters: &exported.parameters,
                constructors: &[],
                access: ImportedTypeAccess::Hidden,
                display_spelling: Some(&exported.spelling),
                display_is_private: exported.display_is_private,
                origin: &exported.origin,
            })
    }

    pub(crate) fn constructor_by_id(&self, id: ConstructorId) -> Option<&ExportedConstructor> {
        self.constructors
            .get(self.constructor_names_by_id.get(&id)?)
    }

    #[cfg(test)]
    pub(crate) fn test_fixture(
        module: ModuleId,
        terms: Vec<(&str, BinderId, Type, Origin)>,
        nominals: Vec<(&str, NominalTypeId, ExportedTypeAccess, Origin)>,
        constructors: Vec<(&str, ConstructorId, Option<Type>, Origin)>,
        unavailable: Vec<&str>,
    ) -> Self {
        let nominal_names_by_id = nominals
            .iter()
            .map(|(spelling, id, _, _)| (*id, (*spelling).to_owned()))
            .collect();
        let constructor_names_by_id = constructors
            .iter()
            .map(|(spelling, id, _, _)| (*id, (*spelling).to_owned()))
            .collect();
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
            nominals: nominals
                .into_iter()
                .map(|(spelling, id, access, origin)| {
                    (
                        spelling.to_owned(),
                        ExportedType {
                            id,
                            parameter_count: 0,
                            parameters: Vec::new().into_boxed_slice(),
                            constructors: Vec::new().into_boxed_slice(),
                            access,
                            origin,
                        },
                    )
                })
                .collect(),
            nominal_names_by_id,
            constructors: constructors
                .into_iter()
                .map(|(spelling, id, payload, origin)| {
                    (
                        spelling.to_owned(),
                        ExportedConstructor {
                            id,
                            spelling: spelling.to_owned(),
                            payload,
                            origin,
                        },
                    )
                })
                .collect(),
            constructor_names_by_id,
            interface_names: HashMap::new(),
            method_names: HashMap::new(),
            interfaces: Vec::new(),
            interface_positions: HashMap::new(),
            hidden_interfaces: Vec::new(),
            implementations: Vec::new(),
            implementation_positions: HashMap::new(),
            hidden_nominals: HashMap::new(),
            withheld: unavailable
                .into_iter()
                .flat_map(|spelling| {
                    [
                        WithheldNamespace::Term,
                        WithheldNamespace::Nominal,
                        WithheldNamespace::Constructor,
                    ]
                    .into_iter()
                    .map(move |namespace| {
                        (
                            (spelling.to_owned(), namespace),
                            WithheldExport {
                                kind: WithheldExportKind::Private,
                                origin: None,
                            },
                        )
                    })
                })
                .collect(),
        }
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
        for (spelling, _) in &opaque_constructors {
            summary
                .withheld
                .remove(&(spelling.to_string(), WithheldNamespace::Term));
            summary
                .withheld
                .remove(&(spelling.to_string(), WithheldNamespace::Constructor));
        }
        summary
            .withheld
            .extend(opaque_constructors.into_iter().map(|(spelling, origin)| {
                (
                    (spelling.to_owned(), WithheldNamespace::Constructor),
                    WithheldExport {
                        kind: WithheldExportKind::OpaqueConstructor,
                        origin: Some(origin),
                    },
                )
            }));
        summary
            .hidden_nominals
            .extend(hidden_nominals.into_iter().map(
                |(spelling, id, parameter_count, display_is_private, origin)| {
                    (
                        id,
                        ExportedHiddenType {
                            id,
                            parameter_count,
                            parameters: Vec::new().into_boxed_slice(),
                            spelling: spelling.to_owned(),
                            display_is_private,
                            origin,
                        },
                    )
                },
            ));
        summary
    }
}

fn collect_nominal_identities(
    root: &Type,
    output: &mut HashSet<NominalTypeId>,
    budget: &mut TypeWorkBudget,
) -> Result<(), ()> {
    let mut work = vec![root];
    while let Some(ty) = work.pop() {
        budget.charge(1)?;
        match ty {
            Type::Nominal(id) => {
                output.insert(*id);
            }
            Type::AppliedNominal(id, arguments) => {
                output.insert(*id);
                work.extend(arguments);
            }
            Type::Tuple(elements) => work.extend(elements),
            Type::Function(domain, codomain) => {
                work.push(codomain);
                work.push(domain);
            }
            Type::Forall(_, body) => work.push(body),
            Type::Int | Type::Bool | Type::Unit | Type::Variable(_) | Type::Inference(_) => {}
        }
    }
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

pub(crate) struct ImportedNominalFactRef<'a> {
    pub(crate) id: NominalTypeId,
    pub(crate) parameter_count: usize,
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
        for (_, exported) in self.nominals.drain() {
            for parameter in exported.parameters.into_vec() {
                discard_origin_iteratively(parameter.origin);
            }
            discard_origin_iteratively(exported.origin);
        }
        self.nominal_names_by_id.clear();
        for (_, exported) in self.constructors.drain() {
            if let Some(payload) = exported.payload {
                discard_type_iteratively(payload);
            }
            discard_origin_iteratively(exported.origin);
        }
        self.constructor_names_by_id.clear();
        self.interface_names.clear();
        self.method_names.clear();
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
        for (_, withheld) in self.withheld.drain() {
            if let Some(origin) = withheld.origin {
                discard_origin_iteratively(origin);
            }
        }
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
    abstract_nominal_names: HashMap<NominalTypeId, String>,
}

struct ResolvedConstructorBuffer(Vec<ResolvedConstructor>);

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
            abstract_nominal_names: HashMap::new(),
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
        let mut nominals = self.nominals.to_vec();
        let mut constructors = ResolvedConstructorBuffer(Vec::with_capacity(
            self.constructors
                .len()
                .saturating_add(imported.constructors.len()),
        ));
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
        let mut parameters = self
            .nominal_parameters
            .iter()
            .map(|(owner, parameters)| (*owner, parameters.to_vec()))
            .collect::<Vec<_>>();

        for fact in imported.nominals() {
            if fact.access != ImportedTypeAccess::Transparent {
                continue;
            }
            if fact.parameters.len() != fact.parameter_count
                || nominals.iter().any(|nominal| nominal.id == fact.id)
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
            nominals.push(ResolvedNominalType {
                id: fact.id,
                spelling: fact
                    .display_spelling
                    .clone()
                    .unwrap_or_else(|| "<imported>".to_owned()),
                constructors: fact.constructors.clone(),
                origin: fact.origin.clone(),
            });
            parameters.push((fact.id, fact.parameters.to_vec()));
        }

        let abstract_nominal_names = imported
            .nominals()
            .filter(|fact| fact.access != ImportedTypeAccess::Transparent)
            .map(|fact| {
                let spelling = fact.display_spelling.as_deref().unwrap_or("hidden");
                let display = if fact.display_is_private {
                    format!("<private {spelling}>")
                } else {
                    spelling.to_owned()
                };
                (fact.id, display)
            })
            .collect();
        Ok(Self::new(nominals, constructors.into_vec())
            .with_type_parameters(parameters)
            .with_additional_type_variables(self.type_variables.values().cloned())
            .with_abstract_nominal_names(abstract_nominal_names))
    }

    /// Combines complete defining registries by canonical semantic identity.
    pub(crate) fn combine_checked(
        modules: &[CheckedModule],
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        let mut module_ids = HashSet::new();
        let mut nominal_ids = HashSet::new();
        let mut constructor_ids = HashSet::new();
        let mut type_variable_ids = HashSet::new();
        let mut nominals = Vec::new();
        let mut constructors = ResolvedConstructorBuffer(Vec::new());
        let mut parameters = Vec::new();
        let mut additional_type_variables = Vec::new();

        for checked in modules {
            if !module_ids.insert(checked.module()) {
                return Err(ResolvedBuildFailure::InvalidState);
            }
            let registry = checked.registry();
            for nominal in registry.nominals() {
                if nominal.id.module() != checked.module() || !nominal_ids.insert(nominal.id) {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                nominals.push(nominal.clone());
            }
            for constructor in registry.constructors() {
                if constructor.owner.module() != checked.module()
                    || !constructor_ids.insert(constructor.id)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
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
            for (owner, owner_parameters) in registry.nominal_parameter_entries() {
                if owner.module() != checked.module() {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                parameters.push((owner, owner_parameters.to_vec()));
            }
            for parameter in registry.type_variables.values() {
                if parameter.id.module() != Some(checked.module())
                    || !type_variable_ids.insert(parameter.id)
                {
                    return Err(ResolvedBuildFailure::InvalidState);
                }
                additional_type_variables.push(parameter.clone());
            }
        }

        Ok(Self::new(nominals, constructors.into_vec())
            .with_type_parameters(parameters)
            .with_additional_type_variables(additional_type_variables))
    }

    /// Attaches ordered declaration parameters after nominal identity allocation.
    #[must_use]
    pub fn with_type_parameters(
        mut self,
        parameters: Vec<(NominalTypeId, Vec<ResolvedTypeVariable>)>,
    ) -> Self {
        for (owner, parameters) in parameters {
            for parameter in &parameters {
                self.insert_type_variable(parameter.clone());
            }
            if let Some(replaced) = self
                .nominal_parameters
                .insert(owner, parameters.into_boxed_slice())
            {
                for parameter in replaced.into_vec() {
                    discard_origin_iteratively(parameter.origin);
                }
            }
        }
        self
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

    fn with_abstract_nominal_names(mut self, names: HashMap<NominalTypeId, String>) -> Self {
        self.abstract_nominal_names = names;
        self
    }

    fn insert_type_variable(&mut self, parameter: ResolvedTypeVariable) {
        if let Some(replaced) = self.type_variables.insert(parameter.id, parameter) {
            discard_origin_iteratively(replaced.origin);
        }
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
                Task::Type(Type::AppliedNominal(id, arguments)) => {
                    if let Some(nominal) = self.nominal(*id) {
                        output.push_str(&nominal.spelling);
                    } else if let Some(spelling) = self.abstract_nominal_names.get(id) {
                        output.push_str(spelling);
                    } else {
                        output.push_str(&Type::Nominal(*id).to_string());
                    }
                    output.push('<');
                    work.push(Task::Text(">"));
                    for (index, argument) in arguments.iter().enumerate().rev() {
                        work.push(Task::Type(argument));
                        if index > 0 {
                            work.push(Task::Text(", "));
                        }
                    }
                }
                Task::Type(Type::Forall(parameters, body)) => {
                    output.push_str("forall ");
                    for (index, parameter) in parameters.iter().enumerate() {
                        if index > 0 {
                            output.push_str(", ");
                        }
                        if let Some(variable) = self.type_variable(*parameter) {
                            output.push_str(&variable.spelling);
                        } else {
                            output.push_str(&format!("T{}", parameter.local()));
                        }
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
        self.nominal_positions.clear();
        self.constructor_positions.clear();
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
            for parameter in parameters.into_vec() {
                discard_origin_iteratively(parameter.origin);
            }
        }
        for parameter in type_variables.into_values() {
            discard_origin_iteratively(parameter.origin);
        }
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
    /// A saturated nominal type application and its argument roots.
    Application { span: Span, arguments: Box<[usize]> },
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
    /// Free method-local type candidates retained for Task 4 rejection.
    pub type_parameters: Box<[ResolvedTypeVariable]>,
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

fn discard_resolved_definition_iteratively(definition: ResolvedDefinition) {
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

fn discard_resolved_implementation_iteratively(implementation: ResolvedImplementation) {
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

fn discard_resolved_interface_iteratively(interface: ResolvedInterfaceDeclaration) {
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

fn discard_resolved_requirement(requirement: ResolvedRequirement) {
    discard_origin_iteratively(requirement.interface.origin);
    discard_resolved_type(requirement.argument);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interface::RequirementOwner;
    use crate::module::ModuleId;
    use crate::source::{ByteRange, GeneratedReason, SourceFile};

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
            AvailableImplementation::direct_import(imported_id, ModuleId::new(20), span),
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
            nominals: HashMap::new(),
            nominal_names_by_id: HashMap::new(),
            constructors: HashMap::new(),
            constructor_names_by_id: HashMap::new(),
            interface_names: HashMap::new(),
            method_names: HashMap::new(),
            interfaces: Vec::new(),
            interface_positions: HashMap::new(),
            hidden_interfaces: Vec::new(),
            implementations: Vec::new(),
            implementation_positions: HashMap::new(),
            hidden_nominals: HashMap::new(),
            withheld: HashMap::new(),
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

        let group = checked.into_group();
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
                    origin: Origin::Source(interface_span),
                },
                methods: vec![CheckedInterfaceMethodFact {
                    id: method,
                    spelling: "render".into(),
                    value_type: Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                    origin: Origin::Source(interface_span),
                    span: interface_span,
                }]
                .into_boxed_slice(),
                origin: Origin::Source(interface_span),
                span: interface_span,
            },
            base,
            interface_span,
            true,
        );
        let mut export_candidate = ResolvedExportCandidate::default();
        export_candidate.insert_term(
            "apply".into(),
            CandidateGlobal {
                binder,
                origin: Origin::Source(global_span),
            },
        );
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
        let (short, short_used) = freeze_hidden_interface_summary_with_limit(12);
        assert_eq!(short, Err(ResolvedBuildFailure::ConstraintResource));
        assert_eq!(short_used, 12);

        let (exact, exact_used) = freeze_hidden_interface_summary_with_limit(13);
        let summary = exact.expect("the exact budget should retain one hidden interface fact");
        assert_eq!(exact_used, 13);
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
                    origin: Origin::Source(hidden_span),
                },
                methods: Box::new([]),
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
                    origin: Origin::Source(first),
                },
                methods: Box::new([]),
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
                    module,
                    span,
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
                    for index in 0..5_000 {
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
                                origin,
                            },
                            ResolvedTypeVariable {
                                id: parameter,
                                spelling: "B".into(),
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
}
