//! Name-resolved, source-spanned syntax passed to typed elaboration.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::{
    integer::Integer,
    module::ModuleId,
    source::{Origin, Span, discard_origin_iteratively},
    surface::SurfaceTypeVisibility,
    types::{
        ConstructorId, NominalTypeId, Type, TypeVariableId, TypeWorkBudget, clone_type_with_budget,
        discard_type_iteratively,
    },
};

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
    /// Identity of the definition selected by lexical scope.
    pub binder: BinderId,
    /// Exact source spelling at this occurrence.
    pub spelling: String,
    /// Causal source provenance for the occurrence site.
    pub origin: Origin,
}

/// One resolved Mini-Ash source file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedProgram {
    /// Immutable nominal and constructor registry.
    pub registry: Arc<ResolvedRegistry>,
    /// Resolved global definitions in source order.
    pub definitions: Vec<ResolvedDefinition>,
    /// Required final result expression.
    pub result: ResolvedExpr,
    /// Complete accepted source span.
    pub span: Span,
}

/// One declarations-only module after name resolution.
#[derive(Debug, Eq, PartialEq)]
pub struct ResolvedModule {
    module: ModuleId,
    registry: Arc<ResolvedRegistry>,
    imported: ImportedFacts,
    definitions: Box<[ResolvedDefinition]>,
    export_candidate: ResolvedExportCandidate,
    span: Span,
}

impl ResolvedModule {
    pub(crate) fn new(
        module: ModuleId,
        registry: Arc<ResolvedRegistry>,
        imported: ImportedFacts,
        definitions: Vec<ResolvedDefinition>,
        export_candidate: ResolvedExportCandidate,
        span: Span,
    ) -> Self {
        Self {
            module,
            registry,
            imported,
            definitions: definitions.into_boxed_slice(),
            export_candidate,
            span,
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

    /// Returns local definitions in source order.
    #[must_use]
    pub fn definitions(&self) -> &[ResolvedDefinition] {
        &self.definitions
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

/// One fully checked local global scheme retained for linking and exports.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedGlobalScheme {
    /// Stable binder identity.
    pub binder: BinderId,
    /// Source declaration spelling.
    pub spelling: String,
    /// Closed, inference-free rank-1 scheme.
    pub scheme: Type,
    /// Causal declaration provenance.
    pub origin: Origin,
}

/// One successfully checked declarations-only module.
#[derive(Debug)]
pub struct CheckedModule {
    module: ModuleId,
    registry: Arc<ResolvedRegistry>,
    definitions: Box<[ResolvedDefinition]>,
    schemes: Vec<CheckedGlobalScheme>,
    exports: ExportSummary,
    span: Span,
}

impl CheckedModule {
    pub(crate) fn new(
        resolved: ResolvedModule,
        schemes: Vec<CheckedGlobalScheme>,
        exports: ExportSummary,
    ) -> Self {
        Self {
            module: resolved.module,
            registry: resolved.registry,
            definitions: resolved.definitions,
            schemes,
            exports,
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

    /// Returns local definitions in source order.
    #[must_use]
    pub fn definitions(&self) -> &[ResolvedDefinition] {
        &self.definitions
    }

    /// Returns checked local schemes in definition order.
    #[must_use]
    pub fn schemes(&self) -> &[CheckedGlobalScheme] {
        &self.schemes
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
            definitions: std::mem::take(&mut self.definitions),
            schemes: std::mem::take(&mut self.schemes).into_boxed_slice(),
            span: self.span,
        }
    }
}

impl Drop for CheckedModule {
    fn drop(&mut self) {
        for checked in self.schemes.drain(..) {
            discard_type_iteratively(checked.scheme);
            discard_origin_iteratively(checked.origin);
        }
    }
}

/// One checked module-local recursive group retained for final lowering.
#[derive(Debug)]
pub struct ResolvedModuleGroup {
    /// Stable canonical module identity.
    pub module: ModuleId,
    /// Checked local definitions in source order.
    pub definitions: Box<[ResolvedDefinition]>,
    /// Checked schemes in the same definition order.
    pub schemes: Box<[CheckedGlobalScheme]>,
    /// Complete defining source span.
    pub span: Span,
}

impl Drop for ResolvedModuleGroup {
    fn drop(&mut self) {
        for checked in std::mem::take(&mut self.schemes).into_vec() {
            discard_type_iteratively(checked.scheme);
            discard_origin_iteratively(checked.origin);
        }
    }
}

/// Dependency-ordered checked modules ready for one final Core lowering.
#[derive(Debug)]
pub struct ResolvedModuleProgram {
    /// Combined full defining registries from every checked module.
    pub registry: Arc<ResolvedRegistry>,
    /// Dependency-ordered ordinary recursive groups.
    pub groups: Box<[ResolvedModuleGroup]>,
    /// Stable entry module identity.
    pub entry: ModuleId,
    /// Generated entry result expression.
    pub result: ResolvedExpr,
}

/// Body-free dependency facts retained by one resolved module.
#[derive(Debug, Default, Eq, PartialEq)]
pub struct ImportedFacts {
    globals: HashMap<BinderId, ImportedGlobalScheme>,
    nominals: HashMap<NominalTypeId, ImportedNominalFact>,
    constructors: HashMap<ConstructorId, ImportedConstructorFact>,
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

    pub(crate) fn globals(&self) -> impl Iterator<Item = &ImportedGlobalScheme> {
        self.globals.values()
    }

    pub(crate) fn nominals(&self) -> impl Iterator<Item = &ImportedNominalFact> {
        self.nominals.values()
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
}

impl Drop for ImportedFacts {
    fn drop(&mut self) {
        for (_, fact) in self.globals.drain() {
            discard_type_iteratively(fact.scheme);
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
    }
}

/// One imported checked global scheme.
#[derive(Debug, Eq, PartialEq)]
pub struct ImportedGlobalScheme {
    /// Stable defining binder identity.
    pub binder: BinderId,
    /// Fully zonked closed rank-1 scheme.
    pub scheme: Type,
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
    /// Causal declaration provenance.
    pub origin: Origin,
}

impl ImportedNominalFact {
    /// Renders a diagnostic-only name without creating a resolver binding.
    #[must_use]
    pub fn display_name(&self, module_label: &str) -> String {
        match (self.access, self.display_spelling.as_deref()) {
            (ImportedTypeAccess::Hidden, Some(spelling)) => {
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
    /// Display-only private spelling.
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
    /// Fully zonked closed rank-1 scheme.
    pub scheme: Type,
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
    hidden_nominals: HashMap<NominalTypeId, ExportedHiddenType>,
    withheld: HashMap<(String, WithheldNamespace), WithheldExport>,
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
    /// Display-only private spelling.
    pub spelling: String,
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
        checked: &[CheckedGlobalScheme],
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, ()> {
        budget.charge(checked.len())?;
        let mut checked_by_binder = HashMap::new();
        checked_by_binder
            .try_reserve(checked.len())
            .map_err(|_| ())?;
        for scheme in checked {
            if checked_by_binder.insert(scheme.binder, scheme).is_some() {
                return Err(());
            }
        }
        let mut summary = Self {
            module: resolved.module,
            terms: HashMap::new(),
            nominals: HashMap::new(),
            nominal_names_by_id: HashMap::new(),
            constructors: HashMap::new(),
            constructor_names_by_id: HashMap::new(),
            hidden_nominals: HashMap::new(),
            withheld: resolved.export_candidate.withheld.clone(),
        };
        for (spelling, candidate) in &resolved.export_candidate.terms {
            let scheme = checked_by_binder.get(&candidate.binder).ok_or(())?;
            summary.terms.insert(
                spelling.clone(),
                ExportedGlobal {
                    binder: scheme.binder,
                    scheme: clone_type_with_budget(&scheme.scheme, budget)?,
                    origin: scheme.origin.clone(),
                },
            );
        }

        for (spelling, candidate) in &resolved.export_candidate.nominals {
            let parameters = resolved
                .registry
                .nominal_parameters(candidate.id)
                .ok_or(())?;
            let parameter_count = parameters.len();
            let access = match candidate.visibility {
                SurfaceTypeVisibility::PublicOpaque => ExportedTypeAccess::Opaque,
                SurfaceTypeVisibility::PublicTransparent => ExportedTypeAccess::Transparent,
                SurfaceTypeVisibility::Private => return Err(()),
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
                            .ok_or(())?
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
            let constructor = resolved.registry.constructor(candidate.id).ok_or(())?;
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
                        .map(|payload| clone_type_with_budget(payload, budget))
                        .transpose()?,
                    origin: candidate.origin.clone(),
                },
            );
        }

        let mut referenced_nominals = HashSet::new();
        for exported in summary.terms.values() {
            collect_nominal_identities(&exported.scheme, &mut referenced_nominals, budget)?;
        }
        for exported in summary.constructors.values() {
            if let Some(payload) = &exported.payload {
                collect_nominal_identities(payload, &mut referenced_nominals, budget)?;
            }
        }

        for candidate in resolved.export_candidate.hidden_nominals.values() {
            if !referenced_nominals.contains(&candidate.id) {
                continue;
            }
            let parameters = resolved
                .registry
                .nominal_parameters(candidate.id)
                .ok_or(())?
                .to_vec()
                .into_boxed_slice();
            summary.hidden_nominals.insert(
                candidate.id,
                ExportedHiddenType {
                    id: candidate.id,
                    parameter_count: candidate.parameter_count,
                    parameters,
                    spelling: candidate.spelling.clone(),
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

    pub(crate) fn terms(&self) -> impl Iterator<Item = (&str, &ExportedGlobal)> {
        self.terms
            .iter()
            .map(|(spelling, exported)| (spelling.as_str(), exported))
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
                            scheme,
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
        hidden_nominals: Vec<(&str, NominalTypeId, usize, Origin)>,
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
            .extend(
                hidden_nominals
                    .into_iter()
                    .map(|(spelling, id, parameter_count, origin)| {
                        (
                            id,
                            ExportedHiddenType {
                                id,
                                parameter_count,
                                parameters: Vec::new().into_boxed_slice(),
                                spelling: spelling.to_owned(),
                                origin,
                            },
                        )
                    }),
            );
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

pub(crate) struct ImportedNominalFactRef<'a> {
    pub(crate) id: NominalTypeId,
    pub(crate) parameter_count: usize,
    pub(crate) parameters: &'a [ResolvedTypeVariable],
    pub(crate) constructors: &'a [ConstructorId],
    pub(crate) access: ImportedTypeAccess,
    pub(crate) display_spelling: Option<&'a str>,
    pub(crate) origin: &'a Origin,
}

impl Drop for ExportSummary {
    fn drop(&mut self) {
        for (_, exported) in self.terms.drain() {
            discard_type_iteratively(exported.scheme);
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
    ) -> Result<Self, ()> {
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
                    .transpose()?,
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
                return Err(());
            }
            for id in &fact.constructors {
                let constructor = imported.constructor(*id).ok_or(())?;
                if constructor.id.owner() != fact.id {
                    return Err(());
                }
                constructors.0.push(ResolvedConstructor {
                    id: constructor.id,
                    owner: fact.id,
                    spelling: constructor.spelling.clone(),
                    payload: constructor
                        .payload
                        .as_ref()
                        .map(|payload| clone_type_with_budget(payload, budget))
                        .transpose()?,
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
                let display = if fact.access == ImportedTypeAccess::Hidden {
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
    ) -> Result<Self, ()> {
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
                return Err(());
            }
            let registry = checked.registry();
            for nominal in registry.nominals() {
                if nominal.id.module() != checked.module() || !nominal_ids.insert(nominal.id) {
                    return Err(());
                }
                nominals.push(nominal.clone());
            }
            for constructor in registry.constructors() {
                if constructor.owner.module() != checked.module()
                    || !constructor_ids.insert(constructor.id)
                {
                    return Err(());
                }
                constructors.0.push(ResolvedConstructor {
                    id: constructor.id,
                    owner: constructor.owner,
                    spelling: constructor.spelling.clone(),
                    payload: constructor
                        .payload
                        .as_ref()
                        .map(|payload| clone_type_with_budget(payload, budget))
                        .transpose()?,
                    origin: constructor.origin.clone(),
                });
            }
            for (owner, owner_parameters) in registry.nominal_parameter_entries() {
                if owner.module() != checked.module() {
                    return Err(());
                }
                parameters.push((owner, owner_parameters.to_vec()));
            }
            for parameter in registry.type_variables.values() {
                if parameter.id.module() != Some(checked.module())
                    || !type_variable_ids.insert(parameter.id)
                {
                    return Err(());
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
    /// Implicit outer type binders in first-occurrence order.
    pub type_parameters: Box<[ResolvedTypeVariable]>,
    /// Complete interface span.
    pub span: Span,
}

/// A resolved equation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedEquation {
    /// Repeated global name in the equation head.
    pub name: ResolvedOccurrence,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::ModuleId;
    use crate::source::{ByteRange, GeneratedReason, SourceFile};

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
