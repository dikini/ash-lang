//! Lexical name resolution for recovery-free surface syntax.

use std::{
    collections::{HashMap, HashSet},
    fmt,
    ops::{Deref, Range},
    sync::Arc,
};

use crate::{
    diagnostic::{Diagnostic, SourceLabel},
    interface::{
        EvidenceSlot, ImplId, ImplMethodId, InterfaceId, MethodId, RequirementId, RequirementOwner,
    },
    module::{LoadedModule, ModuleDependency, ModuleId},
    resolved::{
        Binder, BinderId, CandidateConstructor, CandidateGlobal, CandidateHiddenNominal,
        CandidateNominal, ExportSummary, ExportedConstructor, ExportedGlobal, ExportedType,
        ImportedConstructorFact, ImportedFacts, ImportedGlobalScheme, ImportedNominalFact,
        ImportedTypeAccess, ResolvedApplicationExpr, ResolvedBinaryExpr, ResolvedBinding,
        ResolvedBlock, ResolvedConstructor, ResolvedConstructorOccurrence, ResolvedDefinition,
        ResolvedDefinitionKind, ResolvedEquation, ResolvedEquationalGlobal,
        ResolvedExportCandidate, ResolvedExpr, ResolvedExprKind, ResolvedExternalInterface,
        ResolvedFunctionExpr, ResolvedImplementation, ResolvedImplementationMethodGroup,
        ResolvedInlineOperationalGlobal, ResolvedInlineOperationalHeader,
        ResolvedInterfaceDeclaration, ResolvedInterfaceMethod, ResolvedInterfaceOccurrence,
        ResolvedLocalDeclaration, ResolvedMatchArm, ResolvedMatchExpr, ResolvedModule,
        ResolvedModuleParts, ResolvedNominalType, ResolvedOccurrence, ResolvedPattern,
        ResolvedPatternKind, ResolvedRecursiveGroup, ResolvedRecursiveMember, ResolvedRegistry,
        ResolvedRequirement, ResolvedTermName, ResolvedType, ResolvedTypeProvenance,
        ResolvedTypeProvenanceNode, ResolvedTypeVariable, ResolvedTypedPattern, WithheldExport,
        WithheldExportKind, WithheldNamespace,
    },
    source::Origin,
    surface::{
        BinaryExpr, SurfaceBinding, SurfaceBlock, SurfaceDeclarationIndex, SurfaceDefinition,
        SurfaceDefinitionKind, SurfaceExpr, SurfaceExprKind, SurfaceImplementation,
        SurfaceImportSelection, SurfaceInterfaceDeclaration, SurfaceLocalDeclaration,
        SurfaceModule, SurfacePattern, SurfacePatternKind, SurfaceRecursiveGroup, SurfaceReference,
        SurfaceRequirement, SurfaceType, SurfaceTypeDeclaration, SurfaceTypeKind,
        SurfaceTypeVisibility,
    },
    types::{
        ConstructorId, NominalTypeId, Type, TypeVariableId, TypeWorkBudget, charge_type_cells,
        clone_type_with_budget,
    },
};

/// The semantic reason that prevented name resolution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResolveReason {
    /// An occurrence has no binding in lexical scope.
    UnknownName,
    /// The equation head repeats a different name from its interface.
    EquationNameMismatch,
    /// A file contains a second global with the same spelling.
    DuplicateGlobal,
    /// A file contains a second nominal type spelling.
    DuplicateType,
    /// A file contains a second constructor spelling.
    DuplicateConstructor,
    /// Two complete imports bind the same module alias.
    DuplicateModuleAlias,
    /// An imported spelling is private or otherwise unavailable.
    UnavailableExport,
    /// An import binding conflicts with another file-wide binding.
    ImportConflict,
    /// A source occurrence attempts to inspect an opaque constructor.
    OpaqueConstructor,
    /// A declaration repeats one type-parameter spelling.
    DuplicateTypeParameter,
    /// A source type occurrence names no declaration.
    UnknownType,
    /// A nominal type constructor has the wrong number of arguments.
    TypeArgumentCount,
    /// A type of kind `Type` was used as a type constructor.
    TypeKind,
    /// An interface position names no interface declaration.
    UnknownInterface,
    /// A nominal type or type parameter was used as an interface.
    InterfaceKind,
    /// An uppercase term or pattern names no constructor.
    UnknownConstructor,
    /// One pattern vector binds the same spelling more than once.
    DuplicatePatternBinder,
    /// A recursive group contains a second member with the same spelling.
    DuplicateRecursiveMember,
    /// The resolver cannot assign another distinct binder identity.
    BinderIdExhausted,
    /// Cumulative source-type resolution exceeded the compiler work budget.
    TypeResourceExhausted,
    /// An internal resolver invariant was lost.
    InternalState,
}

impl fmt::Display for ResolveReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::UnknownName => "resolve.unknown-name",
            Self::EquationNameMismatch => "resolve.equation-name-mismatch",
            Self::DuplicateGlobal => "resolve.duplicate-global",
            Self::DuplicateType => "resolve.duplicate-type",
            Self::DuplicateConstructor => "resolve.duplicate-constructor",
            Self::DuplicateModuleAlias => "resolve.duplicate-module-alias",
            Self::UnavailableExport => "resolve.unavailable-export",
            Self::ImportConflict => "resolve.import-conflict",
            Self::OpaqueConstructor => "resolve.opaque-constructor",
            Self::DuplicateTypeParameter => "resolve.duplicate-type-parameter",
            Self::UnknownType => "resolve.unknown-type",
            Self::TypeArgumentCount => "resolve.type-argument-count",
            Self::TypeKind => "resolve.type-kind",
            Self::UnknownInterface => "resolve.unknown-interface",
            Self::InterfaceKind => "resolve.interface-kind",
            Self::UnknownConstructor => "resolve.unknown-constructor",
            Self::DuplicatePatternBinder => "pattern.duplicate-binder",
            Self::DuplicateRecursiveMember => "resolve.duplicate-recursive-member",
            Self::BinderIdExhausted => "resolve.binder-id-exhausted",
            Self::TypeResourceExhausted => "resolve.type-resource",
            Self::InternalState => "resolve.internal-state",
        })
    }
}

/// A structured name-resolution failure kept compact in pipeline results.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveError(Box<Diagnostic<ResolveReason>>);

impl ResolveError {
    /// Returns the phase-owned structured diagnostic.
    #[must_use]
    pub fn diagnostic(&self) -> &Diagnostic<ResolveReason> {
        &self.0
    }

    /// Consumes the failure and returns its structured diagnostic.
    #[must_use]
    pub fn into_diagnostic(self) -> Diagnostic<ResolveReason> {
        *self.0
    }
}

impl From<Diagnostic<ResolveReason>> for ResolveError {
    fn from(diagnostic: Diagnostic<ResolveReason>) -> Self {
        Self(Box::new(diagnostic))
    }
}

impl Deref for ResolveError {
    type Target = Diagnostic<ResolveReason>;

    fn deref(&self) -> &Self::Target {
        self.diagnostic()
    }
}

impl fmt::Display for ResolveError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0.render_plain())
    }
}

impl std::error::Error for ResolveError {}

/// One source import edge paired with its checked dependency summary.
#[derive(Clone, Copy, Debug)]
pub struct DependencyExports<'a> {
    edge: &'a ModuleDependency,
    summary: &'a ExportSummary,
}

impl<'a> DependencyExports<'a> {
    /// Authenticates a dependency edge and summary pair.
    ///
    /// # Errors
    ///
    /// Returns [`DependencyExportMismatch`] when the summary belongs to a
    /// different canonical module.
    pub fn new(
        edge: &'a ModuleDependency,
        summary: &'a ExportSummary,
    ) -> Result<Self, DependencyExportMismatch> {
        if edge.target() != summary.module() {
            return Err(DependencyExportMismatch);
        }
        Ok(Self { edge, summary })
    }
}

/// A dependency edge was paired with another module's summary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DependencyExportMismatch;

impl fmt::Display for DependencyExportMismatch {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("dependency export summary does not match its module edge")
    }
}

impl std::error::Error for DependencyExportMismatch {}

/// Resolves one declarations-only module from checked dependency summaries.
///
/// # Errors
///
/// Returns a structured resolution failure for invalid import scopes, local
/// declarations, or source occurrences.
pub fn resolve_module(
    loaded: &LoadedModule,
    dependencies: &[DependencyExports<'_>],
) -> Result<ResolvedModule, ResolveError> {
    let mut type_work = TypeWorkBudget::default();
    resolve_module_with_budget(loaded, dependencies, &mut type_work)
}

/// Resolves one module while sharing type-work accounting across a graph pass.
pub(crate) fn resolve_module_with_budget(
    loaded: &LoadedModule,
    dependencies: &[DependencyExports<'_>],
    type_work: &mut TypeWorkBudget,
) -> Result<ResolvedModule, ResolveError> {
    let module = loaded.id();
    let surface = loaded.surface();
    reject_duplicate_module_aliases(surface)?;
    if dependencies.len() != loaded.dependencies().len()
        || surface.imports.len() != loaded.dependencies().len()
        || dependencies
            .iter()
            .zip(loaded.dependencies())
            .zip(&surface.imports)
            .any(|((dependency, loaded_edge), import)| {
                dependency.edge != loaded_edge
                    || loaded_edge.import_span() != import.span
                    || dependency.edge.target() != dependency.summary.module()
            })
    {
        return Err(error(
            ResolveReason::InternalState,
            surface.span,
            "the resolver received incomplete or mismatched dependency summaries",
        ));
    }

    let mut resolver = Resolver::with_type_work(module, std::mem::take(type_work));
    let result = (|| {
        resolver.install_imports(surface, dependencies)?;
        resolver.validate_local_namespaces(surface)?;
        let ResolvedDeclarations {
            registry,
            interfaces,
            implementations,
            definitions,
        } = resolver.resolve_declarations(surface)?;
        let imported = std::mem::take(&mut resolver.imported);
        let export_candidate = build_export_candidate(surface, &registry, &definitions)?;
        let declaration_order = surface
            .declaration_order
            .iter()
            .copied()
            .map(|declaration| match declaration {
                SurfaceDeclarationIndex::Type(index) => {
                    crate::resolved::ResolvedDeclarationIndex::Type(index)
                }
                SurfaceDeclarationIndex::Interface(index) => {
                    crate::resolved::ResolvedDeclarationIndex::Interface(index)
                }
                SurfaceDeclarationIndex::Global(index) => {
                    crate::resolved::ResolvedDeclarationIndex::Global(index)
                }
                SurfaceDeclarationIndex::Implementation(index) => {
                    crate::resolved::ResolvedDeclarationIndex::Implementation(index)
                }
            })
            .collect();
        Ok(ResolvedModule::new(ResolvedModuleParts {
            module,
            registry,
            imported,
            declaration_order,
            interfaces,
            implementations,
            definitions,
            export_candidate,
            span: surface.span,
        }))
    })();
    *type_work = std::mem::take(&mut resolver.type_work);
    result
}

fn reject_duplicate_module_aliases(surface: &SurfaceModule) -> Result<(), ResolveError> {
    let mut aliases = HashMap::new();
    for import in &surface.imports {
        let SurfaceImportSelection::Qualified { alias } = &import.selection else {
            continue;
        };
        if let Some(first) = aliases.insert(alias.text.as_str(), alias.span) {
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateModuleAlias,
                SourceLabel::new(alias.span, "this module alias is already bound"),
            );
            diagnostic
                .related
                .push(SourceLabel::new(first, "the first module alias is here"));
            diagnostic.found = Some(alias.text.clone());
            return Err(diagnostic.into());
        }
    }
    Ok(())
}

fn build_export_candidate(
    surface: &SurfaceModule,
    registry: &ResolvedRegistry,
    definitions: &[ResolvedDefinition],
) -> Result<ResolvedExportCandidate, ResolveError> {
    let mut candidate = ResolvedExportCandidate::default();
    for (source, resolved) in surface.definitions.iter().zip(definitions) {
        if !source.public {
            let binder = definition_binder(resolved);
            candidate.insert_withheld(
                WithheldNamespace::Term,
                binder.spelling.clone(),
                WithheldExport {
                    kind: WithheldExportKind::Private,
                    origin: Some(binder.origin.clone()),
                },
            );
            continue;
        }
        let binder = definition_binder(resolved);
        candidate.insert_term(
            binder.spelling.clone(),
            CandidateGlobal {
                binder: binder.id,
                origin: binder.origin.clone(),
            },
        );
    }

    for (source, resolved) in surface.type_declarations.iter().zip(registry.nominals()) {
        if source.visibility == SurfaceTypeVisibility::Private {
            candidate.insert_hidden_nominal(CandidateHiddenNominal {
                id: resolved.id,
                parameter_count: source.parameters.len(),
                spelling: source.name.text.clone(),
                origin: resolved.origin.clone(),
            });
            candidate.insert_withheld(
                WithheldNamespace::Nominal,
                source.name.text.clone(),
                WithheldExport {
                    kind: WithheldExportKind::Private,
                    origin: Some(resolved.origin.clone()),
                },
            );
            for (constructor, id) in source.constructors.iter().zip(&resolved.constructors) {
                let resolved_constructor = registry.constructor(*id).ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        constructor.span,
                        "the resolver lost a private constructor",
                    )
                })?;
                candidate.insert_withheld(
                    WithheldNamespace::Constructor,
                    constructor.name.text.clone(),
                    WithheldExport {
                        kind: WithheldExportKind::Private,
                        origin: Some(resolved_constructor.origin.clone()),
                    },
                );
            }
            continue;
        }
        candidate.insert_nominal(
            source.name.text.clone(),
            CandidateNominal {
                id: resolved.id,
                visibility: source.visibility,
                origin: resolved.origin.clone(),
            },
        );
        if source.visibility != SurfaceTypeVisibility::PublicTransparent {
            for (constructor, id) in source.constructors.iter().zip(&resolved.constructors) {
                let resolved_constructor = registry.constructor(*id).ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        constructor.span,
                        "the resolver lost an opaque constructor",
                    )
                })?;
                candidate.insert_withheld(
                    WithheldNamespace::Constructor,
                    constructor.name.text.clone(),
                    WithheldExport {
                        kind: WithheldExportKind::OpaqueConstructor,
                        origin: Some(resolved_constructor.origin.clone()),
                    },
                );
            }
            continue;
        }
        for (constructor, id) in source.constructors.iter().zip(&resolved.constructors) {
            let resolved_constructor = registry.constructor(*id).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    constructor.span,
                    "the resolver lost a public constructor",
                )
            })?;
            candidate.insert_constructor(
                constructor.name.text.clone(),
                CandidateConstructor {
                    id: *id,
                    origin: resolved_constructor.origin.clone(),
                },
            );
        }
    }
    Ok(candidate)
}

fn definition_binder(definition: &ResolvedDefinition) -> &Binder {
    match &definition.kind {
        ResolvedDefinitionKind::Equational(global) => &global.interface.name,
        ResolvedDefinitionKind::InlineOperational(global) => &global.header.name,
    }
}

fn surface_definition_name(definition: &SurfaceDefinition) -> &crate::surface::SurfaceName {
    match &definition.kind {
        SurfaceDefinitionKind::Equational(global) => &global.interface.name,
        SurfaceDefinitionKind::InlineOperational(global) => &global.header.name,
    }
}

struct Resolver {
    module: ModuleId,
    next_binder: u32,
    next_type_variable: u32,
    scopes: Vec<HashMap<String, Binder>>,
    globals: HashMap<String, GlobalFact>,
    type_names: HashMap<String, NominalTypeId>,
    interface_names: HashMap<String, InterfaceId>,
    method_names: HashMap<String, MethodId>,
    global_requirement_counts: HashMap<BinderId, usize>,
    constructor_names: HashMap<String, ConstructorId>,
    module_aliases: HashMap<String, ImportedNamespaces>,
    targeted_withheld: HashMap<(String, WithheldNamespace), WithheldImport>,
    imported: ImportedFacts,
    type_scopes: Vec<HashMap<String, ResolvedTypeVariable>>,
    nominal_parameter_counts: HashMap<NominalTypeId, usize>,
    type_work: TypeWorkBudget,
    #[cfg(test)]
    max_type_pending_tasks: usize,
}

struct GlobalFact {
    name_span: crate::source::Span,
    definition_span: crate::source::Span,
}

struct PendingImplementation {
    id: ImplId,
    head_parameters: Vec<ResolvedTypeVariable>,
    prerequisite_only_parameters: Vec<ResolvedTypeVariable>,
    method_groups: Vec<PendingImplementationMethodGroup>,
}

struct PendingImplementationMethodGroup {
    equations: Range<usize>,
    binder: Option<Binder>,
}

struct ResolvedDeclarations {
    registry: Arc<ResolvedRegistry>,
    interfaces: Vec<ResolvedInterfaceDeclaration>,
    implementations: Vec<ResolvedImplementation>,
    definitions: Vec<ResolvedDefinition>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum LocalTypeDeclarationKind {
    Nominal,
    Interface,
}

#[derive(Debug, Default)]
struct ImportedNamespaces {
    terms: HashMap<String, ResolvedTermName>,
    nominals: HashMap<String, ImportedNominalName>,
    constructors: HashMap<String, ConstructorId>,
    withheld: HashMap<(String, WithheldNamespace), WithheldImport>,
}

#[derive(Clone, Copy, Debug)]
struct WithheldImport {
    kind: WithheldExportKind,
    declaration: Option<crate::source::Span>,
}

#[derive(Clone, Copy, Debug)]
struct ImportedNominalName {
    id: NominalTypeId,
    parameter_count: usize,
}

impl Resolver {
    #[cfg(test)]
    fn new(module: ModuleId) -> Self {
        Self::with_type_work(module, TypeWorkBudget::default())
    }

    fn with_type_work(module: ModuleId, type_work: TypeWorkBudget) -> Self {
        Self {
            module,
            next_binder: 0,
            next_type_variable: 0,
            scopes: vec![HashMap::new()],
            globals: HashMap::new(),
            type_names: HashMap::new(),
            interface_names: HashMap::new(),
            method_names: HashMap::new(),
            global_requirement_counts: HashMap::new(),
            constructor_names: HashMap::new(),
            module_aliases: HashMap::new(),
            targeted_withheld: HashMap::new(),
            imported: ImportedFacts::default(),
            type_scopes: Vec::new(),
            nominal_parameter_counts: HashMap::new(),
            type_work,
            #[cfg(test)]
            max_type_pending_tasks: 0,
        }
    }

    fn validate_local_namespaces(&self, surface: &SurfaceModule) -> Result<(), ResolveError> {
        let mut type_names: HashMap<&str, (crate::source::Span, LocalTypeDeclarationKind)> =
            HashMap::new();
        let mut term_names: HashMap<&str, (crate::source::Span, Option<crate::source::Span>)> =
            HashMap::new();

        for declaration in &surface.declaration_order {
            match *declaration {
                SurfaceDeclarationIndex::Type(index) => {
                    let declaration = surface.type_declarations.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid type index",
                        )
                    })?;
                    self.validate_local_type_name(
                        &declaration.name,
                        LocalTypeDeclarationKind::Nominal,
                        &mut type_names,
                    )?;
                }
                SurfaceDeclarationIndex::Interface(index) => {
                    let declaration = surface.interfaces.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid interface index",
                        )
                    })?;
                    self.validate_local_type_name(
                        &declaration.name,
                        LocalTypeDeclarationKind::Interface,
                        &mut type_names,
                    )?;
                    for method in &declaration.methods {
                        self.validate_local_term_name(&method.name, None, &mut term_names)?;
                    }
                }
                SurfaceDeclarationIndex::Global(index) => {
                    let definition = surface.definitions.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid global index",
                        )
                    })?;
                    let name = surface_definition_name(definition);
                    self.validate_local_term_name(name, Some(definition.span), &mut term_names)?;
                }
                SurfaceDeclarationIndex::Implementation(index) => {
                    if surface.implementations.get(index).is_none() {
                        return Err(error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid impl index",
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    fn validate_local_type_name<'a>(
        &self,
        name: &'a crate::surface::SurfaceName,
        kind: LocalTypeDeclarationKind,
        names: &mut HashMap<&'a str, (crate::source::Span, LocalTypeDeclarationKind)>,
    ) -> Result<(), ResolveError> {
        if self.module_aliases.contains_key(&name.text) || self.type_names.contains_key(&name.text)
        {
            return Err(import_conflict(name.span, &name.text));
        }
        if let Some((first, first_kind)) = names.insert(&name.text, (name.span, kind)) {
            if first_kind == LocalTypeDeclarationKind::Nominal
                && kind == LocalTypeDeclarationKind::Nominal
            {
                let mut diagnostic = Diagnostic::new(
                    ResolveReason::DuplicateType,
                    SourceLabel::new(name.span, "this nominal type name is already defined"),
                );
                diagnostic
                    .related
                    .push(SourceLabel::new(first, "the first nominal type is here"));
                return Err(diagnostic.into());
            }
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateType,
                SourceLabel::new(name.span, "this type-namespace name is already declared"),
            );
            diagnostic
                .related
                .push(SourceLabel::new(first, "the first declaration is here"));
            diagnostic.found = Some(name.text.clone());
            return Err(diagnostic.into());
        }
        Ok(())
    }

    fn validate_local_term_name<'a>(
        &self,
        name: &'a crate::surface::SurfaceName,
        complete_definition: Option<crate::source::Span>,
        names: &mut HashMap<&'a str, (crate::source::Span, Option<crate::source::Span>)>,
    ) -> Result<(), ResolveError> {
        if self.module_aliases.contains_key(&name.text)
            || self.constructor_names.contains_key(&name.text)
            || self
                .scopes
                .first()
                .is_some_and(|scope| scope.contains_key(&name.text))
        {
            return Err(import_conflict(name.span, &name.text));
        }
        if let Some((first, first_definition)) =
            names.insert(&name.text, (name.span, complete_definition))
        {
            if let (Some(first_definition), Some(_)) = (first_definition, complete_definition) {
                let mut diagnostic = Diagnostic::new(
                    ResolveReason::DuplicateGlobal,
                    SourceLabel::new(name.span, "this global name is already defined"),
                );
                diagnostic
                    .related
                    .push(SourceLabel::new(first, "the first global name is here"));
                diagnostic.related.push(SourceLabel::new(
                    first_definition,
                    "the first complete definition is here",
                ));
                return Err(diagnostic.into());
            }
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateGlobal,
                SourceLabel::new(name.span, "this term name is already declared"),
            );
            diagnostic
                .related
                .push(SourceLabel::new(first, "the first term name is here"));
            if let Some(first_definition) = first_definition {
                diagnostic.related.push(SourceLabel::new(
                    first_definition,
                    "the first complete definition is here",
                ));
            }
            diagnostic.found = Some(name.text.clone());
            return Err(diagnostic.into());
        }
        Ok(())
    }

    fn resolve_interface_declarations(
        &mut self,
        declarations: &[SurfaceInterfaceDeclaration],
    ) -> Result<(Vec<ResolvedInterfaceDeclaration>, Vec<ResolvedTypeVariable>), ResolveError> {
        let mut identities = Vec::with_capacity(declarations.len());
        for (index, declaration) in declarations.iter().enumerate() {
            let index = u32::try_from(index).map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    declaration.span,
                    "the file contains too many interface declarations",
                )
            })?;
            let id = InterfaceId::new(self.module, index);
            self.interface_names
                .insert(declaration.name.text.clone(), id);
            let mut methods = Vec::with_capacity(declaration.methods.len());
            for (method_index, method) in declaration.methods.iter().enumerate() {
                let method_index = u32::try_from(method_index).map_err(|_| {
                    error(
                        ResolveReason::InternalState,
                        method.span,
                        "the interface contains too many method declarations",
                    )
                })?;
                let method_id = MethodId::new(id, method_index);
                self.method_names
                    .insert(method.name.text.clone(), method_id);
                methods.push(method_id);
            }
            identities.push((id, methods));
        }

        let mut resolved = Vec::with_capacity(declarations.len());
        let mut retained_type_variables = Vec::new();
        for (declaration, (id, method_ids)) in declarations.iter().zip(identities) {
            let parameter = self
                .allocate_type_variable(&declaration.parameter.text, declaration.parameter.span)?;
            retained_type_variables.push(parameter.clone());
            let mut methods = Vec::with_capacity(declaration.methods.len());
            for (method, method_id) in declaration.methods.iter().zip(method_ids) {
                let mut names = Vec::new();
                let mut seen = HashSet::from([declaration.parameter.text.as_str()]);
                collect_free_type_names(
                    &method.annotation,
                    &self.type_names,
                    &self.interface_names,
                    &mut seen,
                    &mut names,
                    &mut self.type_work,
                )?;
                let type_parameters = names
                    .into_iter()
                    .map(|name| self.allocate_type_variable(&name.text, name.span))
                    .collect::<Result<Vec<_>, _>>()?;
                retained_type_variables.extend(type_parameters.iter().cloned());
                self.type_scopes.push(
                    std::iter::once((parameter.spelling.clone(), parameter.clone()))
                        .chain(
                            type_parameters
                                .iter()
                                .map(|parameter| (parameter.spelling.clone(), parameter.clone())),
                        )
                        .collect(),
                );
                let annotation = self.resolve_type(&method.annotation);
                let _ = self.type_scopes.pop();
                methods.push(ResolvedInterfaceMethod {
                    id: method_id,
                    spelling: method.name.text.clone(),
                    annotation: annotation?,
                    type_parameters: type_parameters.into_boxed_slice(),
                    origin: Origin::Source(method.span),
                    span: method.span,
                });
            }
            resolved.push(ResolvedInterfaceDeclaration {
                id,
                public: declaration.public,
                spelling: declaration.name.text.clone(),
                parameter,
                methods: methods.into_boxed_slice(),
                origin: Origin::Source(declaration.span),
                span: declaration.span,
            });
        }
        Ok((resolved, retained_type_variables))
    }

    fn prepare_implementations(
        &mut self,
        declarations: &[SurfaceImplementation],
    ) -> Result<(Vec<PendingImplementation>, Vec<ResolvedTypeVariable>), ResolveError> {
        let mut pending = Vec::with_capacity(declarations.len());
        let mut retained_type_variables = Vec::new();

        for (index, implementation) in declarations.iter().enumerate() {
            let index = u32::try_from(index).map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    implementation.span,
                    "the file contains too many implementation declarations",
                )
            })?;
            let id = ImplId::new(self.module, index);

            let mut seen = HashSet::new();
            let mut head_names = Vec::new();
            collect_free_type_names(
                &implementation.argument,
                &self.type_names,
                &self.interface_names,
                &mut seen,
                &mut head_names,
                &mut self.type_work,
            )?;
            let head_parameters = head_names
                .into_iter()
                .map(|name| self.allocate_type_variable(&name.text, name.span))
                .collect::<Result<Vec<_>, _>>()?;

            let mut prerequisite_only_names = Vec::new();
            for prerequisite in &implementation.prerequisites {
                collect_free_type_names(
                    &prerequisite.argument,
                    &self.type_names,
                    &self.interface_names,
                    &mut seen,
                    &mut prerequisite_only_names,
                    &mut self.type_work,
                )?;
            }
            let prerequisite_only_parameters = prerequisite_only_names
                .into_iter()
                .map(|name| self.allocate_type_variable(&name.text, name.span))
                .collect::<Result<Vec<_>, _>>()?;
            retained_type_variables.extend(head_parameters.iter().cloned());
            retained_type_variables.extend(prerequisite_only_parameters.iter().cloned());

            let mut method_groups = Vec::new();
            let mut start = 0;
            while let Some(first) = implementation.equations.get(start) {
                let mut end = start + 1;
                while implementation
                    .equations
                    .get(end)
                    .is_some_and(|equation| equation.name.text == first.name.text)
                {
                    end += 1;
                }
                method_groups.push(PendingImplementationMethodGroup {
                    equations: start..end,
                    binder: None,
                });
                start = end;
            }

            pending.push(PendingImplementation {
                id,
                head_parameters,
                prerequisite_only_parameters,
                method_groups,
            });
        }

        Ok((pending, retained_type_variables))
    }

    fn install_imports(
        &mut self,
        surface: &SurfaceModule,
        dependencies: &[DependencyExports<'_>],
    ) -> Result<(), ResolveError> {
        for (import, dependency) in surface.imports.iter().zip(dependencies) {
            match &import.selection {
                SurfaceImportSelection::Qualified { alias } => {
                    if self.file_name_is_bound(&alias.text) {
                        return Err(import_conflict(alias.span, &alias.text));
                    }
                    let namespaces =
                        self.clone_summary_namespaces(dependency.summary, import.span)?;
                    self.module_aliases.insert(alias.text.clone(), namespaces);
                }
                SurfaceImportSelection::Targeted(items) => {
                    for item in items {
                        let local = item.alias.as_ref().unwrap_or(&item.name);
                        if self.module_aliases.contains_key(&local.text) {
                            return Err(import_conflict(local.span, &local.text));
                        }
                        let mut selected = false;
                        if let Some(exported) = dependency.summary.term(&item.name.text) {
                            selected = true;
                            if self.constructor_names.contains_key(&local.text) {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            let scope = self.scopes.first_mut().ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    item.span,
                                    "the resolver lost the file scope",
                                )
                            })?;
                            if scope.contains_key(&local.text) {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            scope.insert(
                                local.text.clone(),
                                Binder {
                                    id: exported.binder,
                                    spelling: local.text.clone(),
                                    origin: exported.origin.clone(),
                                },
                            );
                            self.retain_imported_global(exported, dependency.summary, item.span)?;
                        }
                        if let Some(exported) = dependency.summary.nominal(&item.name.text) {
                            selected = true;
                            if self.type_names.contains_key(&local.text) {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            self.type_names.insert(local.text.clone(), exported.id);
                            self.nominal_parameter_counts
                                .insert(exported.id, exported.parameter_count);
                            self.retain_imported_nominal(
                                exported,
                                dependency.summary,
                                Some(&item.name.text),
                                item.span,
                            )?;
                        }
                        if let Some(exported) = dependency.summary.constructor(&item.name.text) {
                            selected = true;
                            if self.constructor_names.contains_key(&local.text)
                                || self
                                    .scopes
                                    .first()
                                    .is_some_and(|scope| scope.contains_key(&local.text))
                            {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            self.constructor_names
                                .insert(local.text.clone(), exported.id);
                            self.retain_imported_constructor(
                                exported,
                                dependency.summary,
                                item.span,
                            )?;
                        }
                        if !selected {
                            let withheld = [
                                WithheldNamespace::Term,
                                WithheldNamespace::Nominal,
                                WithheldNamespace::Constructor,
                            ]
                            .into_iter()
                            .filter_map(|namespace| {
                                dependency
                                    .summary
                                    .withheld_export(namespace, &item.name.text)
                            })
                            .map(|withheld| WithheldImport {
                                kind: withheld.kind,
                                declaration: withheld
                                    .origin
                                    .as_ref()
                                    .map(crate::source::Origin::primary_span),
                            })
                            .min_by_key(|withheld| {
                                match withheld.kind {
                                    WithheldExportKind::Private => 0,
                                    WithheldExportKind::OpaqueConstructor => 1,
                                }
                            });
                            return Err(withheld_export_error(
                                item.name.span,
                                &item.name.text,
                                withheld,
                            ));
                        }
                        for namespace in [
                            WithheldNamespace::Term,
                            WithheldNamespace::Nominal,
                            WithheldNamespace::Constructor,
                        ] {
                            let Some(withheld) = dependency
                                .summary
                                .withheld_export(namespace, &item.name.text)
                            else {
                                continue;
                            };
                            self.targeted_withheld.insert(
                                (local.text.clone(), namespace),
                                WithheldImport {
                                    kind: withheld.kind,
                                    declaration: withheld
                                        .origin
                                        .as_ref()
                                        .map(crate::source::Origin::primary_span),
                                },
                            );
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn clone_summary_namespaces(
        &mut self,
        summary: &ExportSummary,
        import_span: crate::source::Span,
    ) -> Result<ImportedNamespaces, ResolveError> {
        let mut namespaces = ImportedNamespaces::default();
        let entry_count = summary.namespace_entry_count();
        self.type_work.charge(entry_count).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                import_span,
                "imported namespace retention exceeded its work budget",
            )
        })?;

        let mut terms = Vec::new();
        terms
            .try_reserve(summary.terms().size_hint().0)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    import_span,
                    "imported namespace retention exceeded its work budget",
                )
            })?;
        terms.extend(summary.terms());
        terms.sort_unstable_by_key(|(spelling, _)| *spelling);
        for (spelling, exported) in terms {
            namespaces.terms.insert(
                spelling.to_owned(),
                ResolvedTermName::Global(exported.binder),
            );
            self.retain_imported_global(exported, summary, import_span)?;
        }

        let mut nominals = Vec::new();
        nominals
            .try_reserve(summary.nominals().size_hint().0)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    import_span,
                    "imported namespace retention exceeded its work budget",
                )
            })?;
        nominals.extend(summary.nominals());
        nominals.sort_unstable_by_key(|(spelling, _)| *spelling);
        for (spelling, exported) in nominals {
            namespaces.nominals.insert(
                spelling.to_owned(),
                ImportedNominalName {
                    id: exported.id,
                    parameter_count: exported.parameter_count,
                },
            );
            self.retain_imported_nominal(exported, summary, Some(spelling), import_span)?;
        }

        let mut constructors = Vec::new();
        constructors
            .try_reserve(summary.constructors().size_hint().0)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    import_span,
                    "imported namespace retention exceeded its work budget",
                )
            })?;
        constructors.extend(summary.constructors());
        constructors.sort_unstable_by_key(|(spelling, _)| *spelling);
        for (spelling, exported) in constructors {
            namespaces
                .constructors
                .insert(spelling.to_owned(), exported.id);
            self.retain_imported_constructor(exported, summary, import_span)?;
        }
        namespaces
            .withheld
            .try_reserve(summary.withheld_count())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    import_span,
                    "imported namespace retention exceeded its work budget",
                )
            })?;
        namespaces
            .withheld
            .extend(summary.withheld().map(|(namespace, spelling, withheld)| {
                (
                    (spelling.to_owned(), namespace),
                    WithheldImport {
                        kind: withheld.kind,
                        declaration: withheld
                            .origin
                            .as_ref()
                            .map(crate::source::Origin::primary_span),
                    },
                )
            }));
        Ok(namespaces)
    }

    fn retain_imported_global(
        &mut self,
        exported: &ExportedGlobal,
        summary: &ExportSummary,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        if self.imported.contains_global(exported.binder) {
            return Ok(());
        }
        let scheme =
            clone_type_with_budget(&exported.scheme, &mut self.type_work).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported type retention exceeded its work budget",
                )
            })?;
        self.imported.insert_global(ImportedGlobalScheme {
            binder: exported.binder,
            scheme,
            origin: exported.origin.clone(),
        });
        self.retain_scheme_nominals(&exported.scheme, summary, span)?;
        Ok(())
    }

    fn retain_scheme_nominals(
        &mut self,
        scheme: &Type,
        summary: &ExportSummary,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        enum Task<'a> {
            Type(&'a Type),
            Sequence(std::slice::Iter<'a, Type>),
        }

        charge_type_cells(scheme, &mut self.type_work).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "imported nominal retention exceeded its work budget",
            )
        })?;
        let mut pending = vec![Task::Type(scheme)];
        let mut seen = HashSet::new();
        while let Some(task) = pending.pop() {
            let Task::Type(ty) = task else {
                let Task::Sequence(mut remaining) = task else {
                    unreachable!()
                };
                if let Some(next) = remaining.next() {
                    pending.push(Task::Sequence(remaining));
                    pending.push(Task::Type(next));
                }
                continue;
            };
            match ty {
                Type::Nominal(id) => {
                    seen.insert(*id);
                }
                Type::AppliedNominal(id, arguments) => {
                    seen.insert(*id);
                    pending.push(Task::Sequence(arguments.iter()));
                }
                Type::Tuple(elements) => pending.push(Task::Sequence(elements.iter())),
                Type::Function(domain, codomain) => {
                    pending.push(Task::Type(codomain));
                    pending.push(Task::Type(domain));
                }
                Type::Forall(_, body) => pending.push(Task::Type(body)),
                Type::Int | Type::Bool | Type::Unit | Type::Variable(_) | Type::Inference(_) => {}
            }
        }
        for id in seen {
            let Some(exported) = summary.nominal_fact(id) else {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "an exported scheme references missing nominal metadata",
                ));
            };
            self.retain_scheme_nominal_fact(exported, span)?;
        }
        Ok(())
    }

    fn retain_scheme_nominal_fact(
        &mut self,
        exported: crate::resolved::ImportedNominalFactRef<'_>,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        self.charge_imported_nominal_metadata(exported.parameters.len(), 0, span)?;
        self.imported
            .merge_nominal(ImportedNominalFact {
                id: exported.id,
                parameter_count: exported.parameter_count,
                parameters: exported.parameters.to_vec().into_boxed_slice(),
                constructors: Vec::new().into_boxed_slice(),
                access: ImportedTypeAccess::Hidden,
                display_spelling: exported.display_spelling.map(str::to_owned),
                display_is_private: exported.display_is_private,
                origin: exported.origin.clone(),
            })
            .map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "imported routes disagree about nominal metadata",
                )
            })
    }

    fn retain_imported_nominal_fact(
        &mut self,
        exported: crate::resolved::ImportedNominalFactRef<'_>,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        self.charge_imported_nominal_metadata(
            exported.parameters.len(),
            exported.constructors.len(),
            span,
        )?;
        self.imported
            .merge_nominal(ImportedNominalFact {
                id: exported.id,
                parameter_count: exported.parameter_count,
                parameters: exported.parameters.to_vec().into_boxed_slice(),
                constructors: exported.constructors.to_vec().into_boxed_slice(),
                access: exported.access,
                display_spelling: exported.display_spelling.map(str::to_owned),
                display_is_private: exported.display_is_private,
                origin: exported.origin.clone(),
            })
            .map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "imported routes disagree about nominal metadata",
                )
            })
    }

    fn retain_imported_nominal(
        &mut self,
        exported: &ExportedType,
        summary: &ExportSummary,
        display_spelling: Option<&str>,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        self.charge_imported_nominal_metadata(
            exported.parameters.len(),
            exported.constructors.len(),
            span,
        )?;
        self.imported
            .merge_nominal(ImportedNominalFact {
                id: exported.id,
                parameter_count: exported.parameter_count,
                parameters: exported.parameters.to_vec().into_boxed_slice(),
                constructors: exported.constructors.to_vec().into_boxed_slice(),
                access: exported.access.into(),
                display_spelling: display_spelling.map(str::to_owned),
                display_is_private: false,
                origin: exported.origin.clone(),
            })
            .map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "imported routes disagree about nominal metadata",
                )
            })?;
        for constructor in &exported.constructors {
            let constructor = summary.constructor_by_id(*constructor).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "a transparent type summary lost one of its constructors",
                )
            })?;
            self.retain_imported_constructor_fact(constructor, summary, span)?;
        }
        Ok(())
    }

    fn charge_imported_nominal_metadata(
        &mut self,
        parameter_count: usize,
        constructor_count: usize,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        self.type_work
            .charge(parameter_count.saturating_add(constructor_count))
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported nominal metadata retention exceeded its work budget",
                )
            })
    }

    fn retain_imported_constructor(
        &mut self,
        exported: &ExportedConstructor,
        summary: &ExportSummary,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        if self.imported.contains_constructor(exported.id) {
            return Ok(());
        }
        let owner = summary.nominal_fact(exported.id.owner()).ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                span,
                "an exported constructor references missing owner metadata",
            )
        })?;
        let siblings = owner.constructors;
        self.retain_imported_nominal_fact(owner, span)?;
        for sibling in siblings {
            let sibling = summary.constructor_by_id(*sibling).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "a transparent type summary lost one of its constructors",
                )
            })?;
            self.retain_imported_constructor_fact(sibling, summary, span)?;
        }
        self.retain_imported_constructor_fact(exported, summary, span)
    }

    fn retain_imported_constructor_fact(
        &mut self,
        exported: &ExportedConstructor,
        summary: &ExportSummary,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        if self.imported.contains_constructor(exported.id) {
            return Ok(());
        }
        if let Some(payload) = &exported.payload {
            self.retain_scheme_nominals(payload, summary, span)?;
        }
        let payload = exported
            .payload
            .as_ref()
            .map(|payload| clone_type_with_budget(payload, &mut self.type_work))
            .transpose()
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported constructor retention exceeded its work budget",
                )
            })?;
        self.imported.insert_constructor(ImportedConstructorFact {
            id: exported.id,
            spelling: exported.spelling.clone(),
            payload,
            origin: exported.origin.clone(),
        });
        Ok(())
    }

    fn file_name_is_bound(&self, spelling: &str) -> bool {
        self.module_aliases.contains_key(spelling)
            || self.type_names.contains_key(spelling)
            || self.interface_names.contains_key(spelling)
            || self.constructor_names.contains_key(spelling)
            || self.method_names.contains_key(spelling)
            || self
                .scopes
                .first()
                .is_some_and(|scope| scope.contains_key(spelling))
    }

    fn expression_name_is_bound(&self, spelling: &str) -> bool {
        self.module_aliases.contains_key(spelling)
            || self.constructor_names.contains_key(spelling)
            || self.method_names.contains_key(spelling)
            || self
                .scopes
                .first()
                .is_some_and(|scope| scope.contains_key(spelling))
    }

    fn imported_namespace(
        &self,
        reference: &SurfaceReference,
    ) -> Result<Option<&ImportedNamespaces>, ResolveError> {
        let SurfaceReference::Qualified(qualified) = reference else {
            return Ok(None);
        };
        self.module_aliases
            .get(&qualified.qualifier.text)
            .map(Some)
            .ok_or_else(|| {
                withheld_export_error(qualified.qualifier.span, &qualified.qualifier.text, None)
            })
    }

    fn nominal_reference(
        &self,
        reference: &SurfaceReference,
    ) -> Result<ImportedNominalName, ResolveError> {
        if let Some(namespace) = self.imported_namespace(reference)? {
            return namespace
                .nominals
                .get(&reference.member().text)
                .copied()
                .ok_or_else(|| {
                    withheld_export_error(
                        reference.member().span,
                        &reference.member().text,
                        namespace
                            .withheld
                            .get(&(reference.member().text.clone(), WithheldNamespace::Nominal))
                            .copied(),
                    )
                });
        }
        let name = reference.member();
        if self.interface_names.contains_key(&name.text) {
            return Err(type_kind_error(name.span, &name.text));
        }
        let id = self.type_names.get(&name.text).copied().ok_or_else(|| {
            if let Some(withheld) = self
                .targeted_withheld
                .get(&(name.text.clone(), WithheldNamespace::Nominal))
                .copied()
            {
                return withheld_export_error(name.span, &name.text, Some(withheld));
            }
            let mut diagnostic = Diagnostic::new(
                ResolveReason::UnknownType,
                SourceLabel::new(name.span, "this nominal type is not declared"),
            );
            diagnostic.found = Some(name.text.clone());
            ResolveError::from(diagnostic)
        })?;
        let parameter_count = self.nominal_parameter_count(id).ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                name.span,
                "the resolver lost nominal parameter metadata",
            )
        })?;
        Ok(ImportedNominalName {
            id,
            parameter_count,
        })
    }

    fn interface_reference(
        &self,
        reference: &SurfaceReference,
    ) -> Result<ResolvedInterfaceOccurrence, ResolveError> {
        let member = reference.member();
        if let Some(namespace) = self.imported_namespace(reference)? {
            if namespace.nominals.contains_key(&member.text)
                || namespace.constructors.contains_key(&member.text)
                || namespace.terms.contains_key(&member.text)
            {
                return Err(interface_kind_error(member.span, &member.text));
            }
            return Err(unknown_interface_error(member.span, &member.text));
        }
        if let Some(id) = self.interface_names.get(&member.text).copied() {
            return Ok(ResolvedInterfaceOccurrence {
                id,
                spelling: member.text.clone(),
                origin: Origin::Source(reference.span()),
            });
        }
        if self.file_name_is_bound(&member.text)
            || self
                .type_scopes
                .iter()
                .rev()
                .any(|scope| scope.contains_key(&member.text))
        {
            return Err(interface_kind_error(member.span, &member.text));
        }
        Err(unknown_interface_error(member.span, &member.text))
    }

    fn resolve_requirements(
        &mut self,
        owner: RequirementOwner,
        requirements: &[SurfaceRequirement],
    ) -> Result<Box<[ResolvedRequirement]>, ResolveError> {
        requirements
            .iter()
            .enumerate()
            .map(|(index, requirement)| {
                let index = u32::try_from(index).map_err(|_| {
                    error(
                        ResolveReason::InternalState,
                        requirement.span,
                        "the declaration contains too many interface requirements",
                    )
                })?;
                Ok(ResolvedRequirement {
                    id: RequirementId::new(owner, index),
                    interface: self.interface_reference(&requirement.interface)?,
                    argument: self.resolve_type(&requirement.argument)?,
                    span: requirement.span,
                })
            })
            .collect::<Result<Vec<_>, ResolveError>>()
            .map(Vec::into_boxed_slice)
    }

    fn constructor_reference(
        &self,
        reference: &SurfaceReference,
    ) -> Result<ConstructorId, ResolveError> {
        if let Some(namespace) = self.imported_namespace(reference)? {
            return namespace
                .constructors
                .get(&reference.member().text)
                .copied()
                .ok_or_else(|| {
                    withheld_export_error(
                        reference.member().span,
                        &reference.member().text,
                        namespace
                            .withheld
                            .get(&(
                                reference.member().text.clone(),
                                WithheldNamespace::Constructor,
                            ))
                            .copied(),
                    )
                });
        }
        if let Some(constructor) = self
            .constructor_names
            .get(&reference.member().text)
            .copied()
        {
            return Ok(constructor);
        }
        if let Some(kind) = self
            .targeted_withheld
            .get(&(
                reference.member().text.clone(),
                WithheldNamespace::Constructor,
            ))
            .copied()
        {
            return Err(withheld_export_error(
                reference.member().span,
                &reference.member().text,
                Some(kind),
            ));
        }
        let mut diagnostic = Diagnostic::new(
            ResolveReason::UnknownConstructor,
            SourceLabel::new(reference.member().span, "this constructor is not declared"),
        );
        diagnostic.found = Some(reference.member().text.clone());
        Err(diagnostic.into())
    }

    fn allocate_global_binder(
        &mut self,
        definition: &SurfaceDefinition,
    ) -> Result<Binder, ResolveError> {
        let (global_name, global_name_span) = match &definition.kind {
            SurfaceDefinitionKind::Equational(equational) => {
                if equational.equations.is_empty() {
                    return Err(error(
                        ResolveReason::InternalState,
                        definition.span,
                        "the equational definition has no clause",
                    ));
                }
                for equation in &equational.equations {
                    if equational.interface.name.text != equation.name.text {
                        let mut diagnostic = Diagnostic::new(
                            ResolveReason::EquationNameMismatch,
                            SourceLabel::new(
                                equation.name.span,
                                "this equation name does not match its interface",
                            ),
                        );
                        diagnostic.related.push(SourceLabel::new(
                            equational.interface.name.span,
                            "the external interface declares this name",
                        ));
                        diagnostic.expected = Some(equational.interface.name.text.clone());
                        diagnostic.found = Some(equation.name.text.clone());
                        diagnostic.help = Some(format!(
                            "rename the equation head to `{}`",
                            equational.interface.name.text
                        ));
                        return Err(diagnostic.into());
                    }
                }
                (
                    equational.interface.name.text.as_str(),
                    equational.interface.name.span,
                )
            }
            SurfaceDefinitionKind::InlineOperational(operational) => (
                operational.header.name.text.as_str(),
                operational.header.name.span,
            ),
        };
        if let Some(first) = self.globals.get(global_name) {
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateGlobal,
                SourceLabel::new(global_name_span, "this global name is already defined"),
            );
            diagnostic.related.push(SourceLabel::new(
                first.name_span,
                "the first global name is here",
            ));
            diagnostic.related.push(SourceLabel::new(
                first.definition_span,
                "the first complete definition is here",
            ));
            return Err(diagnostic.into());
        }
        if self.expression_name_is_bound(global_name) {
            return Err(import_conflict(global_name_span, global_name));
        }
        let global = self.allocate_binder(global_name, global_name_span)?;
        let requirement_count = match &definition.kind {
            SurfaceDefinitionKind::Equational(global) => global.interface.requirements.len(),
            SurfaceDefinitionKind::InlineOperational(global) => global.header.requirements.len(),
        };
        self.global_requirement_counts
            .insert(global.id, requirement_count);
        let Some(file_scope) = self.scopes.first_mut() else {
            return Err(error(
                ResolveReason::InternalState,
                definition.span,
                "the resolver lost the file scope",
            ));
        };
        file_scope.insert(global.spelling.clone(), global.clone());
        self.globals.insert(
            global_name.to_owned(),
            GlobalFact {
                name_span: global_name_span,
                definition_span: definition.span,
            },
        );
        Ok(global)
    }

    fn resolve_declarations(
        &mut self,
        surface: &SurfaceModule,
    ) -> Result<ResolvedDeclarations, ResolveError> {
        let registry = self.resolve_registry(&surface.type_declarations)?;
        let (interfaces, interface_type_parameters) =
            self.resolve_interface_declarations(&surface.interfaces)?;
        let surface_definitions = &surface.definitions;
        let mut global_type_parameters = Vec::with_capacity(surface_definitions.len());
        for definition in surface_definitions {
            global_type_parameters.push(self.allocate_global_type_parameters(definition)?);
        }
        let (mut pending_implementations, implementation_type_parameters) =
            self.prepare_implementations(&surface.implementations)?;
        let registry = Arc::new(
            registry.with_additional_type_variables(
                interface_type_parameters
                    .into_iter()
                    .chain(global_type_parameters.iter().flatten().cloned())
                    .chain(implementation_type_parameters),
            ),
        );
        let mut global_binders = vec![None; surface_definitions.len()];
        for declaration in &surface.declaration_order {
            match *declaration {
                SurfaceDeclarationIndex::Global(index) => {
                    let definition = surface_definitions.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid global index",
                        )
                    })?;
                    let binder = self.allocate_global_binder(definition)?;
                    let slot = global_binders.get_mut(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a global binder slot",
                        )
                    })?;
                    *slot = Some(binder);
                }
                SurfaceDeclarationIndex::Implementation(index) => {
                    let implementation = surface.implementations.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid impl index",
                        )
                    })?;
                    let pending = pending_implementations.get_mut(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost an implementation plan",
                        )
                    })?;
                    for group in &mut pending.method_groups {
                        let first = implementation
                            .equations
                            .get(group.equations.start)
                            .ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    implementation.span,
                                    "an implementation method group is empty",
                                )
                            })?;
                        group.binder =
                            Some(self.allocate_binder(&first.name.text, first.name.span)?);
                    }
                }
                SurfaceDeclarationIndex::Type(_) | SurfaceDeclarationIndex::Interface(_) => {}
            }
        }

        let global_binders = global_binders
            .into_iter()
            .enumerate()
            .map(|(index, binder)| {
                binder.ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        surface_definitions[index].span,
                        "the resolver did not allocate a global binder",
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let mut definitions = Vec::with_capacity(surface_definitions.len());
        for ((definition, global), type_parameters) in surface_definitions
            .iter()
            .zip(global_binders)
            .zip(global_type_parameters)
        {
            let type_scope_checkpoint = self.type_scopes.len();
            self.type_scopes.push(
                type_parameters
                    .iter()
                    .map(|parameter| (parameter.spelling.clone(), parameter.clone()))
                    .collect(),
            );
            let kind = match &definition.kind {
                SurfaceDefinitionKind::Equational(equational) => {
                    let annotation = self.resolve_type(&equational.interface.annotation)?;
                    let requirements = self.resolve_requirements(
                        RequirementOwner::Global(global.id),
                        &equational.interface.requirements,
                    )?;
                    let mut equations = Vec::with_capacity(equational.equations.len());
                    for equation in &equational.equations {
                        let scope_checkpoint = self.scopes.len();
                        let (patterns, binders) =
                            self.resolve_pattern_vector(&equation.patterns)?;
                        self.push_binder_scope_many(&binders);
                        let resolved_body = self.resolve_expr(&equation.body);
                        self.scopes.truncate(scope_checkpoint);
                        equations.push(ResolvedEquation {
                            name: crate::resolved::ResolvedEquationHead {
                                binder: global.id,
                                spelling: equation.name.text.clone(),
                                origin: Origin::Source(equation.name.span),
                            },
                            patterns,
                            body: resolved_body?,
                            span: equation.span,
                        });
                    }
                    if equations.is_empty() {
                        return Err(error(
                            ResolveReason::InternalState,
                            definition.span,
                            "the resolver produced no equation",
                        ));
                    }
                    ResolvedDefinitionKind::Equational(ResolvedEquationalGlobal {
                        interface: ResolvedExternalInterface {
                            name: global.clone(),
                            annotation,
                            requirements,
                            type_parameters: type_parameters.clone().into_boxed_slice(),
                            span: equational.interface.span,
                        },
                        equations,
                    })
                }
                SurfaceDefinitionKind::InlineOperational(operational) => {
                    let requirements = self.resolve_requirements(
                        RequirementOwner::Global(global.id),
                        &operational.header.requirements,
                    )?;
                    let surface_patterns = operational
                        .header
                        .parameters
                        .iter()
                        .map(|parameter| parameter.pattern.clone())
                        .collect::<Vec<_>>();
                    let (patterns, binders) = self.resolve_pattern_vector(&surface_patterns)?;
                    let scope_checkpoint = self.scopes.len();
                    self.push_binder_scope_many(&binders);
                    let resolved_body = self.resolve_block(&operational.body);
                    self.scopes.truncate(scope_checkpoint);
                    let body = resolved_body?;
                    let parameters = patterns
                        .into_iter()
                        .zip(&operational.header.parameters)
                        .map(|(pattern, parameter)| {
                            Ok(ResolvedTypedPattern {
                                pattern,
                                annotation: self.resolve_type(&parameter.annotation)?,
                                span: parameter.span,
                            })
                        })
                        .collect::<Result<Vec<_>, ResolveError>>()?;
                    if parameters.is_empty() {
                        return Err(error(
                            ResolveReason::InternalState,
                            operational.header.span,
                            "the resolver produced no operational parameter",
                        ));
                    }
                    ResolvedDefinitionKind::InlineOperational(ResolvedInlineOperationalGlobal {
                        header: ResolvedInlineOperationalHeader {
                            name: global.clone(),
                            parameters,
                            result_type: self.resolve_type(&operational.header.result_type)?,
                            requirements,
                            type_parameters: type_parameters.clone().into_boxed_slice(),
                            span: operational.header.span,
                        },
                        body,
                    })
                }
            };
            definitions.push(ResolvedDefinition {
                kind,
                span: definition.span,
            });
            self.type_scopes.truncate(type_scope_checkpoint);
        }

        let implementations = self.resolve_implementations(
            &surface.implementations,
            pending_implementations,
            surface.span,
        )?;

        Ok(ResolvedDeclarations {
            registry,
            interfaces,
            implementations,
            definitions,
        })
    }

    fn resolve_implementations(
        &mut self,
        declarations: &[SurfaceImplementation],
        pending: Vec<PendingImplementation>,
        module_span: crate::source::Span,
    ) -> Result<Vec<ResolvedImplementation>, ResolveError> {
        if declarations.len() != pending.len() {
            return Err(error(
                ResolveReason::InternalState,
                module_span,
                "the resolver retained mismatched implementation plans",
            ));
        }

        declarations
            .iter()
            .zip(pending)
            .map(|(implementation, pending)| {
                let type_scope_checkpoint = self.type_scopes.len();
                self.type_scopes.push(
                    pending
                        .head_parameters
                        .iter()
                        .chain(&pending.prerequisite_only_parameters)
                        .map(|parameter| (parameter.spelling.clone(), parameter.clone()))
                        .collect(),
                );

                let result = (|| {
                    let interface = self.interface_reference(&implementation.interface)?;
                    let argument = self.resolve_type(&implementation.argument)?;
                    let prerequisites = self.resolve_requirements(
                        RequirementOwner::Impl(pending.id),
                        &implementation.prerequisites,
                    )?;
                    let method_groups = pending
                        .method_groups
                        .into_iter()
                        .map(|group| {
                            let equations = implementation
                                .equations
                                .get(group.equations.clone())
                                .ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    implementation.span,
                                    "the resolver retained an invalid method-group range",
                                )
                            })?;
                            let first = equations.first().ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    implementation.span,
                                    "the resolver retained an empty method group",
                                )
                            })?;
                            let last = equations.last().ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    implementation.span,
                                    "the resolver retained an empty method group",
                                )
                            })?;
                            let span = first.span.cover(last.span).ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    implementation.span,
                                    "one implementation method group crosses source files",
                                )
                            })?;
                            let binder = group.binder.ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    first.span,
                                    "the resolver did not allocate a hidden method binder",
                                )
                            })?;
                            let method = self.method_names.get(&first.name.text).copied();
                            let identity =
                                method.map(|method| ImplMethodId::new(pending.id, method));
                            let equations = equations
                                .iter()
                                .map(|equation| {
                                    let scope_checkpoint = self.scopes.len();
                                    let (patterns, binders) =
                                        self.resolve_pattern_vector(&equation.patterns)?;
                                    self.push_binder_scope_many(&binders);
                                    let body = self.resolve_expr(&equation.body);
                                    self.scopes.truncate(scope_checkpoint);
                                    Ok(ResolvedEquation {
                                        name: crate::resolved::ResolvedEquationHead {
                                            binder: binder.id,
                                            spelling: equation.name.text.clone(),
                                            origin: Origin::Source(equation.name.span),
                                        },
                                        patterns,
                                        body: body?,
                                        span: equation.span,
                                    })
                                })
                                .collect::<Result<Vec<_>, ResolveError>>()?;
                            Ok(ResolvedImplementationMethodGroup {
                                method,
                                identity,
                                binder,
                                equations: equations.into_boxed_slice(),
                                span,
                            })
                        })
                        .collect::<Result<Vec<_>, ResolveError>>()?;

                    Ok(ResolvedImplementation {
                        id: pending.id,
                        public: implementation.public,
                        interface,
                        argument,
                        head_parameters: pending.head_parameters.into_boxed_slice(),
                        prerequisite_only_parameters: pending
                            .prerequisite_only_parameters
                            .into_boxed_slice(),
                        prerequisites,
                        method_groups: method_groups.into_boxed_slice(),
                        span: implementation.span,
                    })
                })();

                self.type_scopes.truncate(type_scope_checkpoint);
                result
            })
            .collect()
    }

    fn resolve_registry(
        &mut self,
        type_declarations: &[SurfaceTypeDeclaration],
    ) -> Result<ResolvedRegistry, ResolveError> {
        let mut first_types = HashMap::new();
        let mut nominal_ids = Vec::with_capacity(type_declarations.len());
        for (index, declaration) in type_declarations.iter().enumerate() {
            if let Some(first) =
                first_types.insert(declaration.name.text.as_str(), declaration.name.span)
            {
                let mut diagnostic = Diagnostic::new(
                    ResolveReason::DuplicateType,
                    SourceLabel::new(
                        declaration.name.span,
                        "this nominal type name is already defined",
                    ),
                );
                diagnostic
                    .related
                    .push(SourceLabel::new(first, "the first nominal type is here"));
                return Err(diagnostic.into());
            }
            if self.module_aliases.contains_key(&declaration.name.text)
                || self.type_names.contains_key(&declaration.name.text)
            {
                return Err(import_conflict(
                    declaration.name.span,
                    &declaration.name.text,
                ));
            }
            let index = u32::try_from(index).map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    declaration.span,
                    "the file contains too many type declarations",
                )
            })?;
            let id = NominalTypeId::new(self.module, index);
            self.type_names.insert(declaration.name.text.clone(), id);
            nominal_ids.push(id);
        }

        let mut first_constructors = HashMap::new();
        let mut constructor_ids = Vec::with_capacity(type_declarations.len());
        for (declaration, owner) in type_declarations.iter().zip(&nominal_ids) {
            let mut owned = Vec::with_capacity(declaration.constructors.len());
            for (index, constructor) in declaration.constructors.iter().enumerate() {
                if let Some(first) =
                    first_constructors.insert(constructor.name.text.as_str(), constructor.name.span)
                {
                    let mut diagnostic = Diagnostic::new(
                        ResolveReason::DuplicateConstructor,
                        SourceLabel::new(
                            constructor.name.span,
                            "this constructor name is already defined",
                        ),
                    );
                    diagnostic
                        .related
                        .push(SourceLabel::new(first, "the first constructor is here"));
                    return Err(diagnostic.into());
                }
                if self.module_aliases.contains_key(&constructor.name.text)
                    || self.constructor_names.contains_key(&constructor.name.text)
                    || self
                        .scopes
                        .first()
                        .is_some_and(|scope| scope.contains_key(&constructor.name.text))
                {
                    return Err(import_conflict(
                        constructor.name.span,
                        &constructor.name.text,
                    ));
                }
                let index = u32::try_from(index).map_err(|_| {
                    error(
                        ResolveReason::InternalState,
                        constructor.span,
                        "the declaration contains too many constructors",
                    )
                })?;
                let id = ConstructorId::new(*owner, index);
                self.constructor_names
                    .insert(constructor.name.text.clone(), id);
                owned.push(id);
            }
            constructor_ids.push(owned);
        }

        let mut nominal_parameters = Vec::with_capacity(type_declarations.len());
        for (declaration, owner) in type_declarations.iter().zip(&nominal_ids) {
            let mut first = HashMap::new();
            let mut parameters = Vec::with_capacity(declaration.parameters.len());
            for parameter in &declaration.parameters {
                if let Some(first_span) = first.insert(parameter.text.as_str(), parameter.span) {
                    let mut diagnostic = Diagnostic::new(
                        ResolveReason::DuplicateTypeParameter,
                        SourceLabel::new(parameter.span, "this type parameter is already declared"),
                    );
                    diagnostic.related.push(SourceLabel::new(
                        first_span,
                        "the first type parameter is here",
                    ));
                    return Err(diagnostic.into());
                }
                parameters.push(self.allocate_type_variable(&parameter.text, parameter.span)?);
            }
            nominal_parameters.push((*owner, parameters));
        }
        self.nominal_parameter_counts.extend(
            nominal_parameters
                .iter()
                .map(|(owner, parameters)| (*owner, parameters.len())),
        );

        let nominals = type_declarations
            .iter()
            .zip(&nominal_ids)
            .zip(&constructor_ids)
            .map(|((declaration, id), constructors)| ResolvedNominalType {
                id: *id,
                spelling: declaration.name.text.clone(),
                constructors: constructors.clone().into_boxed_slice(),
                origin: Origin::Source(declaration.span),
            })
            .collect::<Vec<_>>();
        let mut constructors = Vec::new();
        for (((declaration, owner), ids), (_, parameters)) in type_declarations
            .iter()
            .zip(&nominal_ids)
            .zip(&constructor_ids)
            .zip(&nominal_parameters)
        {
            self.type_scopes.push(
                parameters
                    .iter()
                    .map(|parameter| (parameter.spelling.clone(), parameter.clone()))
                    .collect(),
            );
            for (constructor, id) in declaration.constructors.iter().zip(ids) {
                let payload = match constructor.fields.as_slice() {
                    [] => None,
                    [field] => Some(self.resolve_type(field)?.ty),
                    fields => {
                        self.type_work.charge(1).map_err(|()| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                constructor.span,
                                "constructor payload synthesis exceeded its type-work budget",
                            )
                        })?;
                        Some(Type::Tuple(
                            fields
                                .iter()
                                .map(|field| self.resolve_type(field).map(|resolved| resolved.ty))
                                .collect::<Result<Vec<_>, _>>()?
                                .into_boxed_slice(),
                        ))
                    }
                };
                constructors.push(ResolvedConstructor {
                    id: *id,
                    owner: *owner,
                    spelling: constructor.name.text.clone(),
                    payload,
                    origin: Origin::Source(constructor.span),
                });
            }
            let _ = self.type_scopes.pop();
        }
        Ok(ResolvedRegistry::new(nominals, constructors).with_type_parameters(nominal_parameters))
    }

    fn push_binder_scope_many(&mut self, binders: &[Binder]) {
        self.scopes.push(
            binders
                .iter()
                .map(|binder| (binder.spelling.clone(), binder.clone()))
                .collect(),
        );
    }

    fn resolve_type(&mut self, surface: &SurfaceType) -> Result<ResolvedType, ResolveError> {
        enum Task<'a> {
            Visit(&'a SurfaceType),
            Sequence(std::slice::Iter<'a, SurfaceType>),
            Tuple(usize, crate::source::Span),
            Function(crate::source::Span),
            Application(NominalTypeId, usize, crate::source::Span),
        }
        let mut tasks = vec![Task::Visit(surface)];
        let mut completed = Vec::new();
        let mut provenance = Vec::new();
        while let Some(task) = tasks.pop() {
            #[cfg(test)]
            {
                self.max_type_pending_tasks = self.max_type_pending_tasks.max(tasks.len() + 1);
            }
            match task {
                Task::Visit(current) => {
                    self.type_work.charge(1).map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            current.span,
                            "source type resolution exceeded its work budget",
                        )
                    })?;
                    match &current.kind {
                        SurfaceTypeKind::Int => {
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Int, provenance.len() - 1));
                        }
                        SurfaceTypeKind::Bool => {
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Bool, provenance.len() - 1));
                        }
                        SurfaceTypeKind::Unit => {
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Unit, provenance.len() - 1));
                        }
                        SurfaceTypeKind::Named(name) => {
                            if matches!(name, SurfaceReference::Unqualified(_))
                                && let Some(variable) = self
                                    .type_scopes
                                    .iter()
                                    .rev()
                                    .find_map(|scope| scope.get(&name.member().text))
                            {
                                provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                                completed.push((Type::Variable(variable.id), provenance.len() - 1));
                                continue;
                            }
                            let nominal = self.nominal_reference(name)?;
                            let id = nominal.id;
                            let expected = nominal.parameter_count;
                            if expected != 0 {
                                return Err(type_argument_count(
                                    name.span(),
                                    &name.member().text,
                                    expected,
                                    0,
                                ));
                            }
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Nominal(id), provenance.len() - 1));
                        }
                        SurfaceTypeKind::Application {
                            constructor,
                            arguments,
                        } => {
                            if matches!(constructor, SurfaceReference::Unqualified(_))
                                && self
                                    .type_scopes
                                    .iter()
                                    .rev()
                                    .any(|scope| scope.contains_key(&constructor.member().text))
                            {
                                return Err(error(
                                    ResolveReason::TypeKind,
                                    constructor.span(),
                                    "a parameter of kind Type cannot be applied",
                                ));
                            }
                            let nominal = self.nominal_reference(constructor)?;
                            let id = nominal.id;
                            let expected = nominal.parameter_count;
                            if expected != arguments.len() {
                                return Err(type_argument_count(
                                    current.span,
                                    &constructor.member().text,
                                    expected,
                                    arguments.len(),
                                ));
                            }
                            tasks.push(Task::Application(id, arguments.len(), current.span));
                            tasks.push(Task::Sequence(arguments.iter()));
                        }
                        SurfaceTypeKind::Tuple(elements) => {
                            tasks.push(Task::Tuple(elements.len(), current.span));
                            tasks.push(Task::Sequence(elements.iter()));
                        }
                        SurfaceTypeKind::Function(function) => {
                            tasks.push(Task::Function(current.span));
                            tasks.push(Task::Visit(&function.codomain));
                            tasks.push(Task::Visit(&function.domain));
                        }
                    }
                }
                Task::Sequence(mut remaining) => {
                    if let Some(next) = remaining.next() {
                        tasks.push(Task::Sequence(remaining));
                        tasks.push(Task::Visit(next));
                    }
                }
                Task::Tuple(count, span) => {
                    let split = completed.len().checked_sub(count).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a tuple type element",
                        )
                    })?;
                    let elements = completed.split_off(split);
                    let roots = elements
                        .iter()
                        .map(|(_, root)| *root)
                        .collect::<Vec<_>>()
                        .into_boxed_slice();
                    provenance.push(ResolvedTypeProvenanceNode::Tuple {
                        span,
                        elements: roots,
                    });
                    completed.push((
                        Type::Tuple(
                            elements
                                .into_iter()
                                .map(|(ty, _)| ty)
                                .collect::<Vec<_>>()
                                .into_boxed_slice(),
                        ),
                        provenance.len() - 1,
                    ));
                }
                Task::Function(span) => {
                    let (codomain, codomain_root) = completed.pop().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a function codomain",
                        )
                    })?;
                    let (domain, domain_root) = completed.pop().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a function domain",
                        )
                    })?;
                    provenance.push(ResolvedTypeProvenanceNode::Function {
                        span,
                        domain: domain_root,
                        codomain: codomain_root,
                    });
                    completed.push((
                        Type::Function(Box::new(domain), Box::new(codomain)),
                        provenance.len() - 1,
                    ));
                }
                Task::Application(owner, count, span) => {
                    let split = completed.len().checked_sub(count).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a type argument",
                        )
                    })?;
                    let arguments = completed.split_off(split);
                    let roots = arguments
                        .iter()
                        .map(|(_, root)| *root)
                        .collect::<Vec<_>>()
                        .into_boxed_slice();
                    provenance.push(ResolvedTypeProvenanceNode::Application {
                        span,
                        arguments: roots,
                    });
                    completed.push((
                        Type::AppliedNominal(
                            owner,
                            arguments
                                .into_iter()
                                .map(|(ty, _)| ty)
                                .collect::<Vec<_>>()
                                .into_boxed_slice(),
                        ),
                        provenance.len() - 1,
                    ));
                }
            }
        }
        if completed.len() != 1 {
            return Err(error(
                ResolveReason::InternalState,
                surface.span,
                "the resolver retained incomplete type state",
            ));
        }
        let (ty, root) = completed.pop().ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                surface.span,
                "the resolver produced no type",
            )
        })?;
        Ok(ResolvedType {
            ty,
            provenance: ResolvedTypeProvenance::new(provenance, root),
            origin: Origin::Source(surface.span),
            span: surface.span,
        })
    }

    fn resolve_pattern_vector(
        &mut self,
        patterns: &[SurfacePattern],
    ) -> Result<(Vec<ResolvedPattern>, Vec<Binder>), ResolveError> {
        let mut seen = HashMap::new();
        let mut binders = Vec::new();
        let patterns = patterns
            .iter()
            .map(|pattern| self.resolve_pattern(pattern, &mut seen, &mut binders))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((patterns, binders))
    }

    fn resolve_pattern(
        &mut self,
        pattern: &SurfacePattern,
        seen: &mut HashMap<String, crate::source::Span>,
        binders: &mut Vec<Binder>,
    ) -> Result<ResolvedPattern, ResolveError> {
        let kind = match &pattern.kind {
            SurfacePatternKind::Binder(surface) => {
                if let Some(first) = seen.insert(surface.name.text.clone(), surface.name.span) {
                    let mut diagnostic = Diagnostic::new(
                        ResolveReason::DuplicatePatternBinder,
                        SourceLabel::new(
                            surface.name.span,
                            "this pattern binder is already defined",
                        ),
                    );
                    diagnostic
                        .related
                        .push(SourceLabel::new(first, "the first pattern binder is here"));
                    return Err(diagnostic.into());
                }
                let binder = self.allocate_binder(&surface.name.text, surface.name.span)?;
                binders.push(binder.clone());
                ResolvedPatternKind::Binder(binder)
            }
            SurfacePatternKind::Wildcard => ResolvedPatternKind::Wildcard,
            SurfacePatternKind::Boolean(value) => ResolvedPatternKind::Boolean(*value),
            SurfacePatternKind::Unit => ResolvedPatternKind::Unit,
            SurfacePatternKind::Tuple(elements) => ResolvedPatternKind::Tuple(
                elements
                    .iter()
                    .map(|element| self.resolve_pattern(element, seen, binders))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            SurfacePatternKind::Constructor { name, payload } => {
                let constructor = self.constructor_reference(name)?;
                ResolvedPatternKind::Constructor {
                    constructor,
                    occurrence: ResolvedConstructorOccurrence {
                        constructor,
                        spelling: name.member().text.clone(),
                        origin: Origin::Source(name.span()),
                    },
                    payload: payload
                        .as_deref()
                        .map(|payload| self.resolve_pattern(payload, seen, binders).map(Box::new))
                        .transpose()?,
                }
            }
        };
        Ok(ResolvedPattern {
            kind,
            span: pattern.span,
        })
    }

    fn resolve_block(&mut self, block: &SurfaceBlock) -> Result<ResolvedBlock, ResolveError> {
        let resolved = self.resolve_work(ResolveTask::VisitBlock(block))?;
        let ResolvedExprKind::Block(block) = resolved.kind else {
            return Err(error(
                ResolveReason::InternalState,
                block.span,
                "the resolver produced the wrong block payload",
            ));
        };
        Ok(block)
    }

    fn allocate_binder(
        &mut self,
        spelling: &str,
        span: crate::source::Span,
    ) -> Result<Binder, ResolveError> {
        let id = BinderId::resolved(self.module, self.next_binder);
        self.next_binder = self.next_binder.checked_add(1).ok_or_else(|| {
            error(
                ResolveReason::BinderIdExhausted,
                span,
                "the program contains too many binders",
            )
        })?;
        Ok(Binder {
            id,
            spelling: spelling.to_owned(),
            origin: Origin::Source(span),
        })
    }

    fn allocate_type_variable(
        &mut self,
        spelling: &str,
        span: crate::source::Span,
    ) -> Result<ResolvedTypeVariable, ResolveError> {
        let id = TypeVariableId::resolved(self.module, self.next_type_variable);
        self.next_type_variable = self.next_type_variable.checked_add(1).ok_or_else(|| {
            error(
                ResolveReason::BinderIdExhausted,
                span,
                "the program contains too many type binders",
            )
        })?;
        Ok(ResolvedTypeVariable {
            id,
            spelling: spelling.to_owned(),
            origin: Origin::Source(span),
        })
    }

    fn allocate_global_type_parameters(
        &mut self,
        definition: &crate::surface::SurfaceDefinition,
    ) -> Result<Vec<ResolvedTypeVariable>, ResolveError> {
        let mut names = Vec::new();
        let mut seen = HashSet::new();
        match &definition.kind {
            SurfaceDefinitionKind::Equational(equational) => {
                collect_free_type_names(
                    &equational.interface.annotation,
                    &self.type_names,
                    &self.interface_names,
                    &mut seen,
                    &mut names,
                    &mut self.type_work,
                )?;
                for requirement in &equational.interface.requirements {
                    collect_free_type_names(
                        &requirement.argument,
                        &self.type_names,
                        &self.interface_names,
                        &mut seen,
                        &mut names,
                        &mut self.type_work,
                    )?;
                }
            }
            SurfaceDefinitionKind::InlineOperational(operational) => {
                for parameter in &operational.header.parameters {
                    collect_free_type_names(
                        &parameter.annotation,
                        &self.type_names,
                        &self.interface_names,
                        &mut seen,
                        &mut names,
                        &mut self.type_work,
                    )?;
                }
                collect_free_type_names(
                    &operational.header.result_type,
                    &self.type_names,
                    &self.interface_names,
                    &mut seen,
                    &mut names,
                    &mut self.type_work,
                )?;
                for requirement in &operational.header.requirements {
                    collect_free_type_names(
                        &requirement.argument,
                        &self.type_names,
                        &self.interface_names,
                        &mut seen,
                        &mut names,
                        &mut self.type_work,
                    )?;
                }
            }
        }
        names
            .into_iter()
            .map(|name| self.allocate_type_variable(&name.text, name.span))
            .collect()
    }

    fn nominal_parameter_count(&self, id: NominalTypeId) -> Option<usize> {
        self.nominal_parameter_counts.get(&id).copied()
    }

    fn resolve_expr(&mut self, expression: &SurfaceExpr) -> Result<ResolvedExpr, ResolveError> {
        self.resolve_work(ResolveTask::VisitExpr(expression))
    }

    fn resolve_work<'a>(&mut self, initial: ResolveTask<'a>) -> Result<ResolvedExpr, ResolveError> {
        let scope_checkpoint = self.scopes.len();
        let result = self.resolve_work_inner(initial);
        if result.is_err() {
            self.scopes.truncate(scope_checkpoint);
        }
        result
    }

    fn resolve_work_inner<'a>(
        &mut self,
        initial: ResolveTask<'a>,
    ) -> Result<ResolvedExpr, ResolveError> {
        let initial_span = initial.span();
        let mut tasks = vec![initial];
        let mut expressions = Vec::new();
        let mut declarations = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                ResolveTask::VisitExpr(expression) => {
                    self.visit_expression(expression, &mut tasks, &mut expressions)?;
                }
                ResolveTask::VisitBlock(block) => {
                    let scope_checkpoint = self.scopes.len();
                    self.scopes.push(HashMap::new());
                    let declaration_start = declarations.len();
                    tasks.push(ResolveTask::FinishBlock {
                        declaration_start,
                        scope_checkpoint,
                        span: block.span,
                    });
                    tasks.push(ResolveTask::VisitExpr(&block.result));
                    for declaration in block.declarations.iter().rev() {
                        match declaration {
                            SurfaceLocalDeclaration::Binding(binding) => {
                                tasks.push(ResolveTask::FinishBinding(binding));
                                tasks.push(ResolveTask::VisitExpr(&binding.initializer));
                            }
                            SurfaceLocalDeclaration::Recursive(group) => {
                                tasks.push(ResolveTask::VisitRecursiveGroup(group));
                            }
                        }
                    }
                }
                ResolveTask::VisitRecursiveGroup(group) => {
                    let mut first_members = HashMap::with_capacity(group.members.len());
                    let mut binders = Vec::with_capacity(group.members.len());
                    for member in &group.members {
                        if let Some(first_span) =
                            first_members.get(member.binder.name.text.as_str()).copied()
                        {
                            let mut diagnostic = Diagnostic::new(
                                ResolveReason::DuplicateRecursiveMember,
                                SourceLabel::new(
                                    member.binder.name.span,
                                    "this recursive member name is already defined",
                                ),
                            );
                            diagnostic.related.push(SourceLabel::new(
                                first_span,
                                "the first recursive member is here",
                            ));
                            diagnostic.found = Some(member.binder.name.text.clone());
                            return Err(diagnostic.into());
                        }
                        first_members
                            .insert(member.binder.name.text.as_str(), member.binder.name.span);
                        binders.push(
                            self.allocate_binder(
                                &member.binder.name.text,
                                member.binder.name.span,
                            )?,
                        );
                    }
                    let Some(scope) = self.scopes.last_mut() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            group.span,
                            "the resolver lost the current lexical scope",
                        ));
                    };
                    for binder in &binders {
                        scope.insert(binder.spelling.clone(), binder.clone());
                    }
                    tasks.push(ResolveTask::FinishRecursiveGroup { group, binders });
                    for member in group.members.iter().rev() {
                        tasks.push(ResolveTask::VisitExpr(&member.initializer));
                    }
                }
                ResolveTask::FinishApplication { span } => {
                    let (function, argument) = take_expression_pair(&mut expressions, span)?;
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
                            function: Box::new(function),
                            argument: Box::new(argument),
                        }),
                        span,
                    });
                }
                ResolveTask::FinishBinary {
                    kind,
                    operator_span,
                    span,
                } => {
                    let (left, right) = take_expression_pair(&mut expressions, span)?;
                    let binary = ResolvedBinaryExpr {
                        left: Box::new(left),
                        right: Box::new(right),
                        operator_span,
                    };
                    expressions.push(ResolvedExpr {
                        kind: kind.finish(binary),
                        span,
                    });
                }
                ResolveTask::FinishBinding(binding) => {
                    let Some(initializer) = expressions.pop() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            binding.span,
                            "the resolver lost a binding initializer",
                        ));
                    };
                    let (mut patterns, binders) =
                        self.resolve_pattern_vector(std::slice::from_ref(&binding.pattern))?;
                    let pattern = patterns.pop().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            binding.pattern.span,
                            "the resolver produced no binding pattern",
                        )
                    })?;
                    let annotation = binding
                        .annotation
                        .as_ref()
                        .map(|annotation| self.resolve_type(annotation))
                        .transpose()?;
                    let Some(scope) = self.scopes.last_mut() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            binding.span,
                            "the resolver lost the current lexical scope",
                        ));
                    };
                    for binder in binders {
                        scope.insert(binder.spelling.clone(), binder);
                    }
                    declarations.push(ResolvedLocalDeclaration::Binding(Box::new(
                        ResolvedBinding {
                            pattern,
                            annotation,
                            initializer,
                            span: binding.span,
                        },
                    )));
                }
                ResolveTask::FinishRecursiveGroup { group, binders } => {
                    if binders.len() != group.members.len()
                        || expressions.len() < group.members.len()
                    {
                        return Err(error(
                            ResolveReason::InternalState,
                            group.span,
                            "the resolver lost a recursive group member",
                        ));
                    }
                    let expression_start = expressions.len() - group.members.len();
                    let initializers = expressions.split_off(expression_start);
                    let members = group
                        .members
                        .iter()
                        .zip(binders)
                        .zip(initializers)
                        .map(|((member, binder), initializer)| {
                            Ok(ResolvedRecursiveMember {
                                introducer_span: member.introducer_span,
                                binder,
                                annotation: self.resolve_type(&member.annotation)?,
                                initializer,
                                span: member.span,
                            })
                        })
                        .collect::<Result<Vec<_>, ResolveError>>()?;
                    declarations.push(ResolvedLocalDeclaration::Recursive(
                        ResolvedRecursiveGroup {
                            members,
                            span: group.span,
                        },
                    ));
                }
                ResolveTask::FinishBlock {
                    declaration_start,
                    scope_checkpoint,
                    span,
                } => {
                    let Some(result) = expressions.pop() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a block result",
                        ));
                    };
                    if declaration_start > declarations.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a block binding",
                        ));
                    }
                    let block_declarations = declarations.split_off(declaration_start);
                    self.scopes.truncate(scope_checkpoint);
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Block(ResolvedBlock {
                            declarations: block_declarations,
                            result: Box::new(result),
                            span,
                        }),
                        span,
                    });
                }
                ResolveTask::FinishFunction {
                    parameter: pattern,
                    scope_checkpoint,
                    span,
                } => {
                    let Some(body_expression) = expressions.pop() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a function body",
                        ));
                    };
                    let ResolvedExprKind::Block(body) = body_expression.kind else {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver produced the wrong function body payload",
                        ));
                    };
                    self.scopes.truncate(scope_checkpoint);
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Function(ResolvedFunctionExpr { pattern, body }),
                        span,
                    });
                }
                ResolveTask::FinishTuple { count, span } => {
                    let split = expressions.len().checked_sub(count).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a tuple element",
                        )
                    })?;
                    let elements = expressions.split_off(split);
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Tuple(elements),
                        span,
                    });
                }
            }
        }

        let Some(result) = expressions.pop() else {
            return Err(error(
                ResolveReason::InternalState,
                initial_span,
                "the resolver produced no expression",
            ));
        };
        if !expressions.is_empty() || !declarations.is_empty() {
            return Err(error(
                ResolveReason::InternalState,
                initial_span,
                "the resolver retained incomplete expression state",
            ));
        }
        Ok(result)
    }

    fn visit_expression<'a>(
        &mut self,
        expression: &'a SurfaceExpr,
        tasks: &mut Vec<ResolveTask<'a>>,
        expressions: &mut Vec<ResolvedExpr>,
    ) -> Result<(), ResolveError> {
        match &expression.kind {
            SurfaceExprKind::Integer(value) => expressions.push(ResolvedExpr {
                kind: ResolvedExprKind::Integer(value.clone()),
                span: expression.span,
            }),
            SurfaceExprKind::Boolean(value) => expressions.push(ResolvedExpr {
                kind: ResolvedExprKind::Boolean(*value),
                span: expression.span,
            }),
            SurfaceExprKind::Unit => expressions.push(ResolvedExpr {
                kind: ResolvedExprKind::Unit,
                span: expression.span,
            }),
            SurfaceExprKind::Name(name) => {
                let member = name.member();
                let qualified = self.imported_namespace(name)?;
                let term = if let Some(namespace) = qualified {
                    namespace.terms.get(&member.text).copied()
                } else {
                    self.scopes
                        .iter()
                        .rev()
                        .find_map(|scope| scope.get(&member.text))
                        .map(|binder| ResolvedTermName::Global(binder.id))
                        .or_else(|| {
                            self.method_names
                                .get(&member.text)
                                .copied()
                                .map(ResolvedTermName::Method)
                        })
                };
                if let Some(term) = term {
                    let evidence_count = match term {
                        ResolvedTermName::Global(binder) => self
                            .global_requirement_counts
                            .get(&binder)
                            .copied()
                            .unwrap_or(0),
                        ResolvedTermName::Method(_) => 1,
                    };
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                            term,
                            spelling: member.text.clone(),
                            origin: Origin::Source(name.span()),
                            evidence: vec![EvidenceSlot::Empty; evidence_count].into_boxed_slice(),
                        }),
                        span: expression.span,
                    });
                } else if let Some(constructor) = qualified
                    .and_then(|namespace| namespace.constructors.get(&member.text).copied())
                    .or_else(|| {
                        qualified
                            .is_none()
                            .then(|| self.constructor_names.get(&member.text).copied())
                            .flatten()
                    })
                {
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Constructor(ResolvedConstructorOccurrence {
                            constructor,
                            spelling: member.text.clone(),
                            origin: Origin::Source(name.span()),
                        }),
                        span: expression.span,
                    });
                } else if let Some(namespace) = qualified {
                    return Err(withheld_export_error(
                        member.span,
                        &member.text,
                        namespace
                            .withheld
                            .get(&(member.text.clone(), WithheldNamespace::Term))
                            .or_else(|| {
                                namespace
                                    .withheld
                                    .get(&(member.text.clone(), WithheldNamespace::Constructor))
                            })
                            .copied(),
                    ));
                } else {
                    if let Some(kind) = self
                        .targeted_withheld
                        .get(&(member.text.clone(), WithheldNamespace::Term))
                        .or_else(|| {
                            self.targeted_withheld
                                .get(&(member.text.clone(), WithheldNamespace::Constructor))
                        })
                        .copied()
                    {
                        return Err(withheld_export_error(member.span, &member.text, Some(kind)));
                    }
                    return Err(
                        if member.text.chars().next().is_some_and(char::is_uppercase) {
                            let mut diagnostic = Diagnostic::new(
                                ResolveReason::UnknownConstructor,
                                SourceLabel::new(member.span, "this constructor is not declared"),
                            );
                            diagnostic.found = Some(member.text.clone());
                            ResolveError::from(diagnostic)
                        } else {
                            error(
                                ResolveReason::UnknownName,
                                member.span,
                                "this name is not in scope",
                            )
                        },
                    );
                }
            }
            SurfaceExprKind::Apply(application) => {
                tasks.push(ResolveTask::FinishApplication {
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitExpr(&application.argument));
                tasks.push(ResolveTask::VisitExpr(&application.function));
            }
            SurfaceExprKind::Add(binary) => {
                schedule_binary(BinaryKind::Add, expression.span, binary, tasks);
            }
            SurfaceExprKind::Multiply(binary) => {
                schedule_binary(BinaryKind::Multiply, expression.span, binary, tasks);
            }
            SurfaceExprKind::Equal(binary) => {
                schedule_binary(BinaryKind::Equal, expression.span, binary, tasks);
            }
            SurfaceExprKind::Block(block) => tasks.push(ResolveTask::VisitBlock(block)),
            SurfaceExprKind::Function(function) => {
                let (mut patterns, binders) =
                    self.resolve_pattern_vector(std::slice::from_ref(&function.parameter))?;
                let parameter = patterns.pop().ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        function.parameter.span,
                        "the resolver produced no function pattern",
                    )
                })?;
                let scope_checkpoint = self.scopes.len();
                self.push_binder_scope_many(&binders);
                tasks.push(ResolveTask::FinishFunction {
                    parameter,
                    scope_checkpoint,
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitBlock(&function.body));
            }
            SurfaceExprKind::Tuple(elements) => {
                tasks.push(ResolveTask::FinishTuple {
                    count: elements.len(),
                    span: expression.span,
                });
                tasks.extend(elements.iter().rev().map(ResolveTask::VisitExpr));
            }
            SurfaceExprKind::Match(match_expression) => {
                let scrutinee = self.resolve_expr(&match_expression.scrutinee)?;
                let mut arms = Vec::with_capacity(match_expression.arms.len());
                for arm in &match_expression.arms {
                    let scope_checkpoint = self.scopes.len();
                    let (mut patterns, binders) =
                        self.resolve_pattern_vector(std::slice::from_ref(&arm.pattern))?;
                    let pattern = patterns.pop().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            arm.span,
                            "the resolver produced no match pattern",
                        )
                    })?;
                    self.push_binder_scope_many(&binders);
                    let body = self.resolve_expr(&arm.body);
                    self.scopes.truncate(scope_checkpoint);
                    arms.push(ResolvedMatchArm {
                        pattern,
                        body: body?,
                        span: arm.span,
                    });
                }
                expressions.push(ResolvedExpr {
                    kind: ResolvedExprKind::Match(ResolvedMatchExpr {
                        scrutinee: Box::new(scrutinee),
                        arms,
                    }),
                    span: expression.span,
                });
            }
        }
        Ok(())
    }
}

enum ResolveTask<'a> {
    VisitExpr(&'a SurfaceExpr),
    VisitBlock(&'a SurfaceBlock),
    VisitRecursiveGroup(&'a SurfaceRecursiveGroup),
    FinishApplication {
        span: crate::source::Span,
    },
    FinishBinary {
        kind: BinaryKind,
        operator_span: crate::source::Span,
        span: crate::source::Span,
    },
    FinishBinding(&'a SurfaceBinding),
    FinishRecursiveGroup {
        group: &'a SurfaceRecursiveGroup,
        binders: Vec<Binder>,
    },
    FinishBlock {
        declaration_start: usize,
        scope_checkpoint: usize,
        span: crate::source::Span,
    },
    FinishFunction {
        parameter: ResolvedPattern,
        scope_checkpoint: usize,
        span: crate::source::Span,
    },
    FinishTuple {
        count: usize,
        span: crate::source::Span,
    },
}

impl ResolveTask<'_> {
    fn span(&self) -> crate::source::Span {
        match self {
            Self::VisitExpr(expression) => expression.span,
            Self::VisitBlock(block) => block.span,
            Self::VisitRecursiveGroup(group) => group.span,
            Self::FinishApplication { span }
            | Self::FinishBinary { span, .. }
            | Self::FinishBlock { span, .. }
            | Self::FinishFunction { span, .. }
            | Self::FinishTuple { span, .. } => *span,
            Self::FinishBinding(binding) => binding.span,
            Self::FinishRecursiveGroup { group, .. } => group.span,
        }
    }
}

#[derive(Clone, Copy)]
enum BinaryKind {
    Add,
    Multiply,
    Equal,
}

impl BinaryKind {
    fn finish(self, binary: ResolvedBinaryExpr) -> ResolvedExprKind {
        match self {
            Self::Add => ResolvedExprKind::Add(binary),
            Self::Multiply => ResolvedExprKind::Multiply(binary),
            Self::Equal => ResolvedExprKind::Equal(binary),
        }
    }
}

fn schedule_binary<'a>(
    kind: BinaryKind,
    span: crate::source::Span,
    binary: &'a BinaryExpr,
    tasks: &mut Vec<ResolveTask<'a>>,
) {
    tasks.push(ResolveTask::FinishBinary {
        kind,
        operator_span: binary.operator_span,
        span,
    });
    tasks.push(ResolveTask::VisitExpr(&binary.right));
    tasks.push(ResolveTask::VisitExpr(&binary.left));
}

fn take_expression_pair(
    expressions: &mut Vec<ResolvedExpr>,
    span: crate::source::Span,
) -> Result<(ResolvedExpr, ResolvedExpr), ResolveError> {
    let Some(right) = expressions.pop() else {
        return Err(error(
            ResolveReason::InternalState,
            span,
            "the resolver lost a right operand",
        ));
    };
    let Some(left) = expressions.pop() else {
        return Err(error(
            ResolveReason::InternalState,
            span,
            "the resolver lost a left operand",
        ));
    };
    Ok((left, right))
}

fn error(reason: ResolveReason, span: crate::source::Span, message: &str) -> ResolveError {
    Diagnostic::new(reason, SourceLabel::new(span, message)).into()
}

fn import_conflict(span: crate::source::Span, spelling: &str) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::ImportConflict,
        SourceLabel::new(span, "this file-wide name is already bound"),
    );
    diagnostic.found = Some(spelling.to_owned());
    diagnostic.into()
}

fn withheld_export_error(
    span: crate::source::Span,
    spelling: &str,
    withheld: Option<WithheldImport>,
) -> ResolveError {
    let (reason, message) = match withheld.map(|withheld| withheld.kind) {
        Some(WithheldExportKind::Private) => (
            ResolveReason::UnavailableExport,
            "this declaration is private to its defining module",
        ),
        Some(WithheldExportKind::OpaqueConstructor) => (
            ResolveReason::OpaqueConstructor,
            "this constructor belongs to an opaque type",
        ),
        None => (
            ResolveReason::UnavailableExport,
            "the dependency exports no declaration with this spelling",
        ),
    };
    let mut diagnostic = Diagnostic::new(reason, SourceLabel::new(span, message));
    if let Some(declaration) = withheld.and_then(|withheld| withheld.declaration) {
        diagnostic.related.push(SourceLabel::new(
            declaration,
            "the inaccessible declaration is here",
        ));
    }
    diagnostic.found = Some(spelling.to_owned());
    diagnostic.into()
}

fn type_argument_count(
    span: crate::source::Span,
    spelling: &str,
    expected: usize,
    found: usize,
) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::TypeArgumentCount,
        SourceLabel::new(span, "this nominal type has the wrong number of arguments"),
    );
    diagnostic.expected = Some(format!("{spelling} with {expected} type arguments"));
    diagnostic.found = Some(found.to_string());
    diagnostic.into()
}

fn unknown_interface_error(span: crate::source::Span, spelling: &str) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::UnknownInterface,
        SourceLabel::new(span, "this interface is not declared"),
    );
    diagnostic.found = Some(spelling.to_owned());
    diagnostic.into()
}

fn interface_kind_error(span: crate::source::Span, spelling: &str) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::InterfaceKind,
        SourceLabel::new(span, "this name does not denote an interface"),
    );
    diagnostic.expected = Some("interface".to_owned());
    diagnostic.found = Some(spelling.to_owned());
    diagnostic.into()
}

fn type_kind_error(span: crate::source::Span, spelling: &str) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::TypeKind,
        SourceLabel::new(span, "an interface cannot be used as a value type"),
    );
    diagnostic.expected = Some("type".to_owned());
    diagnostic.found = Some(spelling.to_owned());
    diagnostic.into()
}

fn collect_free_type_names<'a>(
    root: &'a SurfaceType,
    nominals: &HashMap<String, NominalTypeId>,
    interfaces: &HashMap<String, InterfaceId>,
    seen: &mut HashSet<&'a str>,
    output: &mut Vec<crate::surface::SurfaceName>,
    budget: &mut TypeWorkBudget,
) -> Result<(), ResolveError> {
    enum Task<'a> {
        Visit(&'a SurfaceType),
        Slice(std::slice::Iter<'a, SurfaceType>),
    }

    let mut work = vec![Task::Visit(root)];
    while let Some(task) = work.pop() {
        let Task::Visit(ty) = task else {
            let Task::Slice(mut remaining) = task else {
                unreachable!("free type discovery task is closed")
            };
            if let Some(next) = remaining.next() {
                work.push(Task::Slice(remaining));
                work.push(Task::Visit(next));
            }
            continue;
        };
        budget.charge(1).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                ty.span,
                "free type discovery exceeded its work budget",
            )
        })?;
        match &ty.kind {
            SurfaceTypeKind::Named(name) => {
                let SurfaceReference::Unqualified(name) = name else {
                    continue;
                };
                if !nominals.contains_key(&name.text)
                    && !interfaces.contains_key(&name.text)
                    && seen.insert(&name.text)
                {
                    output.push(name.clone());
                }
            }
            SurfaceTypeKind::Application {
                constructor,
                arguments,
            } => {
                if let SurfaceReference::Unqualified(constructor) = constructor
                    && !nominals.contains_key(&constructor.text)
                    && !interfaces.contains_key(&constructor.text)
                    && seen.insert(&constructor.text)
                {
                    output.push(constructor.clone());
                }
                work.push(Task::Slice(arguments.iter()));
            }
            SurfaceTypeKind::Tuple(elements) => work.push(Task::Slice(elements.iter())),
            SurfaceTypeKind::Function(function) => {
                work.push(Task::Visit(&function.codomain));
                work.push(Task::Visit(&function.domain));
            }
            SurfaceTypeKind::Int | SurfaceTypeKind::Bool | SurfaceTypeKind::Unit => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod module_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::{ByteRange, SourceFile};
    use crate::surface::{SurfaceDefinitionKind, SurfaceName, SurfaceTypeKind};
    use crate::types::TYPE_WORK_LIMIT;
    use crate::{
        lexer::lex,
        parser::{parse, project_module},
    };

    #[test]
    fn binder_identity_allocation_reports_exhaustion_without_wrapping() {
        let source =
            SourceFile::new("exhaustion.ash", "name").expect("the allocator fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let mut resolver = Resolver::new(ModuleId::new(0));
        resolver.next_binder = u32::MAX;

        let error = resolver
            .allocate_binder("name", span)
            .expect_err("the reserved exhaustion sentinel must not be exposed");

        assert_eq!(error.reason, ResolveReason::BinderIdExhausted);
        assert_eq!(resolver.next_binder, u32::MAX);
    }

    #[test]
    fn hidden_impl_binder_exhaustion_precedes_global_body_resolution() {
        let text = "interface Convert<A> {\nconvert : A -> A\n}\n\nbefore : Int -> Int\nbefore value = missing\n\nimpl Convert<Int> {\nconvert value = value\n}\n";
        let source = SourceFile::new("hidden-exhaustion.ash", text)
            .expect("the exhaustion fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let module = project_module(&source, &tree).expect("the fixture should project");
        let mut resolver = Resolver::new(ModuleId::new(0));
        resolver.next_binder = u32::MAX - 1;
        resolver
            .validate_local_namespaces(&module)
            .expect("the fixture namespaces should be distinct");

        let error = match resolver.resolve_declarations(&module) {
            Err(error) => error,
            Ok(_) => panic!("the hidden binder should exhaust before body resolution"),
        };

        assert_eq!(error.reason, ResolveReason::BinderIdExhausted);
        assert_eq!(resolver.next_binder, u32::MAX);
    }

    #[test]
    fn failed_nested_and_recursive_resolution_restore_the_scope_stack() {
        for (name, text) in [
            (
                "scope-error.ash",
                "main : Unit -> Unit\nmain () = fn(value) {\n{\nmissing\n}\n}\n",
            ),
            (
                "recursive-scope-error.ash",
                "main : Unit -> Int\nmain () = {\nlet rec repeat : Unit -> Int = fn(ignored) {\nmissing\n}\nrepeat ()\n}\n",
            ),
        ] {
            let source = SourceFile::new(name, text).expect("the scope fixture should fit");
            let tree = parse(lex(&source).expect("the fixture should lex"));
            let module = project_module(&source, &tree).expect("the fixture should project");
            let SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
                panic!("the fixture should expose an equational main");
            };
            let body = &main.equations[0].body;
            let mut resolver = Resolver::new(ModuleId::new(0));
            let initial_scope_count = resolver.scopes.len();

            let error = resolver
                .resolve_expr(body)
                .expect_err("the nested unknown name should fail");

            assert_eq!(error.reason, ResolveReason::UnknownName);
            assert_eq!(resolver.scopes.len(), initial_scope_count);
        }
    }

    #[test]
    fn free_type_discovery_charges_before_retaining_each_name() {
        let source = SourceFile::new("free-type-budget.ash", "A B C")
            .expect("the budget fixture should fit");
        let name = |text: &str, start, end| {
            let span = source
                .span(ByteRange::new(start, end).expect("the range is ordered"))
                .expect("the range belongs to the fixture");
            SurfaceType {
                kind: SurfaceTypeKind::Named(SurfaceReference::Unqualified(SurfaceName {
                    text: text.to_owned(),
                    span,
                })),
                span,
            }
        };
        let annotation = SurfaceType {
            kind: SurfaceTypeKind::Tuple(vec![name("A", 0, 1), name("B", 2, 3), name("C", 4, 5)]),
            span: source
                .span(ByteRange::new(0, 5).expect("the range is ordered"))
                .expect("the range belongs to the fixture"),
        };
        let mut budget = TypeWorkBudget::default();
        budget
            .charge(TYPE_WORK_LIMIT - 2)
            .expect("the fixture leaves two units");
        let mut seen = HashSet::new();
        let mut output = Vec::new();

        let error = collect_free_type_names(
            &annotation,
            &HashMap::new(),
            &HashMap::new(),
            &mut seen,
            &mut output,
            &mut budget,
        )
        .expect_err("the second name exceeds the remaining budget");

        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(error.primary.span().range().start(), 2);
        assert_eq!(error.primary.span().range().end(), 3);
        assert_eq!(
            output
                .iter()
                .map(|name| name.text.as_str())
                .collect::<Vec<_>>(),
            ["A"]
        );
        assert_eq!(seen, HashSet::from(["A"]));
    }

    #[test]
    fn constructor_tuple_payloads_charge_the_synthesized_wrapper_exactly() {
        let source = SourceFile::new(
            "constructor-tuple-budget.ash",
            "type Pair =\nPair(Int, Int)\n",
        )
        .expect("the budget fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let module = project_module(&source, &tree).expect("the fixture should project");
        let second_field_span = module.type_declarations[0].constructors[0].fields[1].span;

        let mut exact = Resolver::new(ModuleId::new(0));
        exact
            .type_work
            .charge(TYPE_WORK_LIMIT - 3)
            .expect("the fixture leaves the wrapper and two field cells");
        let registry = exact
            .resolve_registry(&module.type_declarations)
            .expect("the exact constructor payload allowance should fit");
        assert_eq!(
            registry.constructors()[0].payload,
            Some(Type::Tuple(vec![Type::Int, Type::Int].into_boxed_slice()))
        );
        assert_eq!(exact.type_work.charge(1), Err(()));

        let mut short = Resolver::new(ModuleId::new(0));
        short
            .type_work
            .charge(TYPE_WORK_LIMIT - 2)
            .expect("the fixture leaves one cell fewer than the retained payload");
        let error = short
            .resolve_registry(&module.type_declarations)
            .expect_err("the tuple wrapper must consume the remaining budget");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(error.primary.span().range(), second_field_span.range());
    }

    #[test]
    fn wide_tuple_resolution_keeps_pending_type_work_constant_width() {
        const WIDTH: usize = 4_096;

        let source =
            SourceFile::new("wide-tuple-budget.ash", "Int").expect("the budget fixture should fit");
        let span = source
            .span(ByteRange::new(0, 3).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let int = SurfaceType {
            kind: SurfaceTypeKind::Int,
            span,
        };
        let annotation = SurfaceType {
            kind: SurfaceTypeKind::Tuple(vec![int; WIDTH]),
            span,
        };
        let mut resolver = Resolver::new(ModuleId::new(0));
        resolver
            .type_work
            .charge(TYPE_WORK_LIMIT - 1)
            .expect("the fixture leaves one unit for the tuple root");

        let error = resolver
            .resolve_type(&annotation)
            .expect_err("the first tuple field exceeds the remaining budget");

        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert!(
            resolver.max_type_pending_tasks <= 3,
            "wide tuples retained {} pending resolver tasks",
            resolver.max_type_pending_tasks
        );
    }

    #[test]
    fn wide_nominal_application_resolution_keeps_pending_type_work_constant_width() {
        const WIDTH: usize = 4_096;

        let source = SourceFile::new("wide-application-budget.ash", "Wide<Int>")
            .expect("the budget fixture should fit");
        let full_span = source
            .span(ByteRange::new(0, 9).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let constructor_span = source
            .span(ByteRange::new(0, 4).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let argument_span = source
            .span(ByteRange::new(5, 8).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let owner = NominalTypeId::new(source.id(), 0);
        let argument = SurfaceType {
            kind: SurfaceTypeKind::Int,
            span: argument_span,
        };
        let annotation = SurfaceType {
            kind: SurfaceTypeKind::Application {
                constructor: SurfaceReference::Unqualified(SurfaceName {
                    text: "Wide".to_owned(),
                    span: constructor_span,
                }),
                arguments: vec![argument; WIDTH],
            },
            span: full_span,
        };
        let mut resolver = Resolver::new(ModuleId::new(0));
        resolver.type_names.insert("Wide".to_owned(), owner);
        resolver.nominal_parameter_counts.insert(owner, WIDTH);
        resolver
            .type_work
            .charge(TYPE_WORK_LIMIT - 1)
            .expect("the fixture leaves one unit for the application root");

        let error = resolver
            .resolve_type(&annotation)
            .expect_err("the first nominal argument exceeds the remaining budget");

        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(error.primary.span(), argument_span);
        assert!(
            resolver.max_type_pending_tasks <= 3,
            "wide applications retained {} pending resolver tasks",
            resolver.max_type_pending_tasks
        );
    }
}
