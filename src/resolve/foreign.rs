//! Borrowed declaration views keep native symbols in the ordinary effect path.

use std::{collections::HashMap, ops::Range, sync::Arc};

use super::{
    DependencyExports, ResolveError, ResolveReason, ResolvedDeclarations, Resolver, error,
    retain_declaration_order,
};
use crate::foreign::{
    checked_source::{
        ForeignBindingContext, ForeignCallCodecIds, NativeLibraryId, bind_foreign_symbol,
    },
    source_contract::{PreparedForeignLibrary, prepare_foreign_library_with_budget},
};
use crate::{
    diagnostic::{Diagnostic, SourceLabel},
    resolved::ResolvedBuildFailure,
    source::Span,
    surface::{
        SurfaceDeclarationIndex, SurfaceEffectDeclaration, SurfaceForeignMember,
        SurfaceForeignSymbol, SurfaceModule, SurfaceName, SurfaceType, SurfaceTypeParameter,
    },
    types::{ConstructorId, NominalTypeId, TypeWorkBudget},
};

pub(super) struct PreparedLibrarySource {
    pub(super) prepared: Arc<PreparedForeignLibrary>,
    effects: Range<usize>,
}

#[derive(Clone, Copy)]
pub(super) enum EffectSource<'a> {
    Ordinary(&'a SurfaceEffectDeclaration),
    Foreign {
        public: bool,
        symbol: &'a SurfaceForeignSymbol,
    },
}

#[derive(Clone, Copy)]
pub(super) struct OperationSource<'a> {
    pub(super) spelling: &'a str,
    pub(super) name_span: Span,
    pub(super) annotation: &'a SurfaceType,
    pub(super) span: Span,
}

impl EffectSource<'_> {
    pub(super) fn name(&self) -> &SurfaceName {
        match self {
            Self::Ordinary(source) => &source.name,
            Self::Foreign { symbol, .. } => &symbol.name,
        }
    }

    pub(super) fn parameters(&self) -> &[SurfaceTypeParameter] {
        match self {
            Self::Ordinary(source) => &source.parameters,
            Self::Foreign { symbol, .. } => &symbol.parameters,
        }
    }

    pub(super) fn public(&self) -> bool {
        match self {
            Self::Ordinary(source) => source.public,
            Self::Foreign { public, .. } => *public,
        }
    }

    pub(super) fn span(&self) -> Span {
        match self {
            Self::Ordinary(source) => source.span,
            Self::Foreign { symbol, .. } => symbol.span,
        }
    }

    pub(super) fn origin_span(&self) -> Span {
        match self {
            Self::Ordinary(source) => source.name.span,
            Self::Foreign { symbol, .. } => symbol.span,
        }
    }

    pub(super) fn operation_count(&self) -> usize {
        match self {
            Self::Ordinary(source) => source.operations.len(),
            Self::Foreign { .. } => 1,
        }
    }

    pub(super) fn operation(&self, index: usize) -> Option<OperationSource<'_>> {
        match self {
            Self::Ordinary(source) => {
                source
                    .operations
                    .get(index)
                    .map(|operation| OperationSource {
                        spelling: &operation.name.text,
                        name_span: operation.name.span,
                        annotation: &operation.annotation,
                        span: operation.span,
                    })
            }
            Self::Foreign { symbol, .. } if index == 0 => Some(OperationSource {
                spelling: "call",
                name_span: symbol.name.span,
                annotation: &symbol.ty,
                span: symbol.span,
            }),
            Self::Foreign { .. } => None,
        }
    }
}

impl Resolver {
    pub(super) fn bind_scalar_preflights(
        &mut self,
        loaded: &crate::module::LoadedModule,
        declarations: &mut ResolvedDeclarations,
    ) -> Result<(), ResolveError> {
        if !self.module.is_builtin_foreign() {
            return Ok(());
        }
        use crate::foreign::{
            checked_source::CheckedForeignCallCodec,
            scalar_preflight::{CheckedForeignScalarPreflight, ForeignScalarPreflightRole},
        };
        use crate::resolved::{BinderId, ResolvedDefinitionKind};
        let source = loaded.source();
        let range = u32::try_from(source.text().len())
            .ok()
            .and_then(|len| crate::source::ByteRange::new(0, len).ok())
            .ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    loaded.surface().span,
                    "builtin foreign source range is invalid",
                )
            })?;
        let span = source.span(range).map_err(|_| {
            error(
                ResolveReason::InternalState,
                loaded.surface().span,
                "builtin foreign source provenance is invalid",
            )
        })?;
        let registry = Arc::get_mut(&mut declarations.registry).ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                span,
                "scalar preflight publication requires its original unique registry",
            )
        })?;
        let call = NominalTypeId::new(self.module, 1);
        let codec = CheckedForeignCallCodec::authenticate(
            self.module,
            span,
            ForeignCallCodecIds {
                call,
                returned: ConstructorId::new(call, 0),
                conversion_failed: ConstructorId::new(call, 1),
                conversion_error: NominalTypeId::new(self.module, 0),
            },
            registry,
            &mut self.type_work,
        )
        .map_err(source_admission_failure)?;
        self.type_work.charge(3).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "scalar preflight facts exceeded their work budget",
            )
        })?;
        let codec = Arc::new(codec);
        if declarations.definitions.len() != 10 {
            return Err(error(
                ResolveReason::InternalState,
                span,
                "builtin scalar preflight declaration inventory is invalid",
            ));
        }
        for (definition, role) in declarations.definitions.iter().zip([
            ForeignScalarPreflightRole::I64,
            ForeignScalarPreflightRole::SizeT,
            ForeignScalarPreflightRole::ByteRead,
            ForeignScalarPreflightRole::ByteWrite,
            ForeignScalarPreflightRole::Nul,
            ForeignScalarPreflightRole::DataOf,
            ForeignScalarPreflightRole::ReplaceData,
            ForeignScalarPreflightRole::CopyBytes,
            ForeignScalarPreflightRole::CopyNul,
            ForeignScalarPreflightRole::ExtentValue,
        ]) {
            let ResolvedDefinitionKind::Equational(global) = &definition.kind else {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "builtin scalar preflight header is invalid",
                ));
            };
            if global.interface.name.id != BinderId::resolved(self.module, role.local())
                || match role.borrowed_parameter(self.module) {
                    None => !global.interface.type_parameters.is_empty(),
                    Some(expected) => {
                        let parameters = &global.interface.type_parameters;
                        let (name, _) =
                            crate::module::foreign_scalar_preflight_ranges(span, role.local())
                                .ok_or_else(|| {
                                    error(
                                        ResolveReason::InternalState,
                                        span,
                                        "sealed byte declaration range is invalid",
                                    )
                                })?;
                        parameters.len() != 1 + usize::from(role.data_parameter(self.module).is_some())
                            || parameters[0].id != expected
                            || parameters[0].kind != crate::types::Kind::Type
                            || !matches!(&parameters[0].origin, crate::source::Origin::Source(parameter) if parameter.source() == span.source() && parameter.range().start() == name.end()+1 && parameter.range().end() == name.end()+2)
                            || role.data_parameter(self.module).is_some_and(|expected| parameters.get(1).is_none_or(|parameter| parameter.id != expected || parameter.kind != crate::types::Kind::Type || !matches!(&parameter.origin, crate::source::Origin::Source(origin) if origin.source() == span.source() && origin.range().start() == name.end()+4 && origin.range().end() == name.end()+5)))
                    }
                }
                || !global.interface.requirements.is_empty()
            {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "builtin scalar preflight binder inventory is invalid",
                ));
            }
            let fact = CheckedForeignScalarPreflight::from_original(
                role,
                span,
                &global.interface.name.origin,
                &global.interface.annotation,
                Arc::clone(&codec),
                &mut self.type_work,
            )
            .map_err(source_admission_failure)?;
            registry
                .retain_scalar_preflight(Arc::new(fact), &mut self.type_work)
                .map_err(|failure| source_build_failure(failure, span))?;
        }
        Ok(())
    }

    pub(super) fn validate_source_foreign_members(
        &mut self,
        surface: &SurfaceModule,
    ) -> Result<(), ResolveError> {
        let mut names = HashMap::new();
        for library in &surface.foreign_libraries {
            self.type_work.charge(library.members.len()).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    library.span,
                    "foreign member collision checking exceeded its work budget",
                )
            })?;
            names.try_reserve(library.members.len()).map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    library.span,
                    "foreign member collision storage could not be reserved",
                )
            })?;
            for member in &library.members {
                let name = match member {
                    SurfaceForeignMember::Profile(_) | SurfaceForeignMember::Assumption(_) => {
                        continue;
                    }
                    SurfaceForeignMember::Representation(member) => &member.name,
                    SurfaceForeignMember::Constant(member) => &member.name,
                    SurfaceForeignMember::Sentinel(member) => &member.name,
                    SurfaceForeignMember::Owner(member) => &member.name,
                    SurfaceForeignMember::Access(member) => &member.name,
                    SurfaceForeignMember::Symbol(member) => &member.name,
                };
                self.type_work.charge(name.text.len()).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        name.span,
                        "foreign member spelling comparison exceeded its work budget",
                    )
                })?;
                if let Some(first) = names.insert(name.text.as_str(), name.span) {
                    let mut diagnostic = Diagnostic::new(
                        ResolveReason::ForeignContract,
                        SourceLabel::new(
                            name.span,
                            "foreign libraries in one module require disjoint member spellings",
                        ),
                    );
                    diagnostic
                        .related
                        .push(SourceLabel::new(first, "the first foreign member is here"));
                    return Err(diagnostic.into());
                }
            }
        }
        Ok(())
    }

    pub(super) fn prepare_source_foreign(
        &mut self,
        surface: &SurfaceModule,
    ) -> Result<Vec<PreparedLibrarySource>, ResolveError> {
        let mut prepared = Vec::new();
        self.type_work
            .charge(surface.foreign_libraries.len())
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign library preparation exceeded its work budget",
                )
            })?;
        prepared
            .try_reserve_exact(surface.foreign_libraries.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign library preparation storage could not be reserved",
                )
            })?;
        // Ordinary effects and whole library symbol groups share one source-order
        // identity inventory. This additional walk applies only to foreign graphs.
        if !surface.foreign_libraries.is_empty() {
            self.type_work.charge(surface.effects.len()).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign effect ordering exceeded its work budget",
                )
            })?;
        }
        let mut ordinary = surface.effects.iter().peekable();
        let mut next_effect = 0_usize;
        for library in &surface.foreign_libraries {
            self.type_work.charge(library.members.len()).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    library.span,
                    "foreign publication classification exceeded its work budget",
                )
            })?;
            self.type_work.charge(library.members.len()).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    library.span,
                    "foreign owner classification exceeded its work budget",
                )
            })?;
            let has_owner = library
                .members
                .iter()
                .any(|member| matches!(member, SurfaceForeignMember::Owner(_)));
            // Scalar literals share ordinary Int publication. Native operands
            // keep their original checked representation and member coordinate.
            if let Some((span, message)) = library.members.iter().find_map(|member| match member {
                SurfaceForeignMember::Representation(representation)
                    if !has_owner
                        && matches!(
                            representation.representation,
                            crate::surface::SurfaceForeignRepresentation::Opaque(_)
                                | crate::surface::SurfaceForeignRepresentation::Bytes(_)
                        ) =>
                {
                    Some((
                        representation.span,
                        "source foreign addresses require canonical owner admission",
                    ))
                }
                _ => None,
            }) {
                return Err(error(ResolveReason::ForeignContract, span, message));
            }
            let facts =
                prepare_foreign_library_with_budget(self.module, library, &mut self.type_work)
                    .map_err(|failure| {
                        error(
                            if failure.is_resource_exhaustion() {
                                ResolveReason::TypeResourceExhausted
                            } else {
                                ResolveReason::ForeignContract
                            },
                            failure.span(),
                            &failure.to_string(),
                        )
                    })?;
            while ordinary
                .peek()
                .is_some_and(|effect| effect.span.range().start() < library.span.range().start())
            {
                ordinary.next();
                next_effect = next_effect.checked_add(1).ok_or_else(|| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        library.span,
                        "foreign effect inventory exceeded its bound",
                    )
                })?;
            }
            let end = next_effect
                .checked_add(facts.symbols().len())
                .ok_or_else(|| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        library.span,
                        "foreign effect inventory exceeded its bound",
                    )
                })?;
            prepared.push(PreparedLibrarySource {
                prepared: Arc::new(facts),
                effects: next_effect..end,
            });
            next_effect = end;
        }
        Ok(prepared)
    }

    pub(super) fn bind_source_foreign(
        &mut self,
        surface: &SurfaceModule,
        prepared: &[PreparedLibrarySource],
        declarations: &mut ResolvedDeclarations,
        dependencies: &[DependencyExports<'_>],
    ) -> Result<(), ResolveError> {
        self.type_work.charge(prepared.len()).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                surface.span,
                "foreign symbol inventory classification exceeded its work budget",
            )
        })?;
        if prepared.iter().all(|library| library.effects.is_empty()) {
            return Ok(());
        }
        let mut common = None;
        for dependency in dependencies {
            self.type_work
                .charge(dependency.summary.defining_sources().len())
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        surface.span,
                        "foreign common provenance lookup exceeded its work budget",
                    )
                })?;
            for (module, source) in dependency.summary.defining_sources() {
                if module.is_builtin_foreign() {
                    let len = u32::try_from(source.text().len()).map_err(|_| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "foreign common source exceeds its admitted bound",
                        )
                    })?;
                    let span = source
                        .span(crate::source::ByteRange::new(0, len).map_err(|_| {
                            error(
                                ResolveReason::InternalState,
                                surface.span,
                                "foreign common source range is invalid",
                            )
                        })?)
                        .map_err(|_| {
                            error(
                                ResolveReason::InternalState,
                                surface.span,
                                "foreign common source provenance is invalid",
                            )
                        })?;
                    if common.is_some_and(|previous| previous != (*module, span)) {
                        return Err(error(
                            ResolveReason::ForeignContract,
                            surface.span,
                            "foreign common types have inconsistent defining authority",
                        ));
                    }
                    common = Some((*module, span));
                }
            }
        }
        let (common_module, common_span) = common.ok_or_else(|| {
            error(
                ResolveReason::ForeignContract,
                surface.span,
                "foreign symbols require the canonical @builtin.foreign result types",
            )
        })?;
        let registry = declarations
            .registry
            .checker_view(&self.imported, &mut self.type_work)
            .map_err(|failure| source_build_failure(failure, surface.span))?;
        let call = NominalTypeId::new(common_module, 1);
        let ids = ForeignCallCodecIds {
            call,
            returned: ConstructorId::new(call, 0),
            conversion_failed: ConstructorId::new(call, 1),
            conversion_error: NominalTypeId::new(common_module, 0),
        };
        let mut owners = Vec::new();
        for (ordinal, library) in prepared.iter().enumerate() {
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    surface.span,
                    "foreign library identity exhausted",
                )
            })?;
            self.type_work
                .charge(library.prepared.owners().len())
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        surface.span,
                        "foreign owner binding exceeded its work budget",
                    )
                })?;
            owners
                .try_reserve(library.prepared.owners().len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        surface.span,
                        "foreign owner binding storage could not be reserved",
                    )
                })?;
            for index in 0..library.prepared.owners().len() {
                self.type_work
                    .charge(registry.source_owner_candidate_count())
                    .map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            surface.span,
                            "foreign owner candidate lookup exceeded its work budget",
                        )
                    })?;
                let (nominal, parameters) = registry
                    .source_owner_candidate(&library.prepared, index)
                    .ok_or_else(|| {
                        error(
                            ResolveReason::ForeignContract,
                            surface.span,
                            "foreign owner has no original canonical nominal",
                        )
                    })?;
                owners.push(Arc::new(
                    crate::foreign::source_owner::bind_foreign_owner(
                        NativeLibraryId::new(self.module, ordinal),
                        Arc::clone(&library.prepared),
                        index,
                        nominal,
                        parameters,
                        &registry,
                        &mut self.type_work,
                    )
                    .map_err(source_admission_failure)?,
                ));
            }
        }
        let mut accesses = Vec::new();
        for (ordinal, library) in prepared.iter().enumerate() {
            self.type_work
                .charge(library.prepared.accesses().len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        surface.span,
                        "source access binding exceeded work",
                    )
                })?;
            accesses
                .try_reserve(library.prepared.accesses().len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        surface.span,
                        "source access binding storage refused",
                    )
                })?;
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "source library identity exceeded bound",
                )
            })?;
            for index in 0..library.prepared.accesses().len() {
                self.type_work
                    .charge(registry.source_foreign_nominal_count())
                    .map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            surface.span,
                            "source access lookup exceeded work",
                        )
                    })?;
                let (nominal, parameters) = registry
                    .source_access_candidate(&library.prepared, index)
                    .ok_or_else(|| {
                        error(
                            ResolveReason::ForeignContract,
                            surface.span,
                            "source access has no original nominal",
                        )
                    })?;
                accesses.push(Arc::new(
                    crate::foreign::source_access::bind_foreign_access(
                        NativeLibraryId::new(self.module, ordinal),
                        Arc::clone(&library.prepared),
                        index,
                        nominal,
                        parameters,
                        &registry,
                        &mut self.type_work,
                    )
                    .map_err(source_admission_failure)?,
                ));
            }
        }
        let context = ForeignBindingContext::new(
            &registry,
            common_module,
            common_span,
            ids,
            &mut self.type_work,
        )
        .map_err(source_admission_failure)?
        .with_owners(&owners, &mut self.type_work)
        .map_err(source_admission_failure)?;
        let mut symbols = Vec::new();
        for (ordinal, library) in prepared.iter().enumerate() {
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    surface.span,
                    "foreign library identity exhausted",
                )
            })?;
            self.type_work.charge(library.effects.len()).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign symbol retention exceeded its work budget",
                )
            })?;
            symbols.try_reserve(library.effects.len()).map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign symbol retention storage could not be reserved",
                )
            })?;
            for (index, effect_index) in library.effects.clone().enumerate() {
                let effect_id = declarations
                    .effects
                    .get(effect_index)
                    .ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "foreign effect inventory lost its declaration",
                        )
                    })?
                    .id;
                let original = registry.effect(effect_id).ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        surface.span,
                        "foreign effect inventory lost its registry original",
                    )
                })?;
                symbols.push((
                    effect_index,
                    Arc::new(
                        bind_foreign_symbol(
                            NativeLibraryId::new(self.module, ordinal),
                            Arc::clone(&library.prepared),
                            index,
                            original,
                            &context,
                            &mut self.type_work,
                        )
                        .map_err(source_admission_failure)?,
                    ),
                ));
            }
        }
        drop(context);
        drop(registry);
        let registry = Arc::get_mut(&mut declarations.registry).ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                surface.span,
                "source foreign publication requires its unique defining registry",
            )
        })?;
        registry
            .retain_source_accesses(&accesses, &mut self.type_work)
            .map_err(|failure| source_build_failure(failure, surface.span))?;
        for (effect_index, symbol) in symbols {
            declarations.effects[effect_index].native_contract = Some(Arc::clone(&symbol));
            registry
                .retain_native_symbol(symbol, &mut self.type_work)
                .map_err(|failure| source_build_failure(failure, surface.span))?;
        }
        Ok(())
    }

    pub(super) fn append_source_constant_definitions(
        &mut self,
        surface: &SurfaceModule,
        binders: Vec<crate::resolved::Binder>,
        definitions: &mut super::ResolvedDefinitionBuffer,
    ) -> Result<(), ResolveError> {
        use crate::resolved::{
            ResolvedDefinition, ResolvedDefinitionKind, ResolvedEquation, ResolvedEquationHead,
            ResolvedEquationalGlobal, ResolvedExpr, ResolvedExprKind, ResolvedExternalInterface,
            ResolvedType, ResolvedTypeProvenance, ResolvedTypeProvenanceNode,
        };
        self.type_work
            .charge(binders.len().saturating_mul(5))
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign constant lowering exceeded its budget",
                )
            })?;
        definitions
            .0
            .try_reserve_exact(binders.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign constant definition storage could not be reserved",
                )
            })?;
        let mut binders = binders.into_iter();
        for library in &self.source_foreign_libraries {
            for constant in library.constants() {
                let binder = binders.next().ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        surface.span,
                        "foreign constant binder is missing",
                    )
                })?;
                let span = constant.origin().primary_span();
                let scalar = constant.value();
                let value = scalar.checked_integer().ok_or_else(|| {
                    error(
                        ResolveReason::ForeignContract,
                        span,
                        "checked foreign constant value is invalid",
                    )
                })?;
                self.type_work.charge(constant.name().len()).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "foreign constant spelling copy exceeded its budget",
                    )
                })?;
                let mut spelling = String::new();
                spelling
                    .try_reserve_exact(constant.name().len())
                    .map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "foreign constant spelling storage could not be reserved",
                        )
                    })?;
                spelling.push_str(constant.name());
                let mut provenance = Vec::new();
                provenance.try_reserve_exact(1).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "foreign constant provenance storage could not be reserved",
                    )
                })?;
                provenance.push(ResolvedTypeProvenanceNode::Fact(span));
                let mut equations = Vec::new();
                equations.try_reserve_exact(1).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "foreign constant equation storage could not be reserved",
                    )
                })?;
                equations.push(ResolvedEquation {
                    name: ResolvedEquationHead {
                        binder: binder.id,
                        spelling,
                        origin: binder.origin.clone(),
                    },
                    patterns: Vec::new(),
                    body: ResolvedExpr {
                        kind: ResolvedExprKind::Integer(value),
                        span,
                    },
                    span,
                });
                definitions.0.push(ResolvedDefinition {
                    kind: ResolvedDefinitionKind::ForeignConstant(ResolvedEquationalGlobal {
                        interface: ResolvedExternalInterface {
                            name: binder,
                            annotation: ResolvedType {
                                ty: crate::types::Type::Int,
                                provenance: ResolvedTypeProvenance::new(provenance, 0),
                                origin: constant.origin().clone(),
                                span,
                            },
                            requirements: Box::new([]),
                            type_parameters: Box::new([]),
                            span,
                        },
                        equations,
                    }),
                    span,
                });
            }
        }
        if binders.next().is_some() {
            return Err(error(
                ResolveReason::InternalState,
                surface.span,
                "foreign constant binders disagree",
            ));
        }
        Ok(())
    }

    pub(super) fn order_source_constant_definitions(
        &mut self,
        surface: &SurfaceModule,
        definitions: &mut super::ResolvedDefinitionBuffer,
    ) -> Result<(), ResolveError> {
        if definitions.0.len() == surface.definitions.len() {
            return Ok(());
        }
        let count = definitions.0.len();
        self.type_work
            .charge(
                count
                    .checked_mul(4)
                    .and_then(|n| n.checked_add(surface.declaration_order.len()))
                    .ok_or_else(|| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            surface.span,
                            "foreign constant ordering exceeded its bound",
                        )
                    })?,
            )
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign constant ordering exceeded its budget",
                )
            })?;
        let mut destinations = Vec::new();
        destinations.try_reserve_exact(count).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                surface.span,
                "foreign constant ordering storage could not be reserved",
            )
        })?;
        destinations.resize(count, usize::MAX);
        let mut next = 0;
        let mut constant = surface.definitions.len();
        for declaration in &surface.declaration_order {
            let mut place = |original: usize| -> Result<(), ResolveError> {
                let slot = destinations.get_mut(original).ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        surface.span,
                        "foreign constant declaration index is invalid",
                    )
                })?;
                if *slot != usize::MAX {
                    return Err(error(
                        ResolveReason::InternalState,
                        surface.span,
                        "foreign constant declaration index repeats",
                    ));
                }
                *slot = next;
                next += 1;
                Ok(())
            };
            match *declaration {
                SurfaceDeclarationIndex::Global(index) => place(index)?,
                SurfaceDeclarationIndex::ForeignLibrary(index) => {
                    let library = self.source_foreign_libraries.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "foreign constant library index is invalid",
                        )
                    })?;
                    for _ in library.constants() {
                        place(constant)?;
                        constant += 1;
                    }
                }
                _ => {}
            }
        }
        if next != count || destinations.iter().any(|position| *position >= count) {
            return Err(error(
                ResolveReason::InternalState,
                surface.span,
                "foreign constant declaration order is incomplete",
            ));
        }
        // Each swap settles at least one destination; at most count swaps.
        // This moves existing owners without recursive copies or disposal.
        for original in 0..count {
            while destinations[original] != original {
                let target = destinations[original];
                definitions.0.swap(original, target);
                destinations.swap(original, target);
            }
        }
        Ok(())
    }

    pub(super) fn effect_sources<'a>(
        &mut self,
        surface: &'a SurfaceModule,
    ) -> Result<Vec<EffectSource<'a>>, ResolveError> {
        let mut sources = Vec::new();
        self.type_work.charge(surface.effects.len()).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                surface.span,
                "effect source view preparation exceeded its work budget",
            )
        })?;
        sources.try_reserve(surface.effects.len()).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                surface.span,
                "effect source view storage could not be reserved",
            )
        })?;
        if surface.foreign_libraries.is_empty() {
            sources.extend(surface.effects.iter().map(EffectSource::Ordinary));
            return Ok(sources);
        }
        let mut next_ordinary = 0;
        for library in &surface.foreign_libraries {
            while surface
                .effects
                .get(next_ordinary)
                .is_some_and(|effect| effect.span.range().start() < library.span.range().start())
            {
                sources.try_reserve(1).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        surface.span,
                        "effect source view storage could not be reserved",
                    )
                })?;
                sources.push(EffectSource::Ordinary(&surface.effects[next_ordinary]));
                next_ordinary += 1;
            }
            for member in &library.members {
                self.type_work.charge(1).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        library.span,
                        "foreign effect source views exceeded their work budget",
                    )
                })?;
                if let SurfaceForeignMember::Symbol(symbol) = member {
                    sources.try_reserve(1).map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            symbol.span,
                            "foreign effect source view storage could not be reserved",
                        )
                    })?;
                    sources.push(EffectSource::Foreign {
                        public: library.public,
                        symbol,
                    });
                }
            }
        }
        let remaining = &surface.effects[next_ordinary..];
        sources.try_reserve(remaining.len()).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                surface.span,
                "effect source view storage could not be reserved",
            )
        })?;
        sources.extend(remaining.iter().map(EffectSource::Ordinary));
        Ok(sources)
    }
}

fn source_build_failure(failure: ResolvedBuildFailure, span: Span) -> ResolveError {
    error(
        if failure == ResolvedBuildFailure::TypeResource {
            ResolveReason::TypeResourceExhausted
        } else {
            ResolveReason::InternalState
        },
        span,
        "source foreign facts could not be retained",
    )
}

fn source_admission_failure(
    failure: crate::foreign::checked_source::ForeignAdmissionError,
) -> ResolveError {
    error(
        if failure.is_resource_exhaustion() {
            ResolveReason::TypeResourceExhausted
        } else {
            ResolveReason::ForeignContract
        },
        failure.span(),
        &format!("foreign source admission rejected {:?}", failure.reason()),
    )
}

pub(super) fn retain_module_declaration_order(
    surface: &SurfaceModule,
    prepared: &[PreparedLibrarySource],
    work: &mut TypeWorkBudget,
) -> Result<Vec<crate::resolved::ResolvedDeclarationIndex>, ResolveError> {
    if prepared.is_empty() {
        return retain_declaration_order(&surface.declaration_order, surface.span, work);
    }
    let mut result = Vec::new();
    let mut next_library = 0;
    let mut next_ordinary = 0;
    let mut next_effect = 0;
    let mut next_owner = surface.type_declarations.len();
    let mut next_global = 0;
    for declaration in &surface.declaration_order {
        if let SurfaceDeclarationIndex::ForeignLibrary(index) = *declaration {
            work.charge(1).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign declaration-order traversal exceeded its work budget",
                )
            })?;
            if index != next_library {
                return Err(error(
                    ResolveReason::InternalState,
                    surface.span,
                    "foreign declaration order repeats, skips or reorders a library",
                ));
            }
            let library = prepared.get(index).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    surface.span,
                    "foreign declaration index is invalid",
                )
            })?;
            if library.effects.start != next_effect {
                return Err(error(
                    ResolveReason::InternalState,
                    surface.span,
                    "foreign effect range disagrees with source declaration order",
                ));
            }
            work.charge(library.effects.len()).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign declaration order exceeded its work budget",
                )
            })?;
            let added = library
                .effects
                .len()
                .checked_add(library.prepared.owners().len())
                .and_then(|n| n.checked_add(library.prepared.accesses().len()))
                .and_then(|n| n.checked_add(library.prepared.constants().len()))
                .ok_or_else(|| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        surface.span,
                        "foreign declaration order exceeded its bound",
                    )
                })?;
            result.try_reserve(added).map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign declaration order storage could not be reserved",
                )
            })?;
            let written = &surface.foreign_libraries[index];
            work.charge(written.members.len()).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    written.span,
                    "foreign member order exceeded its work budget",
                )
            })?;
            let mut effect = library.effects.start;
            let mut owners = 0;
            for member in &written.members {
                match member {
                    SurfaceForeignMember::Owner(_) | SurfaceForeignMember::Access(_) => {
                        result.push(crate::resolved::ResolvedDeclarationIndex::Type(next_owner));
                        next_owner = next_owner.checked_add(1).ok_or_else(|| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                written.span,
                                "foreign owner order exceeded its bound",
                            )
                        })?;
                        owners += 1;
                    }
                    SurfaceForeignMember::Constant(_) => {
                        result.push(crate::resolved::ResolvedDeclarationIndex::Global(
                            next_global,
                        ));
                        next_global = next_global.checked_add(1).ok_or_else(|| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                written.span,
                                "foreign constant order exceeded its bound",
                            )
                        })?;
                    }
                    SurfaceForeignMember::Symbol(_) => {
                        result.push(crate::resolved::ResolvedDeclarationIndex::Effect(effect));
                        effect += 1;
                    }
                    _ => {}
                }
            }
            if effect != library.effects.end
                || owners
                    != library
                        .prepared
                        .owners()
                        .len()
                        .saturating_add(library.prepared.accesses().len())
            {
                return Err(error(
                    ResolveReason::InternalState,
                    written.span,
                    "foreign member order disagrees with canonical preparation",
                ));
            }
            next_effect = library.effects.end;
            next_library += 1;
        } else {
            // Reuse the charged ordinary retention walk before inspecting and
            // remapping its source-vector index into the combined inventory.
            let mut ordinary =
                retain_declaration_order(std::slice::from_ref(declaration), surface.span, work)?;
            if let SurfaceDeclarationIndex::Global(_) = *declaration {
                ordinary[0] = crate::resolved::ResolvedDeclarationIndex::Global(next_global);
                next_global = next_global.checked_add(1).ok_or_else(|| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        surface.span,
                        "foreign constant order exceeded its bound",
                    )
                })?;
            }
            if let SurfaceDeclarationIndex::Effect(index) = *declaration {
                if index != next_ordinary || index >= surface.effects.len() {
                    return Err(error(
                        ResolveReason::InternalState,
                        surface.span,
                        "ordinary effect order repeats, skips or reorders a declaration",
                    ));
                }
                ordinary[0] = crate::resolved::ResolvedDeclarationIndex::Effect(next_effect);
                next_ordinary += 1;
                next_effect += 1;
            }
            result.try_reserve(1).map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "declaration order storage could not be reserved",
                )
            })?;
            result.extend(ordinary);
        }
    }
    if next_ordinary != surface.effects.len() {
        return Err(error(
            ResolveReason::InternalState,
            surface.span,
            "foreign declaration order omits an ordinary effect",
        ));
    }
    if next_library != prepared.len() {
        return Err(error(
            ResolveReason::InternalState,
            surface.span,
            "foreign declaration order omits a library",
        ));
    }
    Ok(result)
}

#[cfg(test)]
mod checked_metadata_tests {
    use super::*;
    use crate::{
        lexer::lex,
        module::ModuleId,
        parser::{parse, project_module},
        source::SourceFile,
    };

    #[test]
    fn checked_assumptions_do_not_publish_or_reserve_module_member_names() {
        let text = r#"foreign checked library First {
    assumption Behavior "First original."
}
foreign checked library Second {
    assumption Behavior "Distinct second original."
}
foreign checked library Third {
    symbol Behavior<H> : Unit -> Unit {
        name "noop"
        abi () -> void
        host H
        assumes {}
    }
}
"#;
        let source = SourceFile::new("checked-name-collisions.ash", text).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(tree.parse_diagnostics().is_empty());
        let surface = project_module(&source, &tree).unwrap();
        let mut resolver = Resolver::new(ModuleId::from(source.id()));
        resolver.validate_source_foreign_members(&surface).unwrap();
        // Only published members still collide across libraries.
        let mut duplicate = surface.clone();
        let symbol = duplicate.foreign_libraries[2].members[0].clone();
        duplicate.foreign_libraries[0].members.push(symbol);
        assert!(
            Resolver::new(ModuleId::from(source.id()))
                .validate_source_foreign_members(&duplicate)
                .is_err()
        );
    }
}
