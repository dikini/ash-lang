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
    prepared: Arc<PreparedForeignLibrary>,
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
                    SurfaceForeignMember::Profile(_) => continue,
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
            // Publishing executable constants needs the ordinary term bridge;
            // do not silently omit a source member from this first admission slice.
            if let Some((span, message)) = library.members.iter().find_map(|member| match member {
                SurfaceForeignMember::Constant(constant) => Some((
                    constant.span,
                    "source foreign constant publication is not implemented yet",
                )),
                SurfaceForeignMember::Owner(owner) => Some((
                    owner.span,
                    "source foreign owners require canonical owner admission",
                )),
                SurfaceForeignMember::Representation(representation)
                    if matches!(
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
        let context = ForeignBindingContext::new(
            &registry,
            common_module,
            common_span,
            ids,
            &mut self.type_work,
        )
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
        for (effect_index, symbol) in symbols {
            declarations.effects[effect_index].native_contract = Some(Arc::clone(&symbol));
            registry
                .retain_native_symbol(symbol, &mut self.type_work)
                .map_err(|failure| source_build_failure(failure, surface.span))?;
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
            result.try_reserve(library.effects.len()).map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign declaration order storage could not be reserved",
                )
            })?;
            result.extend(
                library
                    .effects
                    .clone()
                    .map(crate::resolved::ResolvedDeclarationIndex::Effect),
            );
            next_effect = library.effects.end;
            next_library += 1;
        } else {
            // Reuse the charged ordinary retention walk before inspecting and
            // remapping its source-vector index into the combined inventory.
            let mut ordinary =
                retain_declaration_order(std::slice::from_ref(declaration), surface.span, work)?;
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
