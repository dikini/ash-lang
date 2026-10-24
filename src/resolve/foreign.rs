//! Native symbols use the ordinary source effect operation path.
use super::{
    DependencyExports, ResolveError, ResolveReason, ResolvedDeclarations, Resolver, error,
};
use crate::{
    foreign::{
        checked_source::{ForeignBindingContext, NativeLibraryId, bind_foreign_symbol},
        source_contract::{PreparedForeignLibrary, prepare_foreign_library_with_budget},
    },
    source::Span,
    surface::{
        SurfaceEffectDeclaration, SurfaceForeignMember, SurfaceForeignSymbol, SurfaceModule,
        SurfaceName, SurfaceType, SurfaceTypeParameter,
    },
};
use std::{collections::HashMap, ops::Range, sync::Arc};
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
            Self::Foreign { .. } => &[],
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
            for member in &library.members {
                if let SurfaceForeignMember::Symbol(symbol) = member {
                    self.type_work.charge(1).map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            symbol.span,
                            "foreign member work exhausted",
                        )
                    })?;
                    if names
                        .insert(symbol.name.text.as_str(), symbol.span)
                        .is_some()
                        || surface
                            .effects
                            .iter()
                            .any(|effect| effect.name.text == symbol.name.text)
                    {
                        return Err(error(
                            ResolveReason::DuplicateEffect,
                            symbol.span,
                            "duplicate foreign operation name",
                        ));
                    }
                }
            }
        }
        Ok(())
    }
    pub(super) fn prepare_source_foreign(
        &mut self,
        surface: &SurfaceModule,
    ) -> Result<Vec<PreparedLibrarySource>, ResolveError> {
        let mut result = Vec::new();
        result
            .try_reserve_exact(surface.foreign_libraries.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign declaration storage exhausted",
                )
            })?;
        for library in &surface.foreign_libraries {
            let prepared =
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
            let start = surface
                .effects
                .iter()
                .filter(|effect| effect.span.range().start() < library.span.range().start())
                .count()
                + result
                    .iter()
                    .map(|p: &PreparedLibrarySource| p.prepared.symbols().len())
                    .sum::<usize>();
            let end = start.checked_add(prepared.symbols().len()).ok_or_else(|| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    library.span,
                    "foreign operation count overflow",
                )
            })?;
            result.push(PreparedLibrarySource {
                prepared: Arc::new(prepared),
                effects: start..end,
            });
        }
        Ok(result)
    }
    pub(super) fn bind_source_foreign(
        &mut self,
        surface: &SurfaceModule,
        prepared: &[PreparedLibrarySource],
        declarations: &mut ResolvedDeclarations,
        _dependencies: &[DependencyExports<'_>],
    ) -> Result<(), ResolveError> {
        let checking_registry = declarations
            .registry
            .checker_view(&self.imported, &mut self.type_work)
            .map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    surface.span,
                    "foreign checking registry is inconsistent",
                )
            })?;
        let mut symbols = Vec::new();
        for (ordinal, library) in prepared.iter().enumerate() {
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign library count overflow",
                )
            })?;
            for (index, effect_index) in library.effects.clone().enumerate() {
                let effect = declarations.effects.get(effect_index).ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        surface.span,
                        "missing foreign effect",
                    )
                })?;
                let symbol = bind_foreign_symbol(
                    NativeLibraryId::new(self.module, ordinal),
                    Arc::clone(&library.prepared),
                    index,
                    effect,
                    &ForeignBindingContext::new(&checking_registry),
                    &mut self.type_work,
                )
                .map_err(|failure| {
                    error(
                        ResolveReason::ForeignContract,
                        failure.span(),
                        &failure.to_string(),
                    )
                })?;
                symbols.try_reserve(1).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        surface.span,
                        "foreign symbol storage exhausted",
                    )
                })?;
                symbols.push((effect_index, Arc::new(symbol)));
            }
        }
        let registry = Arc::get_mut(&mut declarations.registry).ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                surface.span,
                "foreign registry is shared before publication",
            )
        })?;
        for (index, symbol) in symbols {
            declarations.effects[index].native_contract = Some(Arc::clone(&symbol));
            registry
                .retain_native_symbol(symbol, &mut self.type_work)
                .map_err(|_| {
                    error(
                        ResolveReason::InternalState,
                        surface.span,
                        "could not retain foreign operation",
                    )
                })?;
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

/// Expands passive libraries into their ordinary effect declarations while
/// retaining all ordinary declaration indices and source ordering.
pub(super) fn retain_module_declaration_order(
    surface: &SurfaceModule,
    prepared: &[PreparedLibrarySource],
    work: &mut crate::types::TypeWorkBudget,
) -> Result<Vec<crate::resolved::ResolvedDeclarationIndex>, ResolveError> {
    use crate::resolved::ResolvedDeclarationIndex;
    use crate::surface::SurfaceDeclarationIndex;
    if prepared.is_empty() {
        return super::retain_declaration_order(&surface.declaration_order, surface.span, work);
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
                    "foreign declaration-order work exhausted",
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
                    "foreign effect range disagrees with declaration order",
                ));
            }
            work.charge(library.effects.len()).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign declaration-order work exhausted",
                )
            })?;
            result.try_reserve(library.effects.len()).map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "foreign declaration-order storage exhausted",
                )
            })?;
            result.extend(
                library
                    .effects
                    .clone()
                    .map(ResolvedDeclarationIndex::Effect),
            );
            next_effect = library.effects.end;
            next_library += 1;
        } else {
            let mut ordinary = super::retain_declaration_order(
                std::slice::from_ref(declaration),
                surface.span,
                work,
            )?;
            if let SurfaceDeclarationIndex::Effect(index) = *declaration {
                if index != next_ordinary || index >= surface.effects.len() {
                    return Err(error(
                        ResolveReason::InternalState,
                        surface.span,
                        "ordinary effect order repeats, skips or reorders a declaration",
                    ));
                }
                ordinary[0] = ResolvedDeclarationIndex::Effect(next_effect);
                next_ordinary += 1;
                next_effect += 1;
            }
            result.try_reserve(1).map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "declaration-order storage exhausted",
                )
            })?;
            result.extend(ordinary);
        }
    }
    if next_ordinary != surface.effects.len() || next_library != prepared.len() {
        return Err(error(
            ResolveReason::InternalState,
            surface.span,
            "declaration order omits an effect or library",
        ));
    }
    Ok(result)
}
