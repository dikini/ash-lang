//! Canonical binding for scalar and dependency-free source owner contracts.
//!
//! ABI preparation remains in one shared allocation. Binding adds the original
//! resolved operation, its complete binder vector and signature, and the common
//! result codec. It neither constructs a manifest nor grants native execution.

use std::{collections::HashSet, fmt, sync::Arc};

use crate::{
    module::ModuleId,
    resolved::{
        CanonicalNominalKind, OwnerId, ResolvedEffectDeclaration, ResolvedEffectOperation,
        ResolvedNominalDeclarationKind, ResolvedRegistry, ResolvedTypeProvenance,
        clone_effect_origin_with_budget, same_origin_with_budget,
        same_resolved_type_provenance_with_budget,
    },
    source::{Origin, Span, discard_origin_iteratively},
    types::{
        ConstructorId, EffectId, IterativeTypeOwner, Kind, NominalTypeId, OperationId, Type,
        TypeVariableId, TypeWorkBudget, clone_type_with_budget, same_type_with_budget,
    },
};

use super::source_contract::{
    PreparedAbiResult, PreparedForeignCall, PreparedForeignLibrary, PreparedForeignSymbol,
    PreparedOperandSource, PreparedRepresentation,
};

/// The defining library coordinate, allocated during ordinary source admission.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NativeLibraryId {
    module: ModuleId,
    ordinal: u32,
}

impl NativeLibraryId {
    pub(crate) const fn new(module: ModuleId, ordinal: u32) -> Self {
        Self { module, ordinal }
    }

    pub const fn module(self) -> ModuleId {
        self.module
    }

    pub const fn ordinal(self) -> u32 {
        self.ordinal
    }
}

/// Reconstruct the selected checked H from the complete original actual vector.
/// The returned row member supplies no native execution capability.
pub(crate) fn checked_host_instance(
    symbol: &CheckedForeignSymbol,
    actual: &crate::types::EffectInstance,
    work: &mut TypeWorkBudget,
) -> Result<Option<crate::types::EffectInstance>, ForeignAdmissionError> {
    let span = symbol.call_codec().source();
    charge(work, 3, span)?;
    let Some(contract) = symbol.prepared().checked_contract() else {
        return Ok(None);
    };
    let selected = contract
        .symbols()
        .get(symbol.symbol_index())
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidParameters, span))?;
    if actual.effect() != symbol.effect()
        || actual.arguments().len() != symbol.parameter_ids().len()
    {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    }
    let Some(crate::types::KindedArgument::TypeArg(host)) =
        actual.arguments().get(selected.host_parameter())
    else {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    };
    let host = clone_type_with_budget(host, work)
        .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?;
    Ok(Some(crate::types::EffectInstance::new_kinded(
        EffectId::new(
            symbol.call_codec().module(),
            crate::module::FOREIGN_NATIVE_HOST_LOCAL,
        ),
        Box::new([crate::types::KindedArgument::TypeArg(host)]),
    )))
}

/// Candidate roles supplied by admission of the compiler-owned common module.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ForeignCallCodecIds {
    pub(crate) call: NominalTypeId,
    pub(crate) returned: ConstructorId,
    pub(crate) conversion_failed: ConstructorId,
    pub(crate) conversion_error: NominalTypeId,
}

/// Canonical common result roles, never inferred from a client type's spelling.
pub(crate) struct CheckedForeignCallCodec {
    module: ModuleId,
    source: Span,
    ids: ForeignCallCodecIds,
}

impl CheckedForeignCallCodec {
    pub(crate) fn authenticate(
        module: ModuleId,
        source: Span,
        ids: ForeignCallCodecIds,
        registry: &ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ForeignAdmissionError> {
        authenticate_codec(module, source, ids, registry, work)?;
        Ok(Self {
            module,
            source,
            ids,
        })
    }

    pub(crate) const fn module(&self) -> ModuleId {
        self.module
    }

    pub(crate) const fn ids(&self) -> ForeignCallCodecIds {
        self.ids
    }

    pub(crate) const fn source(&self) -> Span {
        self.source
    }
}

/// One binding pass tied to an immutable original registry allocation.
///
/// The registry cannot change while its codec is used to admit local symbols.
/// Independent consumers construct their own authenticated context once.
pub(crate) struct ForeignBindingContext<'registry> {
    registry: &'registry ResolvedRegistry,
    codec: Arc<CheckedForeignCallCodec>,
    owners: &'registry [Arc<super::source_owner::CheckedForeignOwner>],
    owner_codec: Option<Arc<super::source_owner::CheckedForeignOwnerCodec>>,
}

impl<'registry> ForeignBindingContext<'registry> {
    pub(crate) fn codec(&self) -> &Arc<CheckedForeignCallCodec> {
        &self.codec
    }
    pub(crate) fn new(
        registry: &'registry ResolvedRegistry,
        common_module: ModuleId,
        common_source: Span,
        ids: ForeignCallCodecIds,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ForeignAdmissionError> {
        let codec = CheckedForeignCallCodec::authenticate(
            common_module,
            common_source,
            ids,
            registry,
            work,
        )?;
        charge(work, 1, common_source)?;
        Ok(Self {
            registry,
            codec: Arc::new(codec),
            owners: &[],
            owner_codec: None,
        })
    }

    pub(crate) fn with_owners(
        mut self,
        owners: &'registry [Arc<super::source_owner::CheckedForeignOwner>],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ForeignAdmissionError> {
        charge(work, owners.len(), self.codec.source())?;
        if !owners.is_empty() {
            self.owner_codec = Some(Arc::new(
                super::source_owner::CheckedForeignOwnerCodec::authenticate(
                    self.codec.module(),
                    self.codec.source(),
                    self.registry,
                    work,
                )?,
            ));
        }
        self.owners = owners;
        Ok(self)
    }
}

/// Member-level checked facts shared by registry, Core and bridge planning.
///
/// Source admission owns construction. The descriptor alone is not a provider
/// or a proof of the library's behavioral assumptions.
pub struct CheckedForeignSymbol {
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    symbol_index: usize,
    operation: OperationId,
    parameter_ids: Box<[TypeVariableId]>,
    source_signature: IterativeTypeOwner,
    source_provenance: CheckedForeignSourceProvenance,
    call_codec: Arc<CheckedForeignCallCodec>,
    owner: Option<Arc<super::source_owner::CheckedForeignOwner>>,
    owner_codec: Option<Arc<super::source_owner::CheckedForeignOwnerCodec>>,
}

// Retain only original provenance absent from the immutable prepared facts.
// Origin guards also dismantle partially retained records on a later refusal.
struct CheckedForeignSourceProvenance {
    operation_span: Span,
    operation_origin: ForeignOriginOwner,
    annotation_span: Span,
    annotation_origin: ForeignOriginOwner,
    annotation_provenance: ResolvedTypeProvenance,
    parameter_origins: Box<[ForeignOriginOwner]>,
}

struct ForeignOriginOwner(Option<Origin>);

impl ForeignOriginOwner {
    fn retain(origin: &Origin, work: &mut TypeWorkBudget) -> Result<Self, ()> {
        clone_effect_origin_with_budget(origin, work).map(|origin| Self(Some(origin)))
    }

    fn origin(&self) -> &Origin {
        self.0.as_ref().expect("a retained foreign origin is live")
    }
}

impl Drop for ForeignOriginOwner {
    fn drop(&mut self) {
        if let Some(origin) = self.0.take() {
            discard_origin_iteratively(origin);
        }
    }
}

impl fmt::Debug for CheckedForeignSymbol {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("CheckedForeignSymbol")
            .field("library", &self.library)
            .field("symbol_index", &self.symbol_index)
            .field("symbol", &self.symbol().name())
            .field("operation", &self.operation)
            .field("parameter_count", &self.parameter_ids.len())
            .field("call_codec", &self.call_codec.ids)
            .finish_non_exhaustive()
    }
}

impl PartialEq for CheckedForeignSymbol {
    fn eq(&self, other: &Self) -> bool {
        // One codec allocation identifies an immutable registry binding pass.
        // Within that pass an original operation fixes both its signature and
        // complete binder vector. Metadata equality compares that authority;
        // independent type validation uses the retained signature and a budget.
        self.library == other.library
            && self.symbol_index == other.symbol_index
            && self.operation == other.operation
            && Arc::ptr_eq(&self.prepared, &other.prepared)
            && Arc::ptr_eq(&self.call_codec, &other.call_codec)
            && match (&self.owner, &other.owner) {
                (None, None) => true,
                (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                _ => false,
            }
    }
}

impl Eq for CheckedForeignSymbol {}

impl CheckedForeignSymbol {
    pub(crate) fn owner(&self) -> Option<&Arc<super::source_owner::CheckedForeignOwner>> {
        self.owner.as_ref()
    }

    pub(crate) fn owner_role(&self) -> Option<&super::source_contract::PreparedOwnerCall> {
        self.symbol().owner_call()
    }

    pub(crate) fn owner_codec(&self) -> Option<&super::source_owner::CheckedForeignOwnerCodec> {
        self.owner_codec.as_deref()
    }
    pub(crate) const fn library(&self) -> NativeLibraryId {
        self.library
    }

    pub(crate) fn prepared(&self) -> &Arc<PreparedForeignLibrary> {
        &self.prepared
    }

    pub(crate) const fn symbol_index(&self) -> usize {
        self.symbol_index
    }

    pub(crate) fn symbol(&self) -> &PreparedForeignSymbol {
        &self.prepared.symbols()[self.symbol_index]
    }

    pub(crate) const fn operation(&self) -> OperationId {
        self.operation
    }

    pub(crate) const fn effect(&self) -> EffectId {
        self.operation.owner()
    }

    pub(crate) fn parameter_ids(&self) -> &[TypeVariableId] {
        &self.parameter_ids
    }

    pub(crate) fn source_signature(&self) -> &Type {
        &self.source_signature
    }

    pub(crate) fn call_codec(&self) -> &Arc<CheckedForeignCallCodec> {
        &self.call_codec
    }

    /// Borrows the original source provenance before summary import retention
    /// or independent registry use. No ABI preparation or registry copy occurs.
    pub(crate) fn same_source_provenance(
        &self,
        effect: &ResolvedEffectDeclaration,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        work.charge(effect.parameters.len().checked_add(3).ok_or(())?)?;
        let prepared = self.symbol();
        let source_span = primary_span(prepared.origin(), work, effect.span).map_err(|_| ())?;
        let retained = &self.source_provenance;
        let [operation] = effect.operations.as_ref() else {
            return Ok(false);
        };
        if effect.span != source_span
            || effect.public != self.prepared().public()
            || operation.span != retained.operation_span
            || operation.annotation.span != retained.annotation_span
            || effect.parameters.len() != retained.parameter_origins.len()
            || effect.parameters.len() != prepared.parameters().len()
            || !names_match(&effect.spelling, prepared.name(), work, source_span).map_err(|_| ())?
            || !names_match(&operation.spelling, "call", work, source_span).map_err(|_| ())?
            || !same_origin_with_budget(&effect.origin, prepared.origin(), work)?
            || !same_origin_with_budget(
                &operation.origin,
                retained.operation_origin.origin(),
                work,
            )?
            || !same_origin_with_budget(
                &operation.annotation.origin,
                retained.annotation_origin.origin(),
                work,
            )?
            || !same_resolved_type_provenance_with_budget(
                &operation.annotation.provenance,
                &retained.annotation_provenance,
                work,
            )?
        {
            return Ok(false);
        }
        for ((actual, original), prepared) in effect
            .parameters
            .iter()
            .zip(&retained.parameter_origins)
            .zip(prepared.parameters())
        {
            if !names_match(&actual.spelling, prepared.name(), work, source_span).map_err(|_| ())?
                || !same_origin_with_budget(&actual.origin, original.origin(), work)?
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ForeignAdmissionReason {
    InvalidLibrary,
    InvalidOperation,
    InvalidParameters,
    InvalidCodec,
    InvalidSignature,
    InvalidSourcePosition,
    UnsupportedDomain,
    WorkExhausted,
    StorageRefused,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ForeignAdmissionError {
    reason: ForeignAdmissionReason,
    span: Span,
}

impl ForeignAdmissionError {
    pub(crate) const fn reason(self) -> ForeignAdmissionReason {
        self.reason
    }

    pub(crate) const fn span(self) -> Span {
        self.span
    }

    pub(crate) const fn is_resource_exhaustion(self) -> bool {
        matches!(
            self.reason,
            ForeignAdmissionReason::WorkExhausted | ForeignAdmissionReason::StorageRefused
        )
    }
}

pub(super) fn failure(reason: ForeignAdmissionReason, span: Span) -> ForeignAdmissionError {
    ForeignAdmissionError { reason, span }
}

pub(super) fn charge(
    work: &mut TypeWorkBudget,
    count: usize,
    span: Span,
) -> Result<(), ForeignAdmissionError> {
    work.charge(count)
        .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))
}

fn reserve<T>(
    values: &mut Vec<T>,
    count: usize,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), ForeignAdmissionError> {
    charge(work, count, span)?;
    values
        .try_reserve_exact(count)
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))
}

pub(super) fn names_match(
    left: &str,
    right: &str,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<bool, ForeignAdmissionError> {
    charge(work, 1, span)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    charge(work, left.len(), span)?;
    Ok(left == right)
}

pub(super) fn primary_span(
    mut origin: &Origin,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<Span, ForeignAdmissionError> {
    loop {
        charge(work, 1, span)?;
        match origin {
            Origin::Source(source) => return Ok(*source),
            Origin::Generated { cause, .. } => origin = cause,
            Origin::Related { primary, related } => {
                charge(work, related.len(), span)?;
                origin = primary;
            }
        }
    }
}

fn contains(outer: Span, inner: Span) -> bool {
    outer.source() == inner.source()
        && outer.range().start() <= inner.range().start()
        && inner.range().end() <= outer.range().end()
}

pub(super) fn origin_within(
    outer: Span,
    origin: &Origin,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignAdmissionError> {
    Ok(contains(outer, primary_span(origin, work, outer)?))
}

fn authenticate_codec(
    module: ModuleId,
    source: Span,
    ids: ForeignCallCodecIds,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    if ids.call == NominalTypeId::new(module, 12) {
        let facts =
            super::checked_builtins::authenticate_checked_builtins(registry, module, source, work)?;
        if ids.call != facts.checked_call()
            || ids.returned != facts.returned()
            || ids.conversion_failed != facts.conversion_failed()
            || ids.conversion_error != NominalTypeId::new(module, 0)
        {
            return Err(failure(ForeignAdmissionReason::InvalidCodec, source));
        }
        return Ok(());
    }
    charge(work, 9, source)?;
    if !module.is_builtin_foreign()
        || ids.conversion_error != NominalTypeId::new(module, 0)
        || ids.call != NominalTypeId::new(module, 1)
        || ids.returned != ConstructorId::new(ids.call, 0)
        || ids.conversion_failed != ConstructorId::new(ids.call, 1)
    {
        return Err(failure(ForeignAdmissionReason::InvalidCodec, source));
    }
    let invalid = || failure(ForeignAdmissionReason::InvalidCodec, source);
    let call = registry.nominal(ids.call).ok_or_else(invalid)?;
    let returned = registry.constructor(ids.returned).ok_or_else(invalid)?;
    let failed = registry
        .constructor(ids.conversion_failed)
        .ok_or_else(invalid)?;
    let parameters = registry.nominal_parameters(ids.call).ok_or_else(invalid)?;
    if call.declaration_kind != ResolvedNominalDeclarationKind::Data
        || call.representation.is_some()
        || call.representation_provenance.is_some()
        || call.constructors.as_ref() != [ids.returned, ids.conversion_failed]
        || parameters.len() != 1
        || returned.owner != ids.call
        || failed.owner != ids.call
    {
        return Err(invalid());
    }
    // Imported opacity preserves canonical kind/provenance authority without
    // materializing ConversionError or exposing its hidden constructor family.
    if let Some(error) = registry.nominal(ids.conversion_error)
        && (error.declaration_kind != ResolvedNominalDeclarationKind::Data
            || error.representation.is_some()
            || error.representation_provenance.is_some()
            || !origin_within(source, &error.origin, work)?)
    {
        return Err(invalid());
    }
    let error_origin = match registry.nominal_kind(ids.conversion_error) {
        Some(CanonicalNominalKind::Parameters {
            parameters: [],
            origin,
        }) => origin,
        Some(CanonicalNominalKind::Frozen {
            kind: Kind::Type,
            origin,
        }) => origin,
        _ => return Err(invalid()),
    };
    if !contains(source, error_origin) {
        return Err(invalid());
    }
    let parameter = &parameters[0];
    let canonical = registry.type_variable(parameter.id).ok_or_else(invalid)?;
    if parameter.id.module() != Some(module)
        || parameter.kind != Kind::Type
        || canonical.kind != Kind::Type
        || canonical.id != parameter.id
        || !matches!(&returned.payload, Some(Type::Variable(id)) if *id == parameter.id)
        || !matches!(&failed.payload, Some(Type::Nominal(id)) if *id == ids.conversion_error)
    {
        return Err(invalid());
    }
    if !same_origin_with_budget(&parameter.origin, &canonical.origin, work)
        .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, source))?
    {
        return Err(invalid());
    }
    // Nominal/constructor spellings are display aliases in a consuming view.
    // Exact builtin identities and payload roles above carry the authority.
    if !names_match(&canonical.spelling, &parameter.spelling, work, source)? {
        return Err(invalid());
    }
    for origin in [
        &call.origin,
        &returned.origin,
        &failed.origin,
        &parameter.origin,
        &canonical.origin,
    ] {
        if !origin_within(source, origin, work)? {
            return Err(invalid());
        }
    }
    Ok(())
}

/// Binds an original registry-owned effect after ordinary namespace/type work.
///
/// Scalar calls and the admitted acquire/void-teardown shapes retain their
/// canonical preparation. Owner binding grants no provider phase or activation;
/// unsupported ABI and resolved domain forms remain explicit refusals.
pub(crate) fn bind_foreign_symbol(
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    symbol_index: usize,
    effect: &ResolvedEffectDeclaration,
    context: &ForeignBindingContext<'_>,
    work: &mut TypeWorkBudget,
) -> Result<CheckedForeignSymbol, ForeignAdmissionError> {
    if prepared.checked_contract().is_some() {
        charge(work, 1, effect.span)?;
        return Err(failure(ForeignAdmissionReason::InvalidLibrary, effect.span));
    }
    bind_foreign_symbol_for_profile(library, prepared, symbol_index, effect, context, work)
}

/// Explicit static checked binding; it grants no executable runtime authority.
pub(crate) fn bind_checked_foreign_symbol(
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    symbol_index: usize,
    effect: &ResolvedEffectDeclaration,
    context: &ForeignBindingContext<'_>,
    work: &mut TypeWorkBudget,
) -> Result<CheckedForeignSymbol, ForeignAdmissionError> {
    charge(work, 1, effect.span)?;
    let supported = match prepared
        .symbols()
        .get(symbol_index)
        .map(PreparedForeignSymbol::call)
    {
        Some(PreparedForeignCall::Scalar { .. }) => true,
        Some(PreparedForeignCall::Owner(role)) => {
            use super::source_contract::{
                PreparedAddressRepresentation as Representation, PreparedOwnerCall,
            };
            charge(work, 1, effect.span)?;
            let symbol = &prepared.symbols()[symbol_index];
            prepared.owners().get(role.application().owner()).is_some_and(|owner| {
                owner.retained_parameters().is_empty() && match role {
                    PreparedOwnerCall::Acquire { initialized_bytes, .. } => matches!(
                        (owner.representation(), initialized_bytes),
                        (Representation::Opaque, None) | (Representation::Bytes, Some(_))
                    ),
                    PreparedOwnerCall::Teardown { .. } => matches!(owner.representation(), Representation::Opaque | Representation::Bytes),
                    PreparedOwnerCall::Borrow { .. } if symbol.access_result().is_some() => {
                        // The shared symbol validator proves the exact original
                        // access application, producing key and extent relation.
                        // A live window is independently required at each use.
                        matches!(owner.representation(), Representation::Opaque | Representation::Bytes)
                    }
                    PreparedOwnerCall::Borrow { current_operand: 0, .. } => {
                        // Preserve the narrower PR98 scalar-Current subset.
                        symbol.operands().len() == 1
                            && matches!(symbol.operands()[0].source(), PreparedOperandSource::Current(path) if path == &[0])
                            && effect.operations.first().is_some_and(|operation| {
                                matches!(&operation.annotation.ty, Type::Function(domain, _) if !matches!(domain.as_ref(), Type::Tuple(_)))
                            })
                            && matches!(symbol.result(), PreparedAbiResult::Scalar(_))
                            && owner.representation() == Representation::Opaque
                    }
                    _ => false,
                }
            })
        }
        _ => false,
    };
    if prepared.checked_contract().is_none() || !supported {
        return Err(failure(ForeignAdmissionReason::InvalidLibrary, effect.span));
    }
    bind_foreign_symbol_for_profile(library, prepared, symbol_index, effect, context, work)
}

fn bind_foreign_symbol_for_profile(
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    symbol_index: usize,
    effect: &ResolvedEffectDeclaration,
    context: &ForeignBindingContext<'_>,
    work: &mut TypeWorkBudget,
) -> Result<CheckedForeignSymbol, ForeignAdmissionError> {
    let owner = match prepared
        .symbols()
        .get(symbol_index)
        .and_then(|symbol| symbol.owner_call())
    {
        Some(call) => {
            charge(work, context.owners.len(), effect.span)?;
            let application = call.application();
            Some(
                context
                    .owners
                    .iter()
                    .find(|owner| {
                        Arc::ptr_eq(owner.prepared(), &prepared)
                            && owner.library() == library
                            && owner.owner_index() == application.owner()
                    })
                    .ok_or_else(|| failure(ForeignAdmissionReason::InvalidLibrary, effect.span))?,
            )
        }
        None => None,
    };
    let operation = validate_foreign_symbol_source(
        library,
        &prepared,
        symbol_index,
        effect,
        context,
        owner.map(Arc::as_ref),
        owner.and(context.owner_codec.as_ref()).map(Arc::as_ref),
        work,
    )?;
    let span = operation.span;
    // The source origins are normally inline spans. The shared clone protocol
    // also bounds and safely disposes generated or related provenance.
    charge(work, 3, span)?;
    let operation_origin = ForeignOriginOwner::retain(&operation.origin, work)
        .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?;
    let annotation_origin = ForeignOriginOwner::retain(&operation.annotation.origin, work)
        .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?;
    let mut parameter_ids = Vec::new();
    let mut parameter_origins = Vec::new();
    reserve(&mut parameter_ids, effect.parameters.len(), work, span)?;
    reserve(&mut parameter_origins, effect.parameters.len(), work, span)?;
    for parameter in &effect.parameters {
        charge(work, 1, span)?;
        parameter_ids.push(parameter.id);
        parameter_origins.push(
            ForeignOriginOwner::retain(&parameter.origin, work)
                .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?,
        );
    }
    let source_signature = IterativeTypeOwner::new(
        clone_type_with_budget(&operation.annotation.ty, work)
            .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?,
    );
    Ok(CheckedForeignSymbol {
        library,
        prepared,
        symbol_index,
        operation: operation.id,
        parameter_ids: parameter_ids.into_boxed_slice(),
        source_signature,
        source_provenance: CheckedForeignSourceProvenance {
            operation_span: operation.span,
            operation_origin,
            annotation_span: operation.annotation.span,
            annotation_origin,
            annotation_provenance: operation.annotation.provenance.clone(),
            parameter_origins: parameter_origins.into_boxed_slice(),
        },
        call_codec: Arc::clone(&context.codec),
        owner: owner.map(Arc::clone),
        owner_codec: owner.and(context.owner_codec.as_ref()).map(Arc::clone),
    })
}

/// Checks sealed member facts against an independently consuming registry view.
///
/// Reuses prepared ABI facts and borrows the consuming signature. It allocates
/// no replacement descriptor or Type; scratch identity/traversal storage uses
/// the shared work budget and fallible reservations.
pub(crate) fn authenticate_foreign_symbol(
    symbol: &CheckedForeignSymbol,
    registry: &ResolvedRegistry,
    context: &ForeignBindingContext<'_>,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    let span = primary_span(symbol.prepared().origin(), work, context.codec.source())?;
    charge(work, 5, span)?;
    if !std::ptr::eq(registry, context.registry)
        || symbol.call_codec().module() != context.codec.module()
        || symbol.call_codec().source() != context.codec.source()
        || symbol.call_codec().ids() != context.codec.ids()
    {
        return Err(failure(ForeignAdmissionReason::InvalidCodec, span));
    }
    let effect = registry
        .effect(symbol.effect())
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidOperation, span))?;
    let operation = validate_foreign_symbol_source(
        symbol.library(),
        symbol.prepared(),
        symbol.symbol_index(),
        effect,
        context,
        symbol.owner().map(Arc::as_ref),
        symbol.owner_codec(),
        work,
    )?;
    if operation.id != symbol.operation() {
        return Err(failure(
            ForeignAdmissionReason::InvalidOperation,
            operation.span,
        ));
    }
    if !symbol
        .same_source_provenance(effect, work)
        .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, operation.span))?
    {
        return Err(failure(
            ForeignAdmissionReason::InvalidOperation,
            operation.span,
        ));
    }
    charge(
        work,
        symbol.parameter_ids().len().saturating_add(1),
        operation.span,
    )?;
    if symbol.parameter_ids().len() != effect.parameters.len()
        || !symbol
            .parameter_ids()
            .iter()
            .zip(&effect.parameters)
            .all(|(sealed, current)| *sealed == current.id)
    {
        return Err(failure(
            ForeignAdmissionReason::InvalidParameters,
            operation.span,
        ));
    }
    if !matches!(symbol.source_signature(), Type::Function(_, _))
        || !same_type_with_budget(symbol.source_signature(), &operation.annotation.ty, work)
            .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, operation.span))?
    {
        return Err(failure(
            ForeignAdmissionReason::InvalidSignature,
            operation.span,
        ));
    }
    Ok(())
}

// Keep original symbol coordinates and optional owner authority explicit.
#[allow(clippy::too_many_arguments)]
fn validate_foreign_symbol_source<'effect>(
    library: NativeLibraryId,
    prepared: &PreparedForeignLibrary,
    symbol_index: usize,
    effect: &'effect ResolvedEffectDeclaration,
    context: &ForeignBindingContext<'_>,
    owner: Option<&super::source_owner::CheckedForeignOwner>,
    owner_codec: Option<&super::source_owner::CheckedForeignOwnerCodec>,
    work: &mut TypeWorkBudget,
) -> Result<&'effect ResolvedEffectOperation, ForeignAdmissionError> {
    let registry = context.registry;
    let codec = &context.codec;
    let library_span = primary_span(prepared.origin(), work, effect.span)?;
    charge(work, 5, library_span)?;
    if library.module != prepared.module() || effect.id.module() != library.module {
        return Err(failure(
            ForeignAdmissionReason::InvalidLibrary,
            library_span,
        ));
    }
    let symbol = prepared
        .symbols()
        .get(symbol_index)
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidLibrary, library_span))?;
    charge(work, 1, library_span)?;
    if prepared.checked_contract().is_some()
        != (codec.ids().call == NominalTypeId::new(codec.module(), 12))
    {
        return Err(failure(ForeignAdmissionReason::InvalidCodec, library_span));
    }
    let span = primary_span(symbol.origin(), work, library_span)?;
    if !contains(library_span, span)
        || effect.span != span
        || !same_origin_with_budget(&effect.origin, symbol.origin(), work)
            .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?
        || effect.public != prepared.public()
        || !registry
            .effect(effect.id)
            .is_some_and(|original| std::ptr::eq(original, effect))
        || !names_match(&effect.spelling, symbol.name(), work, span)?
        || effect.operations.len() != 1
    {
        return Err(failure(ForeignAdmissionReason::InvalidOperation, span));
    }
    let operation = &effect.operations[0];
    if operation.id != OperationId::new(effect.id, 0)
        || !names_match(&operation.spelling, "call", work, span)?
        || !contains(span, operation.span)
        || !origin_within(span, &operation.origin, work)?
        || !contains(span, operation.annotation.span)
        || !origin_within(span, &operation.annotation.origin, work)?
        || operation.annotation.provenance.span() != Some(operation.annotation.span)
    {
        return Err(failure(ForeignAdmissionReason::InvalidOperation, span));
    }
    charge_owner_names(&effect.parameters, work, span)?;
    registry
        .authenticate_owner_signature(OwnerId::Effect(effect.id), None, &effect.parameters, work)
        .map_err(|reason| match reason {
            crate::resolved::ResolvedBuildFailure::TypeResource => {
                failure(ForeignAdmissionReason::WorkExhausted, span)
            }
            _ => failure(ForeignAdmissionReason::InvalidParameters, span),
        })?;
    if effect.parameters.len() != symbol.parameters().len() {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    }
    let defining = registry
        .defining_owner_parameters(OwnerId::Effect(effect.id))
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidParameters, span))?;
    charge_owner_names(defining, work, span)?;
    registry
        .authenticate_owner_signature(OwnerId::Effect(effect.id), None, defining, work)
        .map_err(|reason| match reason {
            crate::resolved::ResolvedBuildFailure::TypeResource => {
                failure(ForeignAdmissionReason::WorkExhausted, span)
            }
            _ => failure(ForeignAdmissionReason::InvalidParameters, span),
        })?;
    charge(work, defining.len(), span)?;
    if defining.len() != effect.parameters.len()
        || !defining
            .iter()
            .zip(&effect.parameters)
            .all(|(original, current)| original.id == current.id)
    {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    }
    let mut seen = HashSet::new();
    charge(work, effect.parameters.len(), span)?;
    seen.try_reserve(effect.parameters.len())
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    let mut type_index = 0;
    for (index, (resolved, source)) in effect
        .parameters
        .iter()
        .zip(symbol.parameters())
        .enumerate()
    {
        charge(work, 1, span)?;
        let parameter_span = primary_span(source.origin(), work, span)?;
        if !matches!(source.kind(), Kind::Type | Kind::EffectRow)
            || resolved.kind != *source.kind()
            || resolved.id.module() != Some(library.module)
            || !seen.insert(resolved.id)
            || !names_match(&resolved.spelling, source.name(), work, parameter_span)?
            || !origin_within(parameter_span, &resolved.origin, work)?
        {
            return Err(failure(
                ForeignAdmissionReason::InvalidParameters,
                parameter_span,
            ));
        }
        if resolved.kind == Kind::Type {
            if symbol.native_type_projection().get(type_index) != Some(&index) {
                return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
            }
            type_index += 1;
        }
    }
    if type_index != symbol.native_type_projection().len() {
        return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
    }
    if let PreparedForeignCall::Owner(_) = symbol.call() {
        let owner = owner.ok_or_else(|| failure(ForeignAdmissionReason::InvalidLibrary, span))?;
        let owner_codec =
            owner_codec.ok_or_else(|| failure(ForeignAdmissionReason::InvalidCodec, span))?;
        super::source_owner::validate_owner_symbol(
            library,
            prepared,
            symbol,
            effect,
            owner,
            owner_codec,
            codec,
            registry,
            work,
        )?;
        return Ok(operation);
    }
    if owner.is_some() || owner_codec.is_some() {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    }
    charge(work, 3, span)?;
    let Type::Function(domain, codomain) = &operation.annotation.ty else {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    };
    let Type::Application(head, result) = codomain.as_ref() else {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    };
    if !matches!(head.as_ref(), Type::Nominal(id) if *id == codec.ids.call)
        || !matches!(
            (symbol.result(), result.as_ref()),
            (PreparedAbiResult::Void, Type::Unit) | (PreparedAbiResult::Scalar(_), Type::Int)
        )
    {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    }
    check_domain(domain, &seen, registry, work, span)?;
    for operand in symbol.operands() {
        charge(work, 1, span)?;
        if !matches!(
            (operand.source(), operand.representation()),
            (
                PreparedOperandSource::Source(_) | PreparedOperandSource::Constant(_),
                PreparedRepresentation::Scalar(_)
            ) | (
                PreparedOperandSource::Sentinel(_),
                PreparedRepresentation::FunctionAddressSentinel
            )
        ) {
            return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
        }
        if let PreparedOperandSource::Source(path) = operand.source() {
            check_source_path(domain, path, work, span)?;
        }
    }
    drop(seen);
    Ok(operation)
}

fn charge_owner_names(
    parameters: &[crate::resolved::ResolvedTypeVariable],
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), ForeignAdmissionError> {
    // The existing owner-signature checker prices kinds and origins, but its
    // spelling equality needs this candidate-byte precharge before scanning.
    for parameter in parameters {
        charge(
            work,
            parameter
                .spelling
                .len()
                .checked_add(1)
                .ok_or_else(|| failure(ForeignAdmissionReason::WorkExhausted, span))?,
            span,
        )?;
    }
    Ok(())
}

pub(super) fn check_domain(
    domain: &Type,
    parameters: &HashSet<TypeVariableId>,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), ForeignAdmissionError> {
    let mut pending = Vec::new();
    reserve(&mut pending, 1, work, span)?;
    pending.push(domain);
    while let Some(ty) = pending.pop() {
        charge(work, 1, span)?;
        match ty {
            Type::Int | Type::Unit | Type::Bool | Type::Bytes | Type::String => {}
            Type::Nominal(id) => {
                if let Some(parameters) = registry.nominal_parameters(*id) {
                    // Preserve the ordinary materialized path without traversing
                    // an origin merely to ask for this leaf's kind/arity.
                    if !parameters.is_empty() {
                        return Err(failure(ForeignAdmissionReason::UnsupportedDomain, span));
                    }
                } else {
                    // Opaque imports retain canonical kind/identity without a
                    // declaration or source constructor/representation authority.
                    charge(work, 1, span)?;
                    match registry.nominal_kind(*id) {
                        Some(CanonicalNominalKind::Frozen {
                            kind: Kind::Type, ..
                        }) => {}
                        Some(_) => {
                            return Err(failure(ForeignAdmissionReason::UnsupportedDomain, span));
                        }
                        None => {
                            return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
                        }
                    }
                }
            }
            Type::Variable(id) => {
                charge(work, 1, span)?;
                if !parameters.contains(id)
                    || !registry
                        .type_variable(*id)
                        .is_some_and(|parameter| parameter.kind == Kind::Type)
                {
                    return Err(failure(ForeignAdmissionReason::InvalidParameters, span));
                }
            }
            Type::Tuple(fields) => {
                if fields.len() < 2 {
                    return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
                }
                reserve(&mut pending, fields.len(), work, span)?;
                pending.extend(fields.iter());
            }
            Type::Application(_, _)
            | Type::Inference(_)
            | Type::ResourceApply(_, _)
            | Type::ForeignOwnerApply(_, _)
            | Type::Forall(_, _)
            | Type::Function(_, _)
            | Type::EffectfulFunction(_, _) => {
                return Err(failure(ForeignAdmissionReason::UnsupportedDomain, span));
            }
        }
    }
    Ok(())
}

pub(super) fn check_source_path(
    domain: &Type,
    path: &[usize],
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), ForeignAdmissionError> {
    charge(work, path.len().saturating_add(1), span)?;
    let invalid = || failure(ForeignAdmissionReason::InvalidSourcePosition, span);
    let (first, rest) = path.split_first().ok_or_else(invalid)?;
    let mut selected = match domain {
        Type::Tuple(fields) => fields.get(*first),
        _ if *first == 0 => Some(domain),
        _ => None,
    }
    .ok_or_else(invalid)?;
    for component in rest {
        selected = match selected {
            Type::Tuple(fields) => fields.get(*component),
            _ => None,
        }
        .ok_or_else(invalid)?;
    }
    if !matches!(selected, Type::Int) {
        return Err(invalid());
    }
    Ok(())
}

// Restore a checked member only through the existing canonical binding and
// independent checks.
pub(crate) fn restore_foreign_symbol(
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    symbol_index: usize,
    effect: crate::types::EffectId,
    context: &ForeignBindingContext<'_>,
    work: &mut TypeWorkBudget,
) -> Result<Arc<CheckedForeignSymbol>, ForeignAdmissionError> {
    let span = context.codec.source();
    charge(work, 1, span)?;
    let original = context
        .registry
        .effect(effect)
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidOperation, span))?;
    let symbol = bind_foreign_symbol(library, prepared, symbol_index, original, context, work)?;
    // Binding establishes the complete immutable source correspondence. Final
    // reconstructed Core validation remains the independent crossed-boundary gate.
    charge(work, 1, span)?;
    // This one new original allocation must be retained by all registry tags,
    // NativeInterpretation records and generated bridge members. Restoring an
    // equivalent descriptor separately for the bridge is not permitted.
    Ok(Arc::new(symbol))
}

/// One generated library correspondence check, bound to an immutable registry
/// context and the exact original prepared allocation. This compiler-private
/// brand proves matching normalized construction facts, not external C behavior.
/// It intentionally implements neither Clone nor an unchecked constructor.
pub(crate) struct CheckedExecutableForeignLibrary<'program> {
    proof: ValidatedExecutableRegistry<'program>,
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    target: &'static str,
}

// No constructor accepts an arbitrary registry for the validated variant.
// Borrowing ValidatedEffectProgram is the sole origin of this private proof.
struct ValidatedExecutableRegistry<'program> {
    registry: &'program ResolvedRegistry,
}

/// Exact source member admitted from a generated-library correspondence brand.
/// The evaluator's full actual-instance matching is still an independent gate.
pub(crate) struct CheckedExecutableForeignSymbol {
    original: Arc<CheckedForeignSymbol>,
    target: &'static str,
}

impl CheckedExecutableForeignSymbol {
    pub(crate) const fn target(&self) -> &'static str {
        self.target
    }
    pub(crate) fn into_source(self) -> Arc<CheckedForeignSymbol> {
        self.original
    }
}

pub(crate) fn admit_executable_foreign_symbol(
    library: &CheckedExecutableForeignLibrary<'_>,
    original: &Arc<CheckedForeignSymbol>,
    expected_symbol_index: usize,
    expected_operation: OperationId,
    work: &mut TypeWorkBudget,
) -> Result<CheckedExecutableForeignSymbol, ForeignAdmissionError> {
    let span = match library.prepared.origin() {
        Origin::Source(span) => *span,
        _ => {
            return Err(failure(
                ForeignAdmissionReason::InvalidLibrary,
                original.call_codec().source(),
            ));
        }
    };
    charge(work, 6, span)?;
    let registry = library.proof.registry;
    if original.library() != library.library
        || original.symbol_index() != expected_symbol_index
        || original.operation() != expected_operation
        || !Arc::ptr_eq(original.prepared(), &library.prepared)
        || !registry
            .native_symbol(expected_operation)
            .is_some_and(|sealed| Arc::ptr_eq(sealed, original))
        || !registry
            .effect(original.effect())
            .and_then(|effect| effect.native_contract.as_ref())
            .is_some_and(|sealed| Arc::ptr_eq(sealed, original))
    {
        return Err(failure(ForeignAdmissionReason::InvalidOperation, span));
    }
    // The validated path's inaccessible proof carries the completed independent
    // registry/contract/Core phase; reuse it rather than rewalking signatures.
    charge(work, 1, span)?;
    Ok(CheckedExecutableForeignSymbol {
        original: Arc::clone(original),
        target: library.target,
    })
}

/// Reuses completed independent Effect Core admission for generated dispatch.
/// The caller supplies the validated capability itself, never a raw registry or
/// a boolean declaring that validation happened. All table/tag/Arc membership
/// and expected normalized library facts remain paid checks below this phase.
pub(crate) fn check_executable_foreign_library_in_program<'program>(
    library: NativeLibraryId,
    original: Arc<PreparedForeignLibrary>,
    expected: &PrivateExecutableForeignLibraryParts,
    target: &str,
    program: &'program crate::core::ValidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> Result<CheckedExecutableForeignLibrary<'program>, ForeignAdmissionError> {
    let span = expected.abi.span;
    charge(work, 4, span)?;
    if library.module() != original.module() || library.module() != expected.abi.module {
        return Err(failure(ForeignAdmissionReason::InvalidLibrary, span));
    }
    charge(
        work,
        target
            .len()
            .checked_add(1)
            .ok_or_else(|| failure(ForeignAdmissionReason::WorkExhausted, span))?,
        span,
    )?;
    if target != original.profile() {
        return Err(failure(ForeignAdmissionReason::InvalidLibrary, span));
    }
    let matches =
        super::source_contract::same_prepared_library_parts(&original, &expected.abi, work)
            .map_err(|error| {
                failure(
                    if error.is_resource_exhaustion() {
                        ForeignAdmissionReason::WorkExhausted
                    } else {
                        ForeignAdmissionReason::InvalidLibrary
                    },
                    error.span(),
                )
            })?;
    if !matches {
        return Err(failure(ForeignAdmissionReason::InvalidLibrary, span));
    }
    compare_executable_library_sources(library, &original, expected, program.registry(), work)?;
    let target = original.profile();
    Ok(CheckedExecutableForeignLibrary {
        proof: ValidatedExecutableRegistry {
            registry: program.registry(),
        },
        library,
        prepared: original,
        target,
    })
}

/// Emitter-selected expected library facts decoded through the existing private
/// image coordinates. These records remain untrusted; the owning gate compares
/// the complete library once. The members are ordered by original symbol index.
pub(crate) struct PrivateExecutableForeignLibraryParts {
    pub(crate) abi: super::source_contract::PrivatePreparedLibraryParts,
    pub(crate) members: crate::resolved::ResolvedEffectBuffer,
}

fn compare_executable_library_sources(
    library: NativeLibraryId,
    original: &Arc<PreparedForeignLibrary>,
    expected: &PrivateExecutableForeignLibraryParts,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    let span = expected.abi.span;
    charge(
        work,
        expected
            .members
            .0
            .len()
            .checked_add(1)
            .ok_or_else(|| failure(ForeignAdmissionReason::WorkExhausted, span))?,
        span,
    )?;
    if expected.members.0.len() != original.symbols().len() {
        return Err(failure(ForeignAdmissionReason::InvalidLibrary, span));
    }
    for (index, effect) in expected.members.0.iter().enumerate() {
        charge(work, 7, effect.span)?;
        let [operation] = effect.operations.as_ref() else {
            return Err(failure(
                ForeignAdmissionReason::InvalidOperation,
                effect.span,
            ));
        };
        let symbol = registry
            .native_symbol(operation.id)
            .ok_or_else(|| failure(ForeignAdmissionReason::InvalidOperation, effect.span))?;
        if effect.native_contract.is_some()
            || operation.id != OperationId::new(effect.id, 0)
            || symbol.library() != library
            || symbol.effect() != effect.id
            || symbol.symbol_index() != index
            || !Arc::ptr_eq(symbol.prepared(), original)
            || !registry
                .effect(effect.id)
                .and_then(|effect| effect.native_contract.as_ref())
                .is_some_and(|tag| Arc::ptr_eq(tag, symbol))
            || symbol.parameter_ids().len() != effect.parameters.len()
            || original.symbols()[index].parameters().len() != effect.parameters.len()
            || !symbol
                .same_source_provenance(effect, work)
                .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, effect.span))?
            || !same_type_with_budget(symbol.source_signature(), &operation.annotation.ty, work)
                .map_err(|()| {
                    failure(
                        ForeignAdmissionReason::WorkExhausted,
                        operation.annotation.span,
                    )
                })?
        {
            return Err(failure(
                ForeignAdmissionReason::InvalidOperation,
                effect.span,
            ));
        }
        for ((expected, id), prepared) in effect
            .parameters
            .iter()
            .zip(symbol.parameter_ids())
            .zip(original.symbols()[index].parameters())
        {
            charge(work, 1, effect.span)?;
            if expected.id != *id
                || expected.id.module() != Some(library.module())
                || !matches!(
                    (&expected.kind, prepared.kind()),
                    (Kind::Type, Kind::Type) | (Kind::EffectRow, Kind::EffectRow)
                )
            {
                return Err(failure(
                    ForeignAdmissionReason::InvalidParameters,
                    effect.span,
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        lexer::lex,
        parser::{parse, project_module},
        resolved::{
            ResolvedConstructor, ResolvedEffectOperation, ResolvedNominalType, ResolvedType,
            ResolvedTypeProvenance, ResolvedTypeProvenanceNode, ResolvedTypeVariable,
        },
        source::{ByteRange, SourceFile},
        surface::SurfaceForeignMember,
    };

    const SCALAR: &str = r#"foreign library C {
        profile "x86_64-unknown-linux-gnu"
        repr I32 = signed(32)
        symbol Blend<Before : EffectRow, T, Middle : EffectRow, U> : (Int, (Int, Bool), T, U) -> Foreign.Call<Int> {
            name "blend"
            abi (I32, I32) -> I32
            operand 0 from 0 scalar
            operand 1 from 1.0 scalar
            output result as scalar
            outcome otherwise { readable result }
        }
    }
    "#;

    const VOID: &str = r#"foreign library C {
        profile "x86_64-unknown-linux-gnu"
        symbol Flush : Unit -> Foreign.Call<Unit> {
            name "flush"
            abi () -> void
            outcome otherwise {}
        }
    }
    "#;

    #[derive(Clone, Copy)]
    enum Mutation {
        None,
        DonorModule,
        ReturnedPayload,
        ConstructorRoles,
        CommonOrigin,
        ParameterOrder,
        ScalarPath,
        ScalarCodomain,
        DonorCodomain,
        ExtraOperation,
        UnsupportedDomain,
    }

    struct Fixture {
        prepared: Arc<PreparedForeignLibrary>,
        registry: ResolvedRegistry,
        common_module: ModuleId,
        common_source: Span,
        ids: ForeignCallCodecIds,
        effect: EffectId,
    }

    impl Fixture {
        fn new(text: &str, mutation: Mutation) -> Self {
            let source = SourceFile::new("native-source.ash", text).unwrap();
            let tree = parse(lex(&source).unwrap());
            assert!(tree.parse_diagnostics().is_empty());
            let surface = project_module(&source, &tree).unwrap();
            let module = ModuleId::from(source.id());
            let library = &surface.foreign_libraries[0];
            let symbol = library
                .members
                .iter()
                .find_map(|member| match member {
                    SurfaceForeignMember::Symbol(symbol) => Some(symbol.as_ref()),
                    _ => None,
                })
                .unwrap();
            let prepared = Arc::new(
                if library.checked.is_some() {
                    super::super::source_contract::prepare_checked_foreign_library(module, library)
                } else {
                    super::super::source_contract::prepare_foreign_library(module, library)
                }
                .unwrap(),
            );
            let common = SourceFile::new(
                "@builtin.foreign",
                "pub opaque type ConversionError = HiddenConversionError\npub type Call<T> = Returned(T) | ConversionFailed(ConversionError)\n",
            )
            .unwrap();
            let common_source = common
                .span(ByteRange::new(0, u32::try_from(common.text().len()).unwrap()).unwrap())
                .unwrap();
            let common_module = if matches!(mutation, Mutation::DonorModule) {
                ModuleId::new(73)
            } else {
                ModuleId::builtin_foreign_for_test(73)
            };
            let ids = ForeignCallCodecIds {
                conversion_error: NominalTypeId::new(common_module, 0),
                call: NominalTypeId::new(common_module, 1),
                returned: ConstructorId::new(NominalTypeId::new(common_module, 1), 0),
                conversion_failed: ConstructorId::new(NominalTypeId::new(common_module, 1), 1),
            };
            let call_parameter = ResolvedTypeVariable {
                id: TypeVariableId::resolved(common_module, 0),
                spelling: "T".to_owned(),
                kind: Kind::Type,
                origin: Origin::Source(common_source),
            };
            let origin = if matches!(mutation, Mutation::CommonOrigin) {
                Origin::Source(surface.span)
            } else {
                Origin::Source(common_source)
            };
            let mut call_constructors = vec![ids.returned, ids.conversion_failed];
            if matches!(mutation, Mutation::ConstructorRoles) {
                call_constructors.reverse();
            }
            let nominals = vec![
                ResolvedNominalType {
                    id: ids.conversion_error,
                    declaration_kind: ResolvedNominalDeclarationKind::Data,
                    spelling: "ConversionError".to_owned(),
                    constructors: Box::new([]),
                    representation: None,
                    representation_provenance: None,
                    origin: Origin::Source(common_source),
                },
                ResolvedNominalType {
                    id: ids.call,
                    declaration_kind: ResolvedNominalDeclarationKind::Data,
                    spelling: "Call".to_owned(),
                    constructors: call_constructors.into_boxed_slice(),
                    representation: None,
                    representation_provenance: None,
                    origin,
                },
            ];
            let constructors = vec![
                ResolvedConstructor {
                    id: ids.returned,
                    owner: ids.call,
                    spelling: "Returned".to_owned(),
                    payload: Some(if matches!(mutation, Mutation::ReturnedPayload) {
                        Type::Int
                    } else {
                        Type::Variable(call_parameter.id)
                    }),
                    origin: Origin::Source(common_source),
                },
                ResolvedConstructor {
                    id: ids.conversion_failed,
                    owner: ids.call,
                    spelling: "ConversionFailed".to_owned(),
                    payload: Some(Type::Nominal(ids.conversion_error)),
                    origin: Origin::Source(common_source),
                },
            ];
            let mut parameters: Vec<_> = symbol
                .parameters
                .iter()
                .zip(prepared.symbols()[0].parameters())
                .enumerate()
                .map(|(index, (surface, prepared))| ResolvedTypeVariable {
                    id: TypeVariableId::resolved(module, u32::try_from(index).unwrap()),
                    spelling: surface.name.text.clone(),
                    kind: prepared.kind().clone(),
                    origin: Origin::Source(surface.name.span),
                })
                .collect();
            let void = prepared.symbols()[0].result() == PreparedAbiResult::Void;
            let domain = if void {
                Type::Unit
            } else if matches!(mutation, Mutation::UnsupportedDomain) {
                Type::Function(Box::new(Type::Int), Box::new(Type::Int))
            } else {
                Type::Tuple(
                    vec![
                        Type::Int,
                        Type::Tuple(
                            vec![
                                if matches!(mutation, Mutation::ScalarPath) {
                                    Type::Bool
                                } else {
                                    Type::Int
                                },
                                Type::Bool,
                            ]
                            .into_boxed_slice(),
                        ),
                        Type::Variable(parameters[1].id),
                        Type::Variable(parameters[3].id),
                    ]
                    .into_boxed_slice(),
                )
            };
            if matches!(mutation, Mutation::ParameterOrder) {
                parameters.swap(0, 2);
            }
            let call_id = if matches!(mutation, Mutation::DonorCodomain) {
                NominalTypeId::new(module, 1)
            } else {
                ids.call
            };
            let result = if void || matches!(mutation, Mutation::ScalarCodomain) {
                Type::Unit
            } else {
                Type::Int
            };
            let effect = EffectId::new(module, 4);
            let annotation = ResolvedType {
                ty: Type::Function(
                    Box::new(domain),
                    Box::new(Type::Application(
                        Box::new(Type::Nominal(call_id)),
                        Box::new(result),
                    )),
                ),
                provenance: ResolvedTypeProvenance::new(
                    vec![ResolvedTypeProvenanceNode::Fact(symbol.ty.span)],
                    0,
                ),
                origin: Origin::Source(symbol.ty.span),
                span: symbol.ty.span,
            };
            let operation = ResolvedEffectOperation {
                id: OperationId::new(effect, 0),
                spelling: "call".to_owned(),
                annotation,
                origin: Origin::Source(symbol.name.span),
                span: symbol.span,
            };
            let mut operations = vec![operation];
            if matches!(mutation, Mutation::ExtraOperation) {
                let mut extra = operations[0].clone();
                extra.id = OperationId::new(effect, 1);
                operations.push(extra);
            }
            let registry = ResolvedRegistry::new(nominals, constructors)
                .with_type_parameters(vec![(ids.call, vec![call_parameter])])
                .with_additional_type_variables(parameters.iter().cloned())
                .with_effects(vec![ResolvedEffectDeclaration {
                    native_contract: None,
                    id: effect,
                    public: library.public,
                    spelling: symbol.name.text.clone(),
                    parameters: parameters.into_boxed_slice(),
                    operations: operations.into_boxed_slice(),
                    origin: Origin::Source(symbol.span),
                    span: symbol.span,
                }]);
            Self {
                prepared,
                registry,
                common_module,
                common_source,
                ids,
                effect,
            }
        }

        fn bind(
            &self,
            work: &mut TypeWorkBudget,
        ) -> Result<CheckedForeignSymbol, ForeignAdmissionError> {
            let context = ForeignBindingContext::new(
                &self.registry,
                self.common_module,
                self.common_source,
                self.ids,
                work,
            )?;
            bind_foreign_symbol(
                NativeLibraryId::new(self.prepared.module(), 2),
                Arc::clone(&self.prepared),
                0,
                self.registry.effect(self.effect).unwrap(),
                &context,
                work,
            )
        }
    }

    #[test]
    fn checked_profile_preparation_does_not_authenticate_a_legacy_operation() {
        let text = SCALAR
            .replace("foreign library", "foreign checked library")
            .replace(
                "operand 0 from 0 scalar",
                "host T\n            assumes {}\n            operand 0 from 0 scalar",
            );
        let original = Fixture::new(SCALAR, Mutation::None);
        assert!(original.bind(&mut TypeWorkBudget::default()).is_ok());
        // Even matching legacy codec/signature facts cannot erase checked intent.
        let checked = Fixture::new(&text, Mutation::None);
        assert!(checked.prepared.checked_contract().is_some());
        assert_eq!(
            checked
                .bind(&mut TypeWorkBudget::default())
                .unwrap_err()
                .reason(),
            ForeignAdmissionReason::InvalidLibrary
        );
    }

    #[test]
    fn binds_original_scalar_operation_and_retains_preparation_and_complete_binders() {
        let fixture = Fixture::new(SCALAR, Mutation::None);
        let checked = fixture.bind(&mut TypeWorkBudget::default()).unwrap();
        assert!(Arc::ptr_eq(checked.prepared(), &fixture.prepared));
        assert_eq!(checked.library().module(), fixture.prepared.module());
        assert_eq!(checked.library().ordinal(), 2);
        assert_eq!(checked.symbol_index(), 0);
        assert_eq!(checked.operation(), OperationId::new(fixture.effect, 0));
        assert_eq!(checked.effect(), fixture.effect);
        assert_eq!(
            checked.parameter_ids(),
            &[
                TypeVariableId::resolved(fixture.prepared.module(), 0),
                TypeVariableId::resolved(fixture.prepared.module(), 1),
                TypeVariableId::resolved(fixture.prepared.module(), 2),
                TypeVariableId::resolved(fixture.prepared.module(), 3),
            ]
        );
        assert_eq!(checked.symbol().native_type_projection(), &[1, 3]);
        assert_eq!(checked.call_codec().ids(), fixture.ids);
        assert_eq!(checked.call_codec().module(), fixture.common_module);
        assert_eq!(checked.call_codec().source(), fixture.common_source);
        assert_eq!(
            checked.source_signature(),
            &fixture.registry.effect(fixture.effect).unwrap().operations[0]
                .annotation
                .ty
        );
    }

    #[test]
    fn independent_core_native_membership_lookup_is_paid_for_source_contracts() {
        use crate::core::validate::registered_foreign_effect_with_charge as lookup;

        let mut fixture = Fixture::new(SCALAR, Mutation::None);
        let mut admission = TypeWorkBudget::default();
        let checked = Arc::new(fixture.bind(&mut admission).unwrap());
        fixture
            .registry
            .retain_native_symbol(checked, &mut admission)
            .unwrap();
        assert!(fixture.registry.foreign_modules().next().is_none());

        let mut exhausted = TypeWorkBudget::with_limit(0);
        assert_eq!(
            lookup(&fixture.registry, fixture.effect, |cells| exhausted
                .charge(cells)),
            Err(()),
        );
        let mut exact = TypeWorkBudget::with_limit(1);
        assert!(
            lookup(&fixture.registry, fixture.effect, |cells| exact
                .charge(cells))
            .unwrap()
        );
        assert_eq!(exact.used(), 1);
        let mut ordinary = TypeWorkBudget::with_limit(1);
        assert!(
            !lookup(
                &fixture.registry,
                EffectId::new(fixture.prepared.module(), 0),
                |cells| ordinary.charge(cells)
            )
            .unwrap()
        );
        assert_eq!(ordinary.used(), 1);
    }

    #[test]
    fn binds_zero_operand_void_result_to_canonical_call_unit() {
        let fixture = Fixture::new(VOID, Mutation::None);
        let checked = fixture.bind(&mut TypeWorkBudget::default()).unwrap();
        assert!(checked.symbol().operands().is_empty());
        assert!(checked.parameter_ids().is_empty());
        assert_eq!(checked.symbol().result(), PreparedAbiResult::Void);
        assert!(
            matches!(checked.source_signature(), Type::Function(domain, _) if matches!(domain.as_ref(), Type::Unit))
        );
    }

    #[test]
    fn imported_opaque_error_and_display_aliases_preserve_canonical_call_authority() {
        let fixture = Fixture::new(SCALAR, Mutation::None);
        let mut nominals: Vec<_> = fixture
            .registry
            .nominals()
            .iter()
            .filter(|nominal| nominal.id == fixture.ids.call)
            .cloned()
            .collect();
        nominals[0].spelling = "Alias.Result".to_owned();
        let mut constructors = fixture.registry.constructors().to_vec();
        constructors[0].spelling = "Alias.Success".to_owned();
        constructors[1].spelling = "Alias.Failure".to_owned();
        let effect = fixture.registry.effect(fixture.effect).unwrap();
        let base = ResolvedRegistry::new(nominals, constructors)
            .with_type_parameters(vec![(
                fixture.ids.call,
                fixture
                    .registry
                    .nominal_parameters(fixture.ids.call)
                    .unwrap()
                    .to_vec(),
            )])
            .with_additional_type_variables(effect.parameters.iter().cloned())
            .with_effects(vec![effect.clone()]);
        let mut imported = crate::resolved::ImportedFacts::default();
        let mut work = TypeWorkBudget::default();
        imported
            .merge_nominal(
                crate::resolved::ImportedNominalFact {
                    id: fixture.ids.conversion_error,
                    declaration_kind: ResolvedNominalDeclarationKind::Data,
                    parameter_count: 0,
                    constructor_count: 1,
                    parameters: Box::new([]),
                    representation: None,
                    representation_provenance: None,
                    constructors: Box::new([]),
                    access: crate::resolved::ImportedTypeAccess::Opaque,
                    display_spelling: Some("Alias.FailureDetail".to_owned()),
                    display_is_private: false,
                    origin: Origin::Source(fixture.common_source),
                },
                &mut work,
            )
            .unwrap();
        let consuming = base.checker_view(&imported, &mut work).unwrap();
        assert!(consuming.nominal(fixture.ids.conversion_error).is_none());
        assert!(matches!(
            consuming.nominal_kind(fixture.ids.conversion_error),
            Some(CanonicalNominalKind::Frozen {
                kind: Kind::Type,
                ..
            })
        ));
        let context = ForeignBindingContext::new(
            &consuming,
            fixture.common_module,
            fixture.common_source,
            fixture.ids,
            &mut work,
        )
        .unwrap();
        let checked = bind_foreign_symbol(
            NativeLibraryId::new(fixture.prepared.module(), 2),
            Arc::clone(&fixture.prepared),
            0,
            consuming.effect(fixture.effect).unwrap(),
            &context,
            &mut work,
        )
        .unwrap();
        authenticate_foreign_symbol(&checked, &consuming, &context, &mut work).unwrap();
        assert_eq!(checked.call_codec().ids(), fixture.ids);
    }

    #[test]
    fn refuses_same_shaped_donor_modules_and_corrupt_common_codec_roles() {
        for mutation in [
            Mutation::DonorModule,
            Mutation::ReturnedPayload,
            Mutation::ConstructorRoles,
            Mutation::CommonOrigin,
        ] {
            assert_eq!(
                Fixture::new(SCALAR, mutation)
                    .bind(&mut TypeWorkBudget::default())
                    .err()
                    .unwrap()
                    .reason(),
                ForeignAdmissionReason::InvalidCodec
            );
        }
    }

    #[test]
    fn refuses_resolved_source_disagreement_and_unsupported_domain_forms() {
        for (mutation, reason) in [
            (
                Mutation::ParameterOrder,
                ForeignAdmissionReason::InvalidParameters,
            ),
            (
                Mutation::ScalarPath,
                ForeignAdmissionReason::InvalidSourcePosition,
            ),
            (
                Mutation::ScalarCodomain,
                ForeignAdmissionReason::InvalidSignature,
            ),
            (
                Mutation::DonorCodomain,
                ForeignAdmissionReason::InvalidSignature,
            ),
            (
                Mutation::ExtraOperation,
                ForeignAdmissionReason::InvalidOperation,
            ),
            (
                Mutation::UnsupportedDomain,
                ForeignAdmissionReason::UnsupportedDomain,
            ),
        ] {
            assert_eq!(
                Fixture::new(SCALAR, mutation)
                    .bind(&mut TypeWorkBudget::default())
                    .err()
                    .unwrap()
                    .reason(),
                reason
            );
        }
    }

    #[test]
    fn a_same_shaped_effect_copy_is_not_the_original_registry_operation() {
        let fixture = Fixture::new(SCALAR, Mutation::None);
        let mut work = TypeWorkBudget::default();
        let context = ForeignBindingContext::new(
            &fixture.registry,
            fixture.common_module,
            fixture.common_source,
            fixture.ids,
            &mut work,
        )
        .unwrap();
        let copied = fixture.registry.effect(fixture.effect).unwrap().clone();
        let refused = bind_foreign_symbol(
            NativeLibraryId::new(fixture.prepared.module(), 2),
            Arc::clone(&fixture.prepared),
            0,
            &copied,
            &context,
            &mut work,
        )
        .err()
        .unwrap();
        assert_eq!(refused.reason(), ForeignAdmissionReason::InvalidOperation);
        assert_eq!(refused.span(), copied.span);
    }

    #[test]
    fn independent_authentication_accepts_a_fresh_context_and_rejects_altered_sealed_facts() {
        let fixture = Fixture::new(SCALAR, Mutation::None);
        let mut sealed = fixture.bind(&mut TypeWorkBudget::default()).unwrap();
        let mut work = TypeWorkBudget::default();
        let context = ForeignBindingContext::new(
            &fixture.registry,
            fixture.common_module,
            fixture.common_source,
            fixture.ids,
            &mut work,
        )
        .unwrap();
        assert!(!Arc::ptr_eq(sealed.call_codec(), &context.codec));
        authenticate_foreign_symbol(&sealed, &fixture.registry, &context, &mut work).unwrap();

        sealed.parameter_ids.swap(0, 2);
        assert_eq!(
            authenticate_foreign_symbol(&sealed, &fixture.registry, &context, &mut work)
                .unwrap_err()
                .reason(),
            ForeignAdmissionReason::InvalidParameters,
        );
        sealed.parameter_ids.swap(0, 2);
        sealed.source_signature.replace(Type::Function(
            Box::new(Type::Int),
            Box::new(Type::Application(
                Box::new(Type::Nominal(fixture.ids.call)),
                Box::new(Type::Int),
            )),
        ));
        assert_eq!(
            authenticate_foreign_symbol(&sealed, &fixture.registry, &context, &mut work)
                .unwrap_err()
                .reason(),
            ForeignAdmissionReason::InvalidSignature,
        );
    }

    #[test]
    fn independent_authentication_rejects_a_changed_unused_domain_and_registry_context_mismatch() {
        let fixture = Fixture::new(SCALAR, Mutation::None);
        let sealed = fixture.bind(&mut TypeWorkBudget::default()).unwrap();
        let mut work = TypeWorkBudget::default();
        let mut consuming = fixture.registry;
        let mut effects = consuming.effects().to_vec();
        let Type::Function(domain, _) = &mut effects[0].operations[0].annotation.ty else {
            unreachable!();
        };
        let Type::Tuple(fields) = domain.as_mut() else {
            unreachable!();
        };
        let Type::Tuple(nested) = &mut fields[1] else {
            unreachable!();
        };
        nested[1] = Type::Unit;
        consuming = consuming.replace_effects_for_core_test(effects);
        let context = ForeignBindingContext::new(
            &consuming,
            fixture.common_module,
            fixture.common_source,
            fixture.ids,
            &mut work,
        )
        .unwrap();
        assert_eq!(
            authenticate_foreign_symbol(&sealed, &consuming, &context, &mut work)
                .unwrap_err()
                .reason(),
            ForeignAdmissionReason::InvalidSignature,
        );
        assert_eq!(
            authenticate_foreign_symbol(
                &sealed,
                &Fixture::new(SCALAR, Mutation::None).registry,
                &context,
                &mut work,
            )
            .unwrap_err()
            .reason(),
            ForeignAdmissionReason::InvalidCodec,
        );
    }

    #[test]
    fn independent_authentication_has_an_exact_budget_and_fresh_retry() {
        let fixture = Fixture::new(SCALAR, Mutation::None);
        let sealed = fixture.bind(&mut TypeWorkBudget::default()).unwrap();
        let context = ForeignBindingContext::new(
            &fixture.registry,
            fixture.common_module,
            fixture.common_source,
            fixture.ids,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        let mut measured = TypeWorkBudget::default();
        authenticate_foreign_symbol(&sealed, &fixture.registry, &context, &mut measured).unwrap();
        let exact = measured.used();
        authenticate_foreign_symbol(
            &sealed,
            &fixture.registry,
            &context,
            &mut TypeWorkBudget::with_limit(exact),
        )
        .unwrap();
        for limit in [0, exact / 2, exact - 1] {
            assert_eq!(
                authenticate_foreign_symbol(
                    &sealed,
                    &fixture.registry,
                    &context,
                    &mut TypeWorkBudget::with_limit(limit),
                )
                .unwrap_err()
                .reason(),
                ForeignAdmissionReason::WorkExhausted,
            );
        }
        let mut retry = TypeWorkBudget::with_limit(exact);
        authenticate_foreign_symbol(&sealed, &fixture.registry, &context, &mut retry).unwrap();
        assert_eq!(retry.used(), exact);
    }

    #[test]
    fn shared_context_authenticates_once_and_exact_binding_budgets_retry_fresh() {
        let prefix = format!("Foreign{}", "x".repeat(256));
        let long_names = SCALAR
            .replace("Blend", &format!("{prefix}0"))
            .replace("Before", &format!("{prefix}1"))
            .replace("Middle", &format!("{prefix}2"));
        for text in [SCALAR, long_names.as_str()] {
            let fixture = Fixture::new(text, Mutation::None);
            let mut measured = TypeWorkBudget::default();
            let baseline = fixture.bind(&mut measured).unwrap();
            let exact = measured.used();
            let checked = fixture
                .bind(&mut TypeWorkBudget::with_limit(exact))
                .unwrap();
            assert_eq!(checked.operation(), baseline.operation());
            assert_ne!(checked, baseline);
            for limit in [0, exact / 2, exact - 1] {
                let refused = fixture
                    .bind(&mut TypeWorkBudget::with_limit(limit))
                    .err()
                    .unwrap();
                assert_eq!(refused.reason(), ForeignAdmissionReason::WorkExhausted);
                assert!(refused.is_resource_exhaustion());
            }
            let mut retry = TypeWorkBudget::with_limit(exact);
            assert_eq!(
                fixture.bind(&mut retry).unwrap().operation(),
                baseline.operation()
            );
            assert_eq!(retry.used(), exact);
        }
        let fixture = Fixture::new(SCALAR, Mutation::None);
        let mut shared = TypeWorkBudget::default();
        let context = ForeignBindingContext::new(
            &fixture.registry,
            fixture.common_module,
            fixture.common_source,
            fixture.ids,
            &mut shared,
        )
        .unwrap();
        let before = shared.used();
        let bind = |work: &mut TypeWorkBudget| {
            bind_foreign_symbol(
                NativeLibraryId::new(fixture.prepared.module(), 2),
                Arc::clone(&fixture.prepared),
                0,
                fixture.registry.effect(fixture.effect).unwrap(),
                &context,
                work,
            )
        };
        let first = bind(&mut shared).unwrap();
        let first_work = shared.used() - before;
        let second = bind(&mut shared).unwrap();
        assert_eq!(shared.used() - before, 2 * first_work);
        assert!(Arc::ptr_eq(first.call_codec(), second.call_codec()));
        assert_eq!(first, second);
    }
}

#[cfg(test)]
#[path = "checked_source/checked_borrow_tests.rs"]
mod checked_borrow_tests;
