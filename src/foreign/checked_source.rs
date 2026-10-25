//! Ordinary checked source signatures mapped to data-pointer/void C calls.
use super::source_contract::{PreparedForeignLibrary, PreparedForeignSymbol};
use crate::{
    module::ModuleId,
    resolved::{ResolvedEffectDeclaration, ResolvedRegistry},
    source::Span,
    types::{
        EffectId, IterativeTypeOwner, NominalTypeId, OperationId, Type, TypeVariableId,
        TypeWorkBudget, clone_type_with_budget, same_type_with_budget,
    },
};
use std::{fmt, sync::Arc};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NativeLibraryId {
    module: ModuleId,
    ordinal: u32,
}
impl NativeLibraryId {
    pub const fn new(module: ModuleId, ordinal: u32) -> Self {
        Self { module, ordinal }
    }
    pub const fn module(self) -> ModuleId {
        self.module
    }
    pub const fn ordinal(self) -> u32 {
        self.ordinal
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeArgument {
    Address,
    Bytes,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeResult {
    Address,
    Void,
}

pub struct CheckedForeignSymbol {
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    symbol_index: usize,
    operation: OperationId,
    source_signature: IterativeTypeOwner,
    arguments: Box<[NativeArgument]>,
    result: NativeResult,
    operation_span: Span,
}
impl PartialEq for CheckedForeignSymbol {
    fn eq(&self, other: &Self) -> bool {
        self.library == other.library
            && self.symbol_index == other.symbol_index
            && self.operation == other.operation
            && Arc::ptr_eq(&self.prepared, &other.prepared)
    }
}
impl Eq for CheckedForeignSymbol {}
impl CheckedForeignSymbol {
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
        &[]
    }
    pub(crate) fn source_signature(&self) -> &Type {
        &self.source_signature
    }
    pub(crate) fn arguments(&self) -> &[NativeArgument] {
        &self.arguments
    }
    pub(crate) const fn result(&self) -> NativeResult {
        self.result
    }
    pub(crate) fn same_source_provenance(
        &self,
        effect: &ResolvedEffectDeclaration,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        work.charge(effect.operations.len().saturating_add(1))?;
        let Some(operation) = effect.operations.first() else {
            return Ok(false);
        };
        Ok(effect.id == self.effect()
            && effect.parameters.is_empty()
            && effect.operations.len() == 1
            && effect.spelling == self.symbol().name()
            && operation.id == self.operation
            && operation.spelling == "call"
            && operation.span == self.operation_span
            && same_type_with_budget(&operation.annotation.ty, &self.source_signature, work)?)
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ForeignAdmissionReason {
    InvalidLibrary,
    InvalidOperation,
    InvalidSignature,
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
}
impl fmt::Display for ForeignAdmissionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "unsupported or inconsistent foreign signature: {:?}",
            self.reason
        )
    }
}
impl std::error::Error for ForeignAdmissionError {}
fn failure(reason: ForeignAdmissionReason, span: Span) -> ForeignAdmissionError {
    ForeignAdmissionError { reason, span }
}

pub(crate) struct ForeignBindingContext<'a> {
    pub(crate) registry: &'a ResolvedRegistry,
}
impl<'a> ForeignBindingContext<'a> {
    pub(crate) const fn new(registry: &'a ResolvedRegistry) -> Self {
        Self { registry }
    }
}
fn argument(ty: &Type) -> Option<NativeArgument> {
    match ty {
        Type::Bytes => Some(NativeArgument::Bytes),
        Type::Nominal(id) if id.module().is_builtin_foreign() && id.declaration() == 0 => {
            Some(NativeArgument::Address)
        }
        _ => None,
    }
}
pub(crate) fn bind_foreign_symbol(
    library: NativeLibraryId,
    prepared: Arc<PreparedForeignLibrary>,
    symbol_index: usize,
    effect: &ResolvedEffectDeclaration,
    context: &ForeignBindingContext<'_>,
    work: &mut TypeWorkBudget,
) -> Result<CheckedForeignSymbol, ForeignAdmissionError> {
    let span = effect.span;
    work.charge(
        effect
            .parameters
            .len()
            .saturating_add(effect.operations.len())
            .saturating_add(1),
    )
    .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?;
    let symbol = prepared
        .symbols()
        .get(symbol_index)
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidLibrary, span))?;
    let operation = effect
        .operations
        .first()
        .ok_or_else(|| failure(ForeignAdmissionReason::InvalidOperation, span))?;
    if library.module() != prepared.module()
        || effect.id.module() != library.module()
        || !effect.parameters.is_empty()
        || effect.operations.len() != 1
        || operation.id.owner() != effect.id
        || operation.spelling != "call"
        || symbol.name() != effect.spelling
        || context.registry.effect(effect.id).is_none()
    {
        return Err(failure(ForeignAdmissionReason::InvalidOperation, span));
    }
    let Type::Function(domain, result) = &operation.annotation.ty else {
        return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
    };
    let fields: &[Type] = match domain.as_ref() {
        Type::Unit => &[],
        Type::Tuple(fields) if fields.len() >= 2 => fields.as_ref(),
        other => std::slice::from_ref(other),
    };
    work.charge(fields.len())
        .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, span))?;
    let mut arguments = Vec::new();
    arguments
        .try_reserve_exact(fields.len())
        .map_err(|_| failure(ForeignAdmissionReason::StorageRefused, span))?;
    for field in fields {
        arguments.push(
            argument(field)
                .ok_or_else(|| failure(ForeignAdmissionReason::InvalidSignature, span))?,
        );
    }
    let result = match result.as_ref() {
        Type::Unit => NativeResult::Void,
        ty if argument(ty) == Some(NativeArgument::Address) => NativeResult::Address,
        _ => return Err(failure(ForeignAdmissionReason::InvalidSignature, span)),
    };
    // The Address nominal must be the ordinary opaque declaration from the builtin module.
    for field in fields
        .iter()
        .chain(operation.annotation.ty.function_view().map(|f| f.value()))
    {
        if let Type::Nominal(id) = field {
            if id.module().is_builtin_foreign()
                && (*id != NominalTypeId::new(id.module(), 0)
                    || context.registry.nominal_kind(*id).is_none())
            {
                return Err(failure(ForeignAdmissionReason::InvalidSignature, span));
            }
        }
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
        source_signature,
        arguments: arguments.into_boxed_slice(),
        result,
        operation_span: operation.span,
    })
}
pub(crate) fn authenticate_foreign_symbol(
    symbol: &CheckedForeignSymbol,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignAdmissionError> {
    let effect = registry.effect(symbol.effect()).ok_or_else(|| {
        failure(
            ForeignAdmissionReason::InvalidOperation,
            symbol.operation_span,
        )
    })?;
    if registry
        .native_symbol(symbol.operation())
        .is_none_or(|original| !std::ptr::eq(original.as_ref(), symbol))
        || !symbol
            .same_source_provenance(effect, work)
            .map_err(|()| failure(ForeignAdmissionReason::WorkExhausted, symbol.operation_span))?
    {
        return Err(failure(
            ForeignAdmissionReason::InvalidOperation,
            symbol.operation_span,
        ));
    }
    Ok(())
}

impl fmt::Debug for CheckedForeignSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CheckedForeignSymbol")
            .field("operation", &self.operation)
            .field("source_signature", &*self.source_signature)
            .field("arguments", &self.arguments)
            .field("result", &self.result)
            .finish()
    }
}
