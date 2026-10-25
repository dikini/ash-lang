//! Linked callbacks associated with the ordinary checked symbol identities.
use super::{
    checked_source::CheckedForeignSymbol,
    source_runtime::{NativeArgument, NativeCallback, NativeReply},
};
use crate::{
    core::ValidatedEffectProgram,
    eval::RuntimeFailure,
    types::{OperationId, TypeWorkBudget},
};
use std::{collections::HashMap, sync::Arc};

#[derive(Debug)]
struct NativeBinding {
    symbol: Arc<CheckedForeignSymbol>,
    callback: NativeCallback,
}
/// Callbacks supplied by the generated linked host.
#[derive(Debug, Default)]
pub struct SourceNativeBindings {
    entries: HashMap<OperationId, NativeBinding>,
    pub(crate) tuple_storage: Option<crate::eval::NativeTupleAdapter>,
}
impl SourceNativeBindings {
    pub(crate) fn insert(
        &mut self,
        symbol: Arc<CheckedForeignSymbol>,
        callback: NativeCallback,
        work: &mut TypeWorkBudget,
    ) -> Result<(), RuntimeFailure> {
        work.charge(1)
            .map_err(|()| RuntimeFailure::ForeignBinding)?;
        self.entries
            .try_reserve(1)
            .map_err(|_| RuntimeFailure::ForeignBinding)?;
        if self.entries.contains_key(&symbol.operation()) {
            return Err(RuntimeFailure::ForeignBinding);
        }
        self.entries
            .insert(symbol.operation(), NativeBinding { symbol, callback });
        Ok(())
    }
    pub(crate) fn invoke(
        &self,
        symbol: &Arc<CheckedForeignSymbol>,
        arguments: &[NativeArgument],
    ) -> Result<NativeReply, RuntimeFailure> {
        let binding = self
            .entries
            .get(&symbol.operation())
            .ok_or(RuntimeFailure::ForeignBinding)?;
        if !Arc::ptr_eq(symbol, &binding.symbol) {
            return Err(RuntimeFailure::ForeignBinding);
        }
        (binding.callback)(arguments).map_err(|_| RuntimeFailure::ForeignBinding)
    }
}
/// The existing program/callback association, not evidence about foreign behavior.
#[derive(Debug)]
pub struct AdmittedSourceNativeProgram<'program, 'bindings> {
    pub(crate) program: &'program ValidatedEffectProgram,
    pub(crate) bindings: &'bindings SourceNativeBindings,
}
impl<'program, 'bindings> AdmittedSourceNativeProgram<'program, 'bindings> {
    pub(crate) fn into_parts(
        self,
    ) -> (
        &'program ValidatedEffectProgram,
        &'bindings SourceNativeBindings,
    ) {
        (self.program, self.bindings)
    }
}
pub(crate) fn admit_source_native_program<'p, 'b>(
    program: &'p ValidatedEffectProgram,
    bindings: &'b SourceNativeBindings,
    work: &mut TypeWorkBudget,
) -> Result<AdmittedSourceNativeProgram<'p, 'b>, RuntimeFailure> {
    for (operation, binding) in &bindings.entries {
        work.charge(1)
            .map_err(|()| RuntimeFailure::ForeignBinding)?;
        if program
            .registry()
            .native_symbol(*operation)
            .is_none_or(|symbol| !Arc::ptr_eq(symbol, &binding.symbol))
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
    }
    Ok(AdmittedSourceNativeProgram { program, bindings })
}
