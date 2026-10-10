//! Source-native executable bindings and the pre-execution admission receipt.
//! Only a sealed, independently checked executable member can enter this table.

use std::{collections::HashMap, sync::Arc};

use crate::{
    core::{EffectExprKind, EffectOperation, ValidatedEffectProgram},
    eval::{ResourceFailure, ResourceFailureCause, RuntimeFailure, RuntimePhase, RuntimeResource},
    foreign::{
        checked_source::{CheckedExecutableForeignSymbol, CheckedForeignSymbol},
        source_runtime::{NativeScalarCallError, NativeScalarReply, NativeScalarValue},
    },
    module::ModuleId,
    resolved::{ResolvedNominalDeclarationKind, ResolvedRegistry},
    source::{Origin, Span},
    types::{ConstructorId, EffectInstance, Kind, KindedArgument, TypeWorkBudget},
};

pub(crate) type NativeScalarCallback =
    fn(&[NativeScalarValue]) -> Result<NativeScalarReply, NativeScalarCallError>;

#[derive(Debug)]
pub(crate) struct SourceScalarBinding {
    symbol: Arc<CheckedForeignSymbol>,
    target: &'static str,
    callback: NativeScalarCallback,
}

/// Opaque supplied bindings. Empty construction grants no executable authority.
#[derive(Debug, Default)]
pub struct SourceNativeBindings {
    entries: HashMap<crate::types::OperationId, SourceScalarBinding>,
}

impl SourceNativeBindings {
    /// This crate-private constructor consumes the sealed executable member and
    /// emitter-provided typed callback. No arbitrary source descriptor or name
    /// can register a callback through the public API.
    pub(crate) fn insert_checked(
        &mut self,
        sealed: CheckedExecutableForeignSymbol,
        callback: NativeScalarCallback,
        work: &mut TypeWorkBudget,
    ) -> Result<(), RuntimeFailure> {
        paid(work, 2)?;
        let target = sealed.target();
        if target != "x86_64-unknown-linux-gnu" {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let symbol = sealed.into_source();
        if !symbol.prepared().owners().is_empty()
            || !matches!(
                symbol.symbol().call(),
                super::source_contract::PreparedForeignCall::Scalar { .. }
            )
            || matches!(
                symbol.symbol().result(),
                super::source_contract::PreparedAbiResult::Address(_)
            )
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        // Subset admission inspects only borrowed normalized metadata; it does
        // not prepare another ABI or normalize library policy again.
        paid(work, symbol.symbol().operands().len())?;
        if symbol.symbol().operands().iter().any(|operand| {
            !matches!(
                operand.source(),
                super::source_contract::PreparedOperandSource::Source(_)
            ) || !matches!(
                operand.representation(),
                super::source_contract::PreparedRepresentation::Scalar(_)
            )
        }) {
            return Err(RuntimeFailure::ForeignBinding);
        }
        if self.entries.contains_key(&symbol.operation()) {
            return Err(RuntimeFailure::ForeignBinding);
        }
        self.entries.try_reserve(1).map_err(|_| storage(1))?;
        self.entries.insert(
            symbol.operation(),
            SourceScalarBinding {
                symbol,
                target,
                callback,
            },
        );
        Ok(())
    }

    pub(crate) fn request<'bindings>(
        &'bindings self,
        symbol: &Arc<CheckedForeignSymbol>,
        instance: EffectInstance,
        hidden_error: ConstructorId,
        work: &mut TypeWorkBudget,
    ) -> Result<AdmittedSourceScalarInvocation<'bindings>, RuntimeFailure> {
        paid(work, 2)?;
        let binding = self
            .entries
            .get(&symbol.operation())
            .ok_or(RuntimeFailure::ForeignBinding)?;
        if !Arc::ptr_eq(symbol, &binding.symbol)
            || instance.effect() != symbol.effect()
            || binding.target != "x86_64-unknown-linux-gnu"
            || hidden_error != ConstructorId::new(symbol.call_codec().ids().conversion_error, 0)
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let parameters = symbol.symbol().parameters();
        paid(work, parameters.len())?;
        if instance.arguments().len() != parameters.len()
            || symbol.parameter_ids().len() != parameters.len()
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        // Final independent Core validation and Instantiation::effect already
        // check kind formation/substitution. Retain and recheck ALL ordered tags;
        // unsupported higher-kinded source-native parameters remain explicit.
        let projection = symbol.symbol().native_type_projection();
        let mut native = 0;
        // The parameter-count precharge pays this complete ordered scan. Check
        // the derived Type-only projection here without rescanning phantom rows.
        for (index, (parameter, actual)) in parameters.iter().zip(instance.arguments()).enumerate()
        {
            if !matches!(
                (parameter.kind(), actual),
                (Kind::Type, KindedArgument::TypeArg(_))
                    | (Kind::EffectRow, KindedArgument::RowArg(_))
            ) {
                return Err(RuntimeFailure::ForeignBinding);
            }
            if matches!(actual, KindedArgument::TypeArg(_)) {
                paid(work, 1)?;
                if projection.get(native) != Some(&index) {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                native += 1;
            }
        }
        if native != projection.len() {
            return Err(RuntimeFailure::ForeignBinding);
        }
        Ok(AdmittedSourceScalarInvocation {
            binding,
            _instance: instance,
            hidden_error,
        })
    }
}

/// Non-Clone per-request receipt. Private fields retain exact executable/source
/// authority and the complete instantiated vector through result publication.
#[derive(Debug)]
pub(crate) struct AdmittedSourceScalarInvocation<'bindings> {
    binding: &'bindings SourceScalarBinding,
    _instance: EffectInstance,
    hidden_error: ConstructorId,
}

impl<'bindings> AdmittedSourceScalarInvocation<'bindings> {
    pub(crate) fn symbol(&self) -> &Arc<CheckedForeignSymbol> {
        &self.binding.symbol
    }
    pub(crate) fn result(&self) -> super::source_contract::PreparedAbiResult {
        self.binding.symbol.symbol().result()
    }
    pub(crate) fn returned_constructor(&self) -> ConstructorId {
        self.binding.symbol.call_codec().ids().returned
    }
    pub(crate) fn conversion_failed_constructor(&self) -> ConstructorId {
        self.binding.symbol.call_codec().ids().conversion_failed
    }
    pub(crate) fn hidden_error_constructor(&self) -> ConstructorId {
        self.hidden_error
    }
    pub(crate) fn invoke(
        self,
        values: &[NativeScalarValue],
    ) -> Result<(SourceScalarReturnedAuthority<'bindings>, NativeScalarReply), NativeScalarCallError>
    {
        let raw = (self.binding.callback)(values)?;
        Ok((
            SourceScalarReturnedAuthority {
                _binding: self.binding,
                _instance: self._instance,
            },
            raw,
        ))
    }
}

/// Consuming invocation yields this non-Clone retention receipt with NO invoke
/// method. Returned/Recorded can retain original authority without any callback
/// capability, preventing replay even inside later phase APIs.
#[derive(Debug)]
pub(crate) struct SourceScalarReturnedAuthority<'bindings> {
    _binding: &'bindings SourceScalarBinding,
    _instance: EffectInstance,
}

/// Immutable program and table borrow prevent registry/binding mutation between
/// pre-execution admission and evaluator use. Construction is restricted below.
#[derive(Debug)]
pub struct AdmittedSourceNativeProgram<'program, 'bindings> {
    program: &'program ValidatedEffectProgram,
    bindings: &'bindings mut SourceNativeBindings,
    errors: HashMap<ModuleId, ConstructorId>,
}

impl<'program, 'bindings> AdmittedSourceNativeProgram<'program, 'bindings> {
    pub(crate) fn into_parts(
        self,
    ) -> (
        &'program ValidatedEffectProgram,
        &'bindings mut SourceNativeBindings,
        HashMap<ModuleId, ConstructorId>,
    ) {
        (self.program, self.bindings, self.errors)
    }
}

pub(crate) fn admit_source_native_program<'program, 'bindings>(
    program: &'program ValidatedEffectProgram,
    bindings: &'bindings mut SourceNativeBindings,
    work: &mut TypeWorkBudget,
) -> Result<AdmittedSourceNativeProgram<'program, 'bindings>, RuntimeFailure> {
    let mut errors = HashMap::new();
    for node in program.nodes() {
        paid(work, 1)?;
        let EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) = &node.kind
        else {
            continue;
        };
        if !boundary.interpretations().is_empty()
            && !cfg!(all(
                target_arch = "x86_64",
                target_os = "linux",
                target_env = "gnu",
                target_pointer_width = "64"
            ))
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        for interpretation in boundary.interpretations() {
            paid(work, 3)?;
            let symbol = interpretation.symbol();
            let bound = bindings
                .entries
                .get(&symbol.operation())
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let canonical = program
                .registry()
                .native_symbol(symbol.operation())
                .ok_or(RuntimeFailure::ForeignBinding)?;
            let effect = program
                .registry()
                .effect(symbol.effect())
                .ok_or(RuntimeFailure::ForeignBinding)?;
            if !Arc::ptr_eq(&bound.symbol, symbol)
                || !Arc::ptr_eq(canonical, symbol)
                || effect
                    .native_contract
                    .as_ref()
                    .is_none_or(|tag| !Arc::ptr_eq(tag, symbol))
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
            let module = symbol.call_codec().module();
            paid(work, 1)?;
            if !errors.contains_key(&module) {
                let id = authenticate_hidden_error(program.registry(), symbol, work)?;
                errors.try_reserve(1).map_err(|_| storage(1))?;
                errors.insert(module, id);
            }
        }
    }
    Ok(AdmittedSourceNativeProgram {
        program,
        bindings,
        errors,
    })
}

pub(crate) fn reject_missing_source_bindings(
    program: &ValidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> Result<(), RuntimeFailure> {
    for node in program.nodes() {
        paid(work, 1)?;
        if let EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) = &node.kind
            && !boundary.interpretations().is_empty()
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
    }
    Ok(())
}

fn authenticate_hidden_error(
    registry: &ResolvedRegistry,
    symbol: &CheckedForeignSymbol,
    work: &mut TypeWorkBudget,
) -> Result<ConstructorId, RuntimeFailure> {
    paid(work, 4)?;
    let codec = symbol.call_codec();
    let error = codec.ids().conversion_error;
    if !codec.module().is_builtin_foreign() {
        return Err(RuntimeFailure::ForeignBinding);
    }
    let hidden = ConstructorId::new(error, 0);
    let nominal = registry
        .nominal(error)
        .ok_or(RuntimeFailure::ForeignBinding)?;
    let constructor = registry
        .constructor(hidden)
        .ok_or(RuntimeFailure::ForeignBinding)?;
    if nominal.declaration_kind != ResolvedNominalDeclarationKind::Data
        || nominal.representation.is_some()
        || nominal.representation_provenance.is_some()
        || nominal.constructors.as_ref() != [hidden]
        || registry
            .nominal_parameters(error)
            .is_none_or(|parameters| !parameters.is_empty())
        || constructor.owner != error
        || constructor.payload.is_some()
        || !within(codec.source(), &nominal.origin, work)?
        || !within(codec.source(), &constructor.origin, work)?
    {
        return Err(RuntimeFailure::ForeignBinding);
    }
    Ok(hidden)
}

fn within(
    source: Span,
    mut origin: &Origin,
    work: &mut TypeWorkBudget,
) -> Result<bool, RuntimeFailure> {
    loop {
        paid(work, 1)?;
        match origin {
            Origin::Source(span) => {
                return Ok(source.source() == span.source()
                    && source.range().start() <= span.range().start()
                    && span.range().end() <= source.range().end());
            }
            Origin::Generated { cause, .. } => origin = cause,
            Origin::Related { primary, .. } => origin = primary,
        }
    }
}

fn paid(work: &mut TypeWorkBudget, units: usize) -> Result<(), RuntimeFailure> {
    work.charge(units).map_err(|()| {
        RuntimeFailure::resource(ResourceFailure::new(
            ResourceFailureCause::WorkBudgetExhausted,
            RuntimePhase::Access,
            RuntimeResource::WorkUnits,
            Some(units),
            Some(work.remaining()),
        ))
    })
}
fn storage(units: usize) -> RuntimeFailure {
    RuntimeFailure::resource(ResourceFailure::new(
        ResourceFailureCause::StorageReservationFailed,
        RuntimePhase::Access,
        RuntimeResource::ForeignCodecStorage,
        Some(units),
        None,
    ))
}
