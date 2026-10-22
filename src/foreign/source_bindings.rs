//! Source-native executable bindings and the pre-execution admission receipt.
//! Only a sealed, independently checked executable member can enter this table.

use std::{collections::HashMap, rc::Rc, sync::Arc};

use crate::{
    core::{EffectExprKind, EffectOperation, ValidatedEffectProgram},
    eval::{ResourceFailure, ResourceFailureCause, RuntimeFailure, RuntimePhase, RuntimeResource},
    foreign::{
        checked_source::{CheckedExecutableForeignSymbol, CheckedForeignSymbol},
        source_runtime::{
            NativeOwnerAcquireCallback, NativeOwnerCallReturned, NativeOwnerDisposition,
            NativeOwnerGuard, NativeOwnerGuardReady, NativeOwnerOperand,
            NativeOwnerTeardownCallback, NativeScalarCallError, NativeScalarReply,
            NativeScalarValue,
        },
    },
    module::ModuleId,
    resolved::{ResolvedNominalDeclarationKind, ResolvedRegistry},
    source::{Origin, Span},
    types::{ConstructorId, EffectInstance, Kind, KindedArgument, TypeWorkBudget},
};

pub(crate) type NativeScalarCallback =
    fn(&[NativeScalarValue]) -> Result<NativeScalarReply, NativeScalarCallError>;

pub(crate) fn owner_admission_failure(
    error: super::source_runtime::NativeOwnerAdmissionError,
    work: &TypeWorkBudget,
) -> RuntimeFailure {
    match error {
        super::source_runtime::NativeOwnerAdmissionError::Authority => {
            RuntimeFailure::ForeignBinding
        }
        super::source_runtime::NativeOwnerAdmissionError::Work => effect_work_refusal(work),
        super::source_runtime::NativeOwnerAdmissionError::Storage(count) => storage(count),
    }
}

#[derive(Debug)]
pub(crate) struct SourceScalarBinding {
    symbol: Arc<CheckedForeignSymbol>,
    target: &'static str,
    callback: NativeScalarCallback,
}

/// Generated callbacks remain separate from scalar transport and supply no
/// lifecycle authority until a controlled source-scope receipt admits a request.
#[derive(Debug)]
pub(crate) enum SourceOwnerCallback {
    View(super::source_runtime::NativeViewCallback),
    Borrow(fn(&[NativeOwnerOperand]) -> Result<NativeScalarReply, NativeScalarCallError>),
    Acquire(NativeOwnerAcquireCallback),
    ByteAcquire(
        NativeOwnerAcquireCallback,
        super::source_runtime::NativeByteCallbacks,
    ),
    Teardown(NativeOwnerTeardownCallback),
    StatusTeardown(super::source_runtime::NativeOwnerStatusTeardownCallback),
}

impl SourceOwnerCallback {
    fn teardown_plan(
        &self,
        symbol: &Arc<CheckedForeignSymbol>,
        work: &mut TypeWorkBudget,
    ) -> Result<super::source_runtime::NativeOwnerDestruction, RuntimeFailure> {
        use super::{source_contract::PreparedOwnerCall, source_runtime::NativeOwnerDestruction};
        match (self, symbol.owner_role()) {
            (Self::Teardown(callback), Some(PreparedOwnerCall::Teardown { consumes, .. })) => {
                Ok(NativeOwnerDestruction::Void {
                    callback: *callback,
                    consumes: *consumes,
                })
            }
            (
                Self::StatusTeardown(callback),
                Some(PreparedOwnerCall::StatusTeardown { outcomes, .. }),
            ) => {
                paid(work, 1)?;
                for outcome in outcomes {
                    paid(work, outcome.predicates.len().saturating_add(1))?;
                }
                Ok(NativeOwnerDestruction::Status {
                    callback: *callback,
                    symbol: Arc::clone(symbol),
                })
            }
            _ => Err(RuntimeFailure::ForeignBinding),
        }
    }
}

#[derive(Debug)]
struct SourceOwnerBinding {
    symbol: Arc<CheckedForeignSymbol>,
    target: &'static str,
    callback: SourceOwnerCallback,
}

/// Opaque supplied bindings. Empty construction grants no executable authority.
#[derive(Debug, Default)]
pub struct SourceNativeBindings {
    entries: HashMap<crate::types::OperationId, SourceScalarBinding>,
    owners: HashMap<crate::types::OperationId, SourceOwnerBinding>,
    owner_storage: Rc<super::source_runtime::NativeOwnerStorage>,
}

impl SourceNativeBindings {
    pub(crate) fn declared_owner_dependency(
        &self,
        activation: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<super::source_runtime::NativeOwnerDependency, RuntimeFailure> {
        self.owner_storage
            .declared_dependency(activation, work)
            .map_err(|error| owner_admission_failure(error, work))
    }

    pub(crate) fn borrowed_owner(
        &self,
        activation: usize,
        ty: &crate::types::Type,
        kind: super::source_runtime::NativeOwnerViewKind,
        completion: Option<&NativeOwnerGuard>,
        work: &mut TypeWorkBudget,
    ) -> Result<super::source_runtime::NativeOwnerDependency, RuntimeFailure> {
        self.owner_storage
            .view(activation, ty, kind, completion, work)
            .map_err(|error| owner_admission_failure(error, work))
    }
    pub(crate) fn close_source_owners(&self) -> Result<(), RuntimeFailure> {
        self.owner_storage
            .close()
            .then_some(())
            .ok_or(RuntimeFailure::ResourceCompletion)
    }

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
        if symbol.owner().is_some()
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
                (operand.source(), operand.representation()),
                (
                    super::source_contract::PreparedOperandSource::Source(_)
                        | super::source_contract::PreparedOperandSource::Constant(_),
                    super::source_contract::PreparedRepresentation::Scalar(_)
                ) | (
                    super::source_contract::PreparedOperandSource::Sentinel(_),
                    super::source_contract::PreparedRepresentation::FunctionAddressSentinel
                )
            )
        }) {
            return Err(RuntimeFailure::ForeignBinding);
        }
        if self.entries.contains_key(&symbol.operation())
            || self.owners.contains_key(&symbol.operation())
        {
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

    /// Consumes independently sealed generated authority, but grants no ability
    /// to invoke an owner operation outside its controlled resource scope.
    pub(crate) fn insert_owner_checked(
        &mut self,
        sealed: CheckedExecutableForeignSymbol,
        callback: SourceOwnerCallback,
        work: &mut TypeWorkBudget,
    ) -> Result<(), RuntimeFailure> {
        use super::source_contract::{
            PreparedAbiResult, PreparedAddressRepresentation, PreparedOperandSource,
            PreparedOwnerCall, PreparedRepresentation,
        };
        paid(work, 3)?;
        let target = sealed.target();
        let symbol = sealed.into_source();
        let owner = symbol.owner().ok_or(RuntimeFailure::ForeignBinding)?;
        if target != "x86_64-unknown-linux-gnu" || symbol.owner_codec().is_none() {
            return Err(RuntimeFailure::ForeignBinding);
        }
        paid(work, symbol.symbol().operands().len())?;
        let admitted = match (&callback, symbol.owner_role()) {
            (
                SourceOwnerCallback::Borrow(_),
                Some(PreparedOwnerCall::Borrow {
                    current_operand, ..
                }),
            ) => {
                !matches!(
                    symbol.symbol().access_result(),
                    Some(super::source_contract::PreparedAccessResult::View { .. })
                ) && matches!(symbol.symbol().result(), PreparedAbiResult::Scalar(_))
                    && symbol
                        .symbol()
                        .operands()
                        .iter()
                        .enumerate()
                        .all(|(index, operand)| {
                            match (operand.source(), operand.representation()) {
                                (
                                    PreparedOperandSource::Current(_),
                                    PreparedRepresentation::Address(representation),
                                ) => {
                                    index == *current_operand
                                        && representation == owner.owner().representation()
                                }
                                (
                                    PreparedOperandSource::Bytes { .. },
                                    PreparedRepresentation::Address(
                                        PreparedAddressRepresentation::Bytes,
                                    ),
                                )
                                | (
                                    PreparedOperandSource::Sentinel(_),
                                    PreparedRepresentation::FunctionAddressSentinel,
                                ) => index != *current_operand,
                                (
                                    PreparedOperandSource::Enclosing(_),
                                    PreparedRepresentation::Address(_),
                                )
                                | (
                                    PreparedOperandSource::Source(_)
                                    | PreparedOperandSource::Constant(_),
                                    PreparedRepresentation::Scalar(_),
                                ) => index != *current_operand,
                                _ => false,
                            }
                        })
            }
            (
                SourceOwnerCallback::View(_),
                Some(PreparedOwnerCall::Borrow {
                    current_operand, ..
                }),
            ) => {
                matches!(
                    symbol.symbol().access_result(),
                    Some(super::source_contract::PreparedAccessResult::View { .. })
                ) && symbol.symbol().result()
                    == PreparedAbiResult::Address(PreparedAddressRepresentation::Bytes)
                    && symbol
                        .symbol()
                        .operands()
                        .iter()
                        .enumerate()
                        .all(|(index, operand)| {
                            match (operand.source(), operand.representation()) {
                                (
                                    PreparedOperandSource::Current(_),
                                    PreparedRepresentation::Address(representation),
                                ) => {
                                    index == *current_operand
                                        && representation == owner.owner().representation()
                                }
                                (
                                    PreparedOperandSource::Enclosing(_),
                                    PreparedRepresentation::Address(_),
                                )
                                | (
                                    PreparedOperandSource::Source(_)
                                    | PreparedOperandSource::Constant(_),
                                    PreparedRepresentation::Scalar(_),
                                ) => index != *current_operand,
                                _ => false,
                            }
                        })
            }
            (
                SourceOwnerCallback::Acquire(_),
                Some(PreparedOwnerCall::OutputAcquire {
                    output_operand,
                    offset,
                    ..
                }),
            ) => {
                owner.owner().representation() == PreparedAddressRepresentation::Opaque
                    && matches!(symbol.symbol().result(), PreparedAbiResult::Scalar(_))
                    && symbol
                        .symbol()
                        .operands()
                        .iter()
                        .enumerate()
                        .all(|(index, operand)| {
                            match (operand.source(), operand.representation()) {
                                (
                                    PreparedOperandSource::OwnerOutput,
                                    PreparedRepresentation::Address(
                                        PreparedAddressRepresentation::Opaque,
                                    ),
                                ) => index == *output_operand,
                                (
                                    PreparedOperandSource::OffsetOutput,
                                    PreparedRepresentation::Address(
                                        PreparedAddressRepresentation::Bytes,
                                    ),
                                ) => {
                                    offset.is_some_and(|offset| offset.operand == index)
                                        && index != *output_operand
                                }
                                (
                                    PreparedOperandSource::Enclosing(_),
                                    PreparedRepresentation::Address(_),
                                ) => index != *output_operand,
                                (
                                    PreparedOperandSource::Nul(_),
                                    PreparedRepresentation::Address(
                                        PreparedAddressRepresentation::Bytes,
                                    ),
                                )
                                | (
                                    PreparedOperandSource::Null,
                                    PreparedRepresentation::Address(_),
                                ) => index != *output_operand,
                                (
                                    PreparedOperandSource::Source(_)
                                    | PreparedOperandSource::Constant(_),
                                    PreparedRepresentation::Scalar(_),
                                ) => index != *output_operand,
                                _ => false,
                            }
                        })
            }
            (
                SourceOwnerCallback::Acquire(_),
                Some(PreparedOwnerCall::Acquire {
                    initialized_bytes, ..
                }),
            ) => {
                matches!(
                    (owner.owner().representation(), initialized_bytes),
                    (PreparedAddressRepresentation::Opaque, None)
                ) && symbol.symbol().result()
                    == PreparedAbiResult::Address(owner.owner().representation())
                    && symbol.symbol().operands().iter().all(|operand| {
                        matches!(
                            (operand.source(), operand.representation()),
                            (
                                PreparedOperandSource::Source(_)
                                    | PreparedOperandSource::Constant(_),
                                PreparedRepresentation::Scalar(_)
                            ) | (
                                PreparedOperandSource::Sentinel(_),
                                PreparedRepresentation::FunctionAddressSentinel
                            ) | (
                                PreparedOperandSource::Enclosing(_),
                                PreparedRepresentation::Address(_)
                            )
                        )
                    })
            }
            (
                SourceOwnerCallback::ByteAcquire(_, _),
                Some(PreparedOwnerCall::Acquire {
                    initialized_bytes: Some(_),
                    ..
                }),
            ) => {
                owner.owner().representation() == PreparedAddressRepresentation::Bytes
                    && symbol.symbol().result()
                        == PreparedAbiResult::Address(PreparedAddressRepresentation::Bytes)
                    && symbol.symbol().operands().iter().all(|operand| {
                        matches!(
                            (operand.source(), operand.representation()),
                            (
                                PreparedOperandSource::Source(_)
                                    | PreparedOperandSource::Constant(_),
                                PreparedRepresentation::Scalar(_)
                            ) | (
                                PreparedOperandSource::Sentinel(_),
                                PreparedRepresentation::FunctionAddressSentinel
                            ) | (
                                PreparedOperandSource::Enclosing(_),
                                PreparedRepresentation::Address(_)
                            )
                        )
                    })
            }
            (
                SourceOwnerCallback::Teardown(_) | SourceOwnerCallback::StatusTeardown(_),
                Some(
                    PreparedOwnerCall::Teardown {
                        current_operand, ..
                    }
                    | PreparedOwnerCall::StatusTeardown {
                        current_operand, ..
                    },
                ),
            ) => {
                matches!(
                    (&callback, symbol.owner_role(), symbol.symbol().result()),
                    (
                        SourceOwnerCallback::Teardown(_),
                        Some(PreparedOwnerCall::Teardown { .. }),
                        PreparedAbiResult::Void
                    ) | (
                        SourceOwnerCallback::StatusTeardown(_),
                        Some(PreparedOwnerCall::StatusTeardown { .. }),
                        PreparedAbiResult::Scalar(_)
                    )
                ) && symbol
                    .symbol()
                    .operands()
                    .get(*current_operand)
                    .is_some_and(|operand| {
                        matches!(operand.source(), PreparedOperandSource::Current(_))
                            && operand.representation()
                                == PreparedRepresentation::Address(owner.owner().representation())
                    })
                    && symbol
                        .symbol()
                        .operands()
                        .iter()
                        .enumerate()
                        .all(|(index, operand)| {
                            index == *current_operand
                                || matches!(
                                    (operand.source(), operand.representation()),
                                    (
                                        PreparedOperandSource::Enclosing(_),
                                        PreparedRepresentation::Address(_)
                                    ) | (
                                        PreparedOperandSource::Source(_)
                                            | PreparedOperandSource::Constant(_),
                                        PreparedRepresentation::Scalar(_)
                                    ) | (
                                        PreparedOperandSource::Sentinel(_),
                                        PreparedRepresentation::FunctionAddressSentinel
                                    )
                                )
                        })
            }
            _ => false,
        };
        if !admitted
            || self.entries.contains_key(&symbol.operation())
            || self.owners.contains_key(&symbol.operation())
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        self.owners.try_reserve(1).map_err(|_| storage(1))?;
        self.owners.insert(
            symbol.operation(),
            SourceOwnerBinding {
                symbol,
                target,
                callback,
            },
        );
        Ok(())
    }

    /// Passive exact-membership check used by pre-execution scope admission.
    /// It returns no callback or per-request lifecycle permission.
    pub(crate) fn authenticate_owner_binding(
        &self,
        symbol: &Arc<CheckedForeignSymbol>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), RuntimeFailure> {
        paid(work, 2)?;
        let binding = self
            .owners
            .get(&symbol.operation())
            .ok_or(RuntimeFailure::ForeignBinding)?;
        if binding.target != "x86_64-unknown-linux-gnu" || !Arc::ptr_eq(&binding.symbol, symbol) {
            return Err(RuntimeFailure::ForeignBinding);
        }
        Ok(())
    }

    /// Admits one request from a final checked scope's actual lifecycle copy.
    /// Header facts or an ordinary interpreter alone cannot create this receipt.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn admit_source_owner_invocation<'bindings>(
        &'bindings self,
        program: &crate::eval::ExecutableProgram,
        scope_node: crate::core::NodeId,
        request: crate::core::NodeId,
        phase: SourceOwnerPhase,
        instance: &EffectInstance,
        symbol: &Arc<CheckedForeignSymbol>,
        work: &mut TypeWorkBudget,
    ) -> Result<AdmittedSourceOwnerInvocation<'bindings>, RuntimeFailure> {
        let receipt = SourceOwnerScopeRequest::admit(
            program, scope_node, request, phase, instance, symbol, work,
        )?;
        let header = receipt._scope.header();
        self.authenticate_owner_binding(symbol, work)?;
        self.authenticate_owner_binding(&header.teardown, work)?;
        let binding = self
            .owners
            .get(&symbol.operation())
            .ok_or(RuntimeFailure::ForeignBinding)?;
        // Destruction is the owner's original declared member, independently
        // of the source finish member selected by this resource header.
        paid(work, self.owners.len())?;
        let teardown = self
            .owners
            .values()
            .find(|binding| {
                binding
                    .symbol
                    .owner()
                    .is_some_and(|owner| Arc::ptr_eq(owner, &header.owner))
                    && binding.symbol.symbol().member_index()
                        == header.owner.owner().teardown_member()
            })
            .ok_or(RuntimeFailure::ForeignBinding)?;
        match (phase, &binding.callback, &teardown.callback) {
            (SourceOwnerPhase::Borrow(_), SourceOwnerCallback::Borrow(_), _) => {
                let hidden_error = authenticate_hidden_error(program.registry(), symbol, work)?;
                Ok(AdmittedSourceOwnerInvocation::Borrow(
                    AdmittedSourceOwnerBorrowInvocation {
                        checked: None,
                        binding,
                        receipt,
                        hidden_error,
                    },
                ))
            }
            (
                SourceOwnerPhase::Acquire,
                SourceOwnerCallback::Acquire(_) | SourceOwnerCallback::ByteAcquire(_, _),
                SourceOwnerCallback::Teardown(_) | SourceOwnerCallback::StatusTeardown(_),
            ) => {
                let hidden_error = authenticate_hidden_error(program.registry(), symbol, work)?;
                paid(work, 1)?;
                let current_operand = teardown
                    .symbol
                    .owner_role()
                    .and_then(|role| role.current_operand())
                    .ok_or(RuntimeFailure::ForeignBinding)?;
                let plan = teardown.callback.teardown_plan(&teardown.symbol, work)?;
                paid(work, teardown.symbol.symbol().operands().len())?;
                let mut readiness = NativeOwnerGuardReady::in_storage_plan(
                    Arc::clone(&header.owner),
                    plan,
                    teardown.symbol.symbol().operands().len(),
                    current_operand,
                    Rc::clone(&self.owner_storage),
                )
                .map_err(|()| storage(1))?;
                if let SourceOwnerCallback::ByteAcquire(_, bytes) = &binding.callback {
                    readiness.prepare_byte_callbacks(*bytes);
                }
                Ok(AdmittedSourceOwnerInvocation::Acquire(
                    AdmittedSourceOwnerAcquireInvocation {
                        binding,
                        readiness,
                        receipt,
                        hidden_error,
                        destructor: &teardown.symbol,
                    },
                ))
            }
            (
                SourceOwnerPhase::Finish,
                SourceOwnerCallback::Teardown(_) | SourceOwnerCallback::StatusTeardown(_),
                SourceOwnerCallback::Teardown(_) | SourceOwnerCallback::StatusTeardown(_),
            ) => {
                let hidden_error = authenticate_hidden_error(program.registry(), symbol, work)?;
                Ok(AdmittedSourceOwnerInvocation::Teardown(
                    AdmittedSourceOwnerTeardownInvocation {
                        symbol: &binding.symbol,
                        plan: binding.callback.teardown_plan(&binding.symbol, work)?,
                        receipt,
                        hidden_error,
                    },
                ))
            }
            _ => Err(RuntimeFailure::ForeignBinding),
        }
    }

    /// A window request must originate in the exact checked lifecycle copy,
    /// match its original declared family and complete runtime interpretation,
    /// and use the separately supplied typed binding. None of those facts alone
    /// provides a live owner, pointer or read permission.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn admit_source_window_invocation<'bindings>(
        &'bindings self,
        program: &crate::eval::ExecutableProgram,
        scope_node: crate::core::NodeId,
        window_node: crate::core::NodeId,
        request: crate::core::NodeId,
        phase: crate::core::source_resource::SourceResourcePhase,
        arguments: &[KindedArgument],
        instance: &EffectInstance,
        symbol: &Arc<CheckedForeignSymbol>,
        work: &mut TypeWorkBudget,
    ) -> Result<AdmittedSourceWindowInvocation<'bindings>, RuntimeFailure> {
        let receipt = SourceOwnerScopeRequest::admit_window(
            program,
            scope_node,
            window_node,
            request,
            phase,
            arguments,
            instance,
            symbol,
            work,
        )?;
        let crate::eval::ExecutableProgram::Effect(program) = program else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        self.authenticate_owner_binding(symbol, work)?;
        let binding = self
            .owners
            .get(&symbol.operation())
            .ok_or(RuntimeFailure::ForeignBinding)?;
        if !matches!(
            (&binding.callback, symbol.owner_role()),
            (
                SourceOwnerCallback::View(_) | SourceOwnerCallback::Borrow(_),
                Some(super::source_contract::PreparedOwnerCall::Borrow { .. })
            )
        ) {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let hidden_error = authenticate_hidden_error(program.registry(), symbol, work)?;
        Ok(AdmittedSourceWindowInvocation {
            checked: None,
            binding,
            hidden_error,
            receipt,
        })
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

fn core_admission_failure(
    error: crate::core::ValidationError,
    work: &TypeWorkBudget,
) -> RuntimeFailure {
    if error.reason() == crate::core::ValidationReason::Resource {
        effect_work_refusal(work)
    } else {
        RuntimeFailure::ForeignBinding
    }
}

fn effect_work_refusal(work: &TypeWorkBudget) -> RuntimeFailure {
    RuntimeFailure::resource(ResourceFailure::new(
        ResourceFailureCause::WorkBudgetExhausted,
        RuntimePhase::Access,
        RuntimeResource::WorkUnits,
        None,
        Some(work.remaining()),
    ))
}

fn admit_complete_native_instance(
    symbol: &CheckedForeignSymbol,
    instance: &EffectInstance,
    work: &mut TypeWorkBudget,
) -> Result<(), RuntimeFailure> {
    let parameters = symbol.symbol().parameters();
    paid(work, parameters.len())?;
    if instance.effect() != symbol.effect()
        || instance.arguments().len() != parameters.len()
        || symbol.parameter_ids().len() != parameters.len()
    {
        return Err(RuntimeFailure::ForeignBinding);
    }
    let projection = symbol.symbol().native_type_projection();
    let mut native = 0;
    for (index, (parameter, actual)) in parameters.iter().zip(instance.arguments()).enumerate() {
        if !matches!(
            (parameter.kind(), actual),
            (Kind::Type, KindedArgument::TypeArg(_)) | (Kind::EffectRow, KindedArgument::RowArg(_))
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
    Ok(())
}

/// Current checked scope lifecycle phase; ordinary interpreter requests cannot
/// construct an invocation using this stage alone.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SourceOwnerPhase {
    Acquire,
    Finish,
    Borrow(crate::core::source_resource::SourceResourcePhase),
}

/// Per-request scope authority retains the final checked template and full
/// runtime instance. Only exact final-program scope/request admission creates it.
#[derive(Debug)]
pub(super) struct SourceOwnerScopeRequest {
    pub(super) _scope: Arc<crate::core::source_resource::CheckedSourceResourceTemplate>,
    pub(super) _scope_node: crate::core::NodeId,
    pub(super) _window: Option<crate::core::NodeId>,
    pub(super) _request: crate::core::NodeId,
    pub(super) _phase: SourceOwnerPhase,
    _instance: EffectInstance,
}

impl SourceOwnerScopeRequest {
    #[allow(clippy::too_many_arguments)]
    fn admit_window(
        program: &crate::eval::ExecutableProgram,
        scope_node: crate::core::NodeId,
        window_node: crate::core::NodeId,
        request: crate::core::NodeId,
        phase: crate::core::source_resource::SourceResourcePhase,
        arguments: &[KindedArgument],
        instance: &EffectInstance,
        symbol: &Arc<CheckedForeignSymbol>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        paid(work, 6)?;
        let crate::eval::ExecutableProgram::Effect(program) = program else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let scope = match program.node(scope_node).map(|node| &node.kind) {
            Some(EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope))) => scope,
            _ => return Err(RuntimeFailure::ForeignBinding),
        };
        let window = match program.node(window_node).map(|node| &node.kind) {
            Some(EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window))) => window,
            _ => return Err(RuntimeFailure::ForeignBinding),
        };
        if !scope
            .contains_phase_window(phase, window_node, work)
            .map_err(|error| core_admission_failure(error, work))?
            || !scope
                .contains_window_request(phase, window_node, request, symbol, work)
                .map_err(|error| core_admission_failure(error, work))?
            || !program
                .registry()
                .native_symbol(symbol.operation())
                .is_some_and(|canonical| Arc::ptr_eq(canonical, symbol))
            || !program
                .registry()
                .effect(symbol.effect())
                .and_then(|effect| effect.native_contract.as_ref())
                .is_some_and(|canonical| Arc::ptr_eq(canonical, symbol))
            || !super::source_access::window_operation_matches(
                window.family(),
                arguments,
                symbol,
                instance,
                program.registry(),
                work,
            )
            .map_err(|error| {
                if error.is_resource_exhaustion() {
                    effect_work_refusal(work)
                } else {
                    RuntimeFailure::ForeignBinding
                }
            })?
        {
            return Err(RuntimeFailure::ForeignBinding);
        }

        admit_complete_native_instance(symbol, instance, work)?;
        let instance = crate::types::clone_effect_instance_with_budget(instance, work)
            .map_err(|()| effect_work_refusal(work))?;
        paid(work, 1)?;
        Ok(Self {
            _scope: Arc::clone(scope.original()),
            _scope_node: scope_node,
            _window: Some(window_node),
            _request: request,
            _phase: SourceOwnerPhase::Borrow(phase),
            _instance: instance,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn admit(
        program: &crate::eval::ExecutableProgram,
        scope_node: crate::core::NodeId,
        request: crate::core::NodeId,
        phase: SourceOwnerPhase,
        instance: &EffectInstance,
        symbol: &Arc<CheckedForeignSymbol>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        paid(work, 6)?;
        // Access-result members require the distinct exact-window invocation
        // receipt, never an ordinary owner phase or compatible scalar callback.
        if symbol.symbol().access_result().is_some() {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let crate::eval::ExecutableProgram::Effect(program) = program else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let Some(scope_node_value) = program.node(scope_node) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
            &scope_node_value.kind
        else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        if !scope
            .contains_phase_request(
                program,
                request,
                match phase {
                    SourceOwnerPhase::Acquire => {
                        crate::core::source_resource::SourceResourcePhase::Acquire
                    }
                    SourceOwnerPhase::Finish => {
                        crate::core::source_resource::SourceResourcePhase::Finish
                    }
                    SourceOwnerPhase::Borrow(phase) => phase,
                },
                work,
            )
            .map_err(|error| {
                if error.reason() == crate::core::ValidationReason::Resource {
                    effect_work_refusal(work)
                } else {
                    RuntimeFailure::ForeignBinding
                }
            })?
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let header = scope.header();
        let expected = match phase {
            SourceOwnerPhase::Acquire => &header.acquire,
            SourceOwnerPhase::Finish => &header.teardown,
            SourceOwnerPhase::Borrow(_) => {
                if !matches!(
                    symbol.owner_role(),
                    Some(super::source_contract::PreparedOwnerCall::Borrow { .. })
                ) || !symbol
                    .owner()
                    .is_some_and(|owner| Arc::ptr_eq(owner, &header.owner))
                {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                symbol
            }
        };
        if !Arc::ptr_eq(symbol, expected)
            || !program
                .registry()
                .native_symbol(symbol.operation())
                .is_some_and(|canonical| Arc::ptr_eq(canonical, symbol))
            || !program
                .registry()
                .effect(symbol.effect())
                .and_then(|effect| effect.native_contract.as_ref())
                .is_some_and(|canonical| Arc::ptr_eq(canonical, symbol))
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        admit_complete_native_instance(symbol, instance, work)?;
        let instance = crate::types::clone_effect_instance_with_budget(instance, work)
            .map_err(|()| effect_work_refusal(work))?;
        paid(work, 1)?;
        Ok(SourceOwnerScopeRequest {
            _scope: Arc::clone(scope.original()),
            _scope_node: scope_node,
            _window: None,
            _request: request,
            _phase: phase,
            _instance: instance,
        })
    }
}

#[derive(Debug)]
pub(crate) enum AdmittedSourceOwnerInvocation<'bindings> {
    Borrow(AdmittedSourceOwnerBorrowInvocation<'bindings>),
    Acquire(AdmittedSourceOwnerAcquireInvocation<'bindings>),
    Teardown(AdmittedSourceOwnerTeardownInvocation<'bindings>),
}

#[derive(Debug)]
pub(crate) struct AdmittedSourceOwnerBorrowInvocation<'bindings> {
    checked: Option<super::source_runtime::NativeOwnerBorrowRecord>,
    binding: &'bindings SourceOwnerBinding,
    receipt: SourceOwnerScopeRequest,
    hidden_error: ConstructorId,
}
impl<'bindings> AdmittedSourceOwnerBorrowInvocation<'bindings> {
    pub(crate) fn prepare_checked_boundary(
        mut self,
        guard: &NativeOwnerGuard,
        activation: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        self.checked = guard
            .prepare_checked_borrow(&self.receipt, &self.binding.symbol, activation, work)
            .map_err(|error| owner_admission_failure(error, work))?;
        Ok(self)
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
        operands: &[NativeOwnerOperand],
    ) -> Result<(SourceOwnerReturnedAuthority<'bindings>, NativeScalarReply), NativeScalarCallError>
    {
        let SourceOwnerCallback::Borrow(callback) = &self.binding.callback else {
            return Err(NativeScalarCallError::ArgumentContract);
        };
        if let Some(checked) = &self.checked {
            checked
                .begin()
                .map_err(|_| NativeScalarCallError::ArgumentContract)?;
        }
        let raw = match callback(operands) {
            Ok(raw) => raw,
            Err(error) => {
                if let Some(checked) = &self.checked {
                    checked.output_failed();
                }
                return Err(error);
            }
        };
        let checked = self.checked.map(|record| record.returned());
        Ok((
            SourceOwnerReturnedAuthority {
                checked,
                _symbol: &self.binding.symbol,
                _receipt: self.receipt,
            },
            raw,
        ))
    }
}

/// Single-use, exact-window native transport. The runtime must separately
/// preadmit the guard, source operands and complete result storage before invoke.
#[derive(Debug)]
pub(crate) struct AdmittedSourceWindowInvocation<'bindings> {
    checked: Option<super::source_runtime::NativeOwnerBorrowRecord>,
    binding: &'bindings SourceOwnerBinding,
    hidden_error: ConstructorId,
    receipt: SourceOwnerScopeRequest,
}
#[derive(Debug)]
pub(crate) enum SourceWindowRaw {
    View(super::source_runtime::NativeViewReturned),
    Scalar(NativeScalarReply),
}
impl<'bindings> AdmittedSourceWindowInvocation<'bindings> {
    pub(crate) fn prepare_checked_boundary(
        mut self,
        guard: &NativeOwnerGuard,
        activation: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        self.checked = guard
            .prepare_checked_borrow(&self.receipt, &self.binding.symbol, activation, work)
            .map_err(|error| owner_admission_failure(error, work))?;
        Ok(self)
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
        operands: &[NativeOwnerOperand],
    ) -> Result<(SourceOwnerReturnedAuthority<'bindings>, SourceWindowRaw), NativeScalarCallError>
    {
        if let Some(checked) = &self.checked {
            checked
                .begin()
                .map_err(|_| NativeScalarCallError::ArgumentContract)?;
        }
        let result = match &self.binding.callback {
            SourceOwnerCallback::View(callback) => callback(operands).map(SourceWindowRaw::View),
            SourceOwnerCallback::Borrow(callback) => {
                callback(operands).map(SourceWindowRaw::Scalar)
            }
            _ => Err(NativeScalarCallError::ArgumentContract),
        };
        let raw = match result {
            Ok(raw) => raw,
            Err(error) => {
                if let Some(checked) = &self.checked {
                    checked.output_failed();
                }
                return Err(error);
            }
        };
        let checked = self.checked.map(|record| record.returned());
        Ok((
            SourceOwnerReturnedAuthority {
                checked,
                _symbol: &self.binding.symbol,
                _receipt: self.receipt,
            },
            raw,
        ))
    }
}

#[derive(Debug)]
pub(crate) struct AdmittedSourceOwnerAcquireInvocation<'bindings> {
    binding: &'bindings SourceOwnerBinding,
    readiness: NativeOwnerGuardReady,
    receipt: SourceOwnerScopeRequest,
    hidden_error: ConstructorId,
    destructor: &'bindings Arc<CheckedForeignSymbol>,
}

#[derive(Debug)]
pub(crate) struct AdmittedSourceOwnerTeardownInvocation<'bindings> {
    symbol: &'bindings Arc<CheckedForeignSymbol>,
    plan: super::source_runtime::NativeOwnerDestruction,
    receipt: SourceOwnerScopeRequest,
    hidden_error: ConstructorId,
}

/// Ownership returned from native code has no acquisition or teardown callback
/// capability. The complete request and original symbol remain retained.
#[derive(Debug)]
pub(crate) struct SourceOwnerReturnedAuthority<'bindings> {
    checked: Option<super::source_runtime::NativeOwnerBoundary>,
    _symbol: &'bindings Arc<CheckedForeignSymbol>,
    _receipt: SourceOwnerScopeRequest,
}

impl SourceOwnerReturnedAuthority<'_> {
    pub(crate) fn output_failed(&self) {
        if let Some(checked) = &self.checked {
            checked.output_failed();
        }
    }
}

impl<'bindings> AdmittedSourceOwnerAcquireInvocation<'bindings> {
    pub(crate) fn checked_boundary(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<super::source_runtime::NativeOwnerBoundary>, RuntimeFailure> {
        self.readiness
            .checked_boundary(work)
            .map_err(|error| owner_admission_failure(error, work))
    }

    pub(crate) fn destructor(&self) -> &Arc<CheckedForeignSymbol> {
        self.destructor
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn prepare_owner_authority(
        mut self,
        activation: usize,
        limits: Option<super::source_runtime::CheckedOwnerLimits>,
        state: crate::types::IterativeTypeOwner,
        access: crate::types::IterativeTypeOwner,
        dependencies: Vec<super::source_runtime::NativeOwnerDependency>,
        operands: Vec<NativeOwnerOperand>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        self.readiness
            .prepare_authority(activation, state, access, dependencies, operands, work)
            .map_err(|error| owner_admission_failure(error, work))?;
        self.readiness
            .prepare_checked_boundary(&self.receipt, activation, limits, work)
            .map_err(|error| owner_admission_failure(error, work))?;
        Ok(self)
    }
    /// Accepts only the extent shape required by this exact acquisition contract.
    /// The evaluator projects and narrows its original source leaf beforehand.
    pub(crate) fn prepare_initialized_bytes(
        mut self,
        extent: Option<usize>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, RuntimeFailure> {
        let initialized_bytes = match self.binding.symbol.owner_role() {
            Some(super::source_contract::PreparedOwnerCall::Acquire {
                initialized_bytes, ..
            }) => initialized_bytes.as_ref(),
            Some(super::source_contract::PreparedOwnerCall::OutputAcquire { .. }) => None,
            _ => return Err(RuntimeFailure::ForeignBinding),
        };
        if extent.is_some() || initialized_bytes.is_some() {
            paid(work, 1)?;
        }
        if extent.is_some() != initialized_bytes.is_some() {
            return Err(RuntimeFailure::ForeignBinding);
        }
        if let Some(extent) = extent {
            // The exact original initialization fact carries proportional
            // native initialization and fixed release work. Admit both before
            // acquisition; recording the returned owner cannot charge or fail.
            let units = extent.checked_add(2).ok_or_else(|| {
                RuntimeFailure::resource(ResourceFailure::new(
                    ResourceFailureCause::WorkBudgetExhausted,
                    RuntimePhase::Access,
                    RuntimeResource::WorkUnits,
                    None,
                    Some(work.remaining()),
                ))
            })?;
            paid(work, units)?;
        }
        self.readiness.prepare_initialized_bytes(extent);
        Ok(self)
    }

    pub(crate) fn symbol(&self) -> &Arc<CheckedForeignSymbol> {
        &self.binding.symbol
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
    pub(crate) fn nullable_constructors(&self) -> [ConstructorId; 2] {
        *self
            .binding
            .symbol
            .owner_codec()
            .expect("admitted owner codec")
            .nullable_constructors()
    }
    pub(crate) fn readable_constructor(&self) -> ConstructorId {
        self.binding
            .symbol
            .owner_codec()
            .expect("admitted owner codec")
            .output_constructors()[1]
    }
    pub(crate) fn invoke(
        self,
        values: &[NativeOwnerOperand],
    ) -> Result<
        (
            SourceOwnerReturnedAuthority<'bindings>,
            NativeOwnerCallReturned,
        ),
        NativeScalarCallError,
    > {
        let callback = match &self.binding.callback {
            SourceOwnerCallback::Acquire(callback)
            | SourceOwnerCallback::ByteAcquire(callback, _) => callback,
            SourceOwnerCallback::View(_)
            | SourceOwnerCallback::Borrow(_)
            | SourceOwnerCallback::Teardown(_)
            | SourceOwnerCallback::StatusTeardown(_) => {
                return Err(NativeScalarCallError::ArgumentContract);
            }
        };
        let mut readiness = self.readiness;
        readiness
            .begin_checked_acquire()
            .map_err(|_| NativeScalarCallError::ArgumentContract)?;
        let raw = callback(values, readiness)?;
        Ok((
            SourceOwnerReturnedAuthority {
                checked: None,
                _symbol: &self.binding.symbol,
                _receipt: self.receipt,
            },
            raw,
        ))
    }
}

impl<'bindings> AdmittedSourceOwnerTeardownInvocation<'bindings> {
    pub(crate) fn prepare_checked_finish(
        &self,
        guard: &NativeOwnerGuard,
        activation: usize,
        blocked: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<(), RuntimeFailure> {
        guard
            .prepare_checked_finish(&self.receipt, activation, blocked, work)
            .map_err(|error| owner_admission_failure(error, work))
    }

    pub(crate) fn result(&self) -> super::source_contract::PreparedAbiResult {
        self.symbol.symbol().result()
    }
    pub(crate) fn owner(&self) -> &Arc<super::source_owner::CheckedForeignOwner> {
        self.symbol.owner().expect("admitted owner identity")
    }
    pub(crate) fn returned_constructor(&self) -> ConstructorId {
        self.symbol.call_codec().ids().returned
    }
    pub(crate) fn conversion_failed_constructor(&self) -> ConstructorId {
        self.symbol.call_codec().ids().conversion_failed
    }
    pub(crate) fn hidden_error_constructor(&self) -> ConstructorId {
        self.hidden_error
    }
    pub(crate) fn disposition_constructors(&self) -> [ConstructorId; 3] {
        *self
            .symbol
            .owner_codec()
            .expect("admitted owner codec")
            .disposition_constructors()
    }
    pub(crate) fn invoke(
        self,
        guard: NativeOwnerGuard,
        operands: &[NativeOwnerOperand],
        blocked: bool,
    ) -> (
        SourceOwnerReturnedAuthority<'bindings>,
        NativeOwnerDisposition,
        Option<super::source_runtime::NativeOwnerStatus>,
    ) {
        guard
            .begin_checked_finish()
            .expect("admitted checked finish ticket");
        let (consumed, status) = guard.finish_with_plan(&self.plan, operands, blocked);
        (
            SourceOwnerReturnedAuthority {
                checked: None,
                _symbol: self.symbol,
                _receipt: self.receipt,
            },
            consumed,
            status,
        )
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
        if matches!(&node.kind, EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) if boundary.host().is_some())
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        if let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) = &node.kind {
            if !cfg!(all(
                target_arch = "x86_64",
                target_os = "linux",
                target_env = "gnu",
                target_pointer_width = "64"
            )) {
                return Err(RuntimeFailure::ForeignBinding);
            }
            paid(work, scope.native_interpretations().len())?;
            for interpretation in scope.native_interpretations() {
                let symbol = interpretation.symbol();
                bindings.authenticate_owner_binding(symbol, work)?;
                if symbol.owner().is_none()
                    || !program
                        .registry()
                        .native_symbol(symbol.operation())
                        .is_some_and(|canonical| Arc::ptr_eq(canonical, symbol))
                    || !program
                        .registry()
                        .effect(symbol.effect())
                        .and_then(|effect| effect.native_contract.as_ref())
                        .is_some_and(|canonical| Arc::ptr_eq(canonical, symbol))
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
            continue;
        }
        if let EffectExprKind::Operation(EffectOperation::SourceCopyWindow(window)) = &node.kind {
            // Resolve every lexical-window callback before ANY acquisition/body
            // callback. Presence grants no live loan or invocation permission.
            for interpretation in window.interpretations() {
                paid(work, 3)?;
                let symbol = interpretation.symbol();
                bindings.authenticate_owner_binding(symbol, work)?;
                if !super::source_access::window_interpretation_matches(
                    window.family(),
                    window.arguments(),
                    interpretation,
                    program.registry(),
                    work,
                )
                .map_err(|error| {
                    if error.is_resource_exhaustion() {
                        effect_work_refusal(work)
                    } else {
                        RuntimeFailure::ForeignBinding
                    }
                })? || !program
                    .registry()
                    .effect(symbol.effect())
                    .and_then(|effect| effect.native_contract.as_ref())
                    .is_some_and(|canonical| Arc::ptr_eq(canonical, symbol))
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
            continue;
        }
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
            if symbol.owner().is_some() {
                // Ordinary entry interpretation cannot grant owner lifecycle authority.
                return Err(RuntimeFailure::ForeignBinding);
            }
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
            && (boundary.host().is_some() || !boundary.interpretations().is_empty())
        {
            return Err(RuntimeFailure::ForeignBinding);
        }
        if matches!(
            &node.kind,
            EffectExprKind::Operation(
                EffectOperation::SourceResourceScope(_) | EffectOperation::SourceCopyWindow(_)
            )
        ) {
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

#[cfg(test)]
#[path = "source_owner_boundary_tests.rs"]
mod boundary_tests;

#[cfg(test)]
pub(crate) use boundary_tests::with_recorded_boundary_for_test;
