//! Target resolution and typed Rust calls for checked scalar and native owners.
//!
//! Plans retain original source authority. They do not link a library, discharge
//! an effect, convert Ash values or validate an external binary's assumptions.

use std::{
    fmt::{self, Write},
    sync::Arc,
};

use crate::{
    foreign::{
        checked_source::CheckedForeignSymbol,
        source_contract::{
            PreparedAbiResult, PreparedAddressRepresentation, PreparedForeignCall,
            PreparedOperandSource, PreparedOwnerCall, PreparedRepresentation,
            PreparedScalarRepresentation,
        },
    },
    source::{Origin, Span},
    types::{OperationId, TypeWorkBudget},
};

#[cfg(test)]
use crate::{
    foreign::checked_source::{
        ForeignBindingContext, NativeLibraryId, authenticate_foreign_symbol,
    },
    resolved::ResolvedRegistry,
};

const TARGET: &str = "x86_64-unknown-linux-gnu";
const VALUE: &str = "ash::foreign::source_runtime::NativeScalarValue";
const REPLY: &str = "ash::foreign::source_runtime::NativeScalarReply";
const ERROR: &str = "ash::foreign::source_runtime::NativeScalarCallError";
const OWNER_READY: &str = "ash::foreign::source_runtime::NativeOwnerGuardReady";
const OWNER_RETURNED: &str = "ash::foreign::source_runtime::NativeOwnerCallReturned";
const OWNER_OPERAND: &str = "ash::foreign::source_runtime::NativeOwnerOperand";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TargetOperand {
    Scalar(TargetScalar),
    Address,
    FunctionAddressSentinel,
}

impl TargetOperand {
    const fn rust_type(self) -> &'static str {
        match self {
            Self::Scalar(scalar) => scalar.rust_type(),
            Self::Address | Self::FunctionAddressSentinel => "*mut core::ffi::c_void",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ForeignBridgeTarget {
    X86_64LinuxGnu,
}

impl ForeignBridgeTarget {
    #[cfg(test)]
    pub(crate) const fn triple(self) -> &'static str {
        match self {
            Self::X86_64LinuxGnu => TARGET,
        }
    }
}

/// Concrete scalar ABI choices, including the target-resolved size_t role.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TargetScalar {
    I8,
    U8,
    I32,
    U32,
    I64,
    U64,
    USize64,
}

impl TargetScalar {
    const fn rust_type(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::U8 => "u8",
            Self::I32 => "i32",
            Self::U32 => "u32",
            Self::I64 => "i64",
            Self::U64 => "u64",
            Self::USize64 => "usize",
        }
    }

    const fn value_variant(self) -> &'static str {
        match self {
            Self::I8 => "I8",
            Self::U8 => "U8",
            Self::I32 => "I32",
            Self::U32 => "U32",
            Self::I64 => "I64",
            Self::U64 => "U64",
            Self::USize64 => "USize",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TargetResult {
    Void,
    Scalar(TargetScalar),
    OwnerAddress,
}

/// Distinct generated callback roles; pointers never enter scalar transport.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TargetBridgeCall {
    Scalar,
    OwnerAcquire,
    OwnerTeardown,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ForeignBridgeReason {
    UnsupportedTarget,
    UnsupportedProfile,
    UnsupportedRepresentation,
    InvalidAuthority,
    Resource,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ForeignBridgeFailure {
    reason: ForeignBridgeReason,
    span: Span,
}

impl ForeignBridgeFailure {
    #[cfg(test)]
    pub(crate) const fn reason(self) -> ForeignBridgeReason {
        self.reason
    }
    #[cfg(test)]
    pub(crate) const fn span(self) -> Span {
        self.span
    }
}

impl fmt::Display for ForeignBridgeFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self.reason {
            ForeignBridgeReason::UnsupportedTarget => "foreign bridge target is unsupported",
            ForeignBridgeReason::UnsupportedProfile => "foreign bridge profile is unsupported",
            ForeignBridgeReason::UnsupportedRepresentation => {
                "foreign bridge ABI representation is unsupported"
            }
            ForeignBridgeReason::InvalidAuthority => {
                "foreign bridge source authority does not match its registry"
            }
            ForeignBridgeReason::Resource => "foreign bridge work or storage admission refused",
        })
    }
}

fn fail(reason: ForeignBridgeReason, span: Span) -> ForeignBridgeFailure {
    ForeignBridgeFailure { reason, span }
}

fn charge(work: &mut TypeWorkBudget, count: usize, span: Span) -> Result<(), ForeignBridgeFailure> {
    work.charge(count)
        .map_err(|()| fail(ForeignBridgeReason::Resource, span))
}

fn target_scalar(
    representation: PreparedScalarRepresentation,
    span: Span,
) -> Result<TargetScalar, ForeignBridgeFailure> {
    Ok(match representation {
        PreparedScalarRepresentation::Signed(8) => TargetScalar::I8,
        PreparedScalarRepresentation::Unsigned(8) => TargetScalar::U8,
        PreparedScalarRepresentation::Signed(32) => TargetScalar::I32,
        PreparedScalarRepresentation::Unsigned(32) => TargetScalar::U32,
        PreparedScalarRepresentation::Signed(64) => TargetScalar::I64,
        PreparedScalarRepresentation::Unsigned(64) => TargetScalar::U64,
        PreparedScalarRepresentation::SizeT => TargetScalar::USize64,
        _ => return Err(fail(ForeignBridgeReason::UnsupportedRepresentation, span)),
    })
}

/// One completed target phase; its checked descriptor remains the source of
/// native spelling, source leaf mappings, complete binders and assumptions.
pub(crate) struct TargetResolvedForeignBridge {
    symbol: Arc<CheckedForeignSymbol>,
    target: ForeignBridgeTarget,
    operands: Box<[TargetOperand]>,
    result: TargetResult,
    call: TargetBridgeCall,
    rust_function_name: String,
    span: Span,
}

impl fmt::Debug for TargetResolvedForeignBridge {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("TargetResolvedForeignBridge")
            .field("operation", &self.operation())
            .field("target", &self.target)
            .field("operand_count", &self.operands.len())
            .field("result", &self.result)
            .finish_non_exhaustive()
    }
}

impl TargetResolvedForeignBridge {
    pub(crate) const fn call(&self) -> TargetBridgeCall {
        self.call
    }
    pub(crate) fn byte_owner(&self) -> bool {
        self.symbol.owner().is_some_and(|owner| {
            owner.owner().representation() == PreparedAddressRepresentation::Bytes
        })
    }
    #[cfg(test)]
    pub(crate) fn symbol(&self) -> &Arc<CheckedForeignSymbol> {
        &self.symbol
    }
    #[cfg(test)]
    pub(crate) fn library(&self) -> NativeLibraryId {
        self.symbol.library()
    }
    pub(crate) fn operation(&self) -> OperationId {
        self.symbol.operation()
    }
    #[cfg(test)]
    pub(crate) const fn target(&self) -> ForeignBridgeTarget {
        self.target
    }
    #[cfg(test)]
    pub(crate) fn operands(&self) -> &[TargetOperand] {
        &self.operands
    }
    pub(crate) const fn result(&self) -> TargetResult {
        self.result
    }
    #[cfg(test)]
    pub(crate) fn native_type_projection(&self) -> &[usize] {
        self.symbol.symbol().native_type_projection()
    }
    pub(crate) fn rust_function_name(&self) -> &str {
        &self.rust_function_name
    }
}

/// Resolves only the admitted scalar/void subset, with no host-width fallback.
///
/// Exact registry/tag allocation and independent source correspondence precede
/// planning. Whole-program native inputs supply linker dependencies, and
/// executable registration must retain this same original symbol allocation.
#[cfg(test)]
pub(crate) fn plan_foreign_bridge(
    symbol: Arc<CheckedForeignSymbol>,
    target: &str,
    registry: &ResolvedRegistry,
    context: &ForeignBindingContext<'_>,
    work: &mut TypeWorkBudget,
) -> Result<TargetResolvedForeignBridge, ForeignBridgeFailure> {
    let span = prepared_span(&symbol, work)?;
    charge(
        work,
        target
            .len()
            .checked_add(3)
            .ok_or_else(|| fail(ForeignBridgeReason::Resource, span))?,
        span,
    )?;
    if target != TARGET {
        return Err(fail(ForeignBridgeReason::UnsupportedTarget, span));
    }
    if symbol.prepared().profile() != TARGET {
        return Err(fail(ForeignBridgeReason::UnsupportedProfile, span));
    }
    if !registry
        .native_symbol(symbol.operation())
        .is_some_and(|original| Arc::ptr_eq(original, &symbol))
        || !registry
            .effect(symbol.effect())
            .and_then(|effect| effect.native_contract.as_ref())
            .is_some_and(|original| Arc::ptr_eq(original, &symbol))
    {
        return Err(fail(ForeignBridgeReason::InvalidAuthority, span));
    }
    authenticate_foreign_symbol(&symbol, registry, context, work).map_err(|error| {
        fail(
            if error.is_resource_exhaustion() {
                ForeignBridgeReason::Resource
            } else {
                ForeignBridgeReason::InvalidAuthority
            },
            error.span(),
        )
    })?;
    plan_target_bridge(symbol, work, span)
}

/// A completed independent Core validation supplies source authentication.
/// Exact original table/tag allocation is still checked and charged here.
pub(crate) fn plan_foreign_bridge_in_program(
    symbol: Arc<CheckedForeignSymbol>,
    target: &str,
    program: &crate::core::ValidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> Result<TargetResolvedForeignBridge, ForeignBridgeFailure> {
    let span = prepared_span(&symbol, work)?;
    charge(
        work,
        target
            .len()
            .checked_add(3)
            .ok_or_else(|| fail(ForeignBridgeReason::Resource, span))?,
        span,
    )?;
    if target != TARGET {
        return Err(fail(ForeignBridgeReason::UnsupportedTarget, span));
    }
    if symbol.prepared().profile() != TARGET {
        return Err(fail(ForeignBridgeReason::UnsupportedProfile, span));
    }
    let registry = program.registry();
    if !registry
        .native_symbol(symbol.operation())
        .is_some_and(|original| Arc::ptr_eq(original, &symbol))
        || !registry
            .effect(symbol.effect())
            .and_then(|effect| effect.native_contract.as_ref())
            .is_some_and(|original| Arc::ptr_eq(original, &symbol))
    {
        return Err(fail(ForeignBridgeReason::InvalidAuthority, span));
    }
    plan_target_bridge(symbol, work, span)
}

fn plan_target_bridge(
    symbol: Arc<CheckedForeignSymbol>,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<TargetResolvedForeignBridge, ForeignBridgeFailure> {
    let source = symbol.symbol();
    charge(
        work,
        source
            .operands()
            .len()
            .checked_add(1)
            .ok_or_else(|| fail(ForeignBridgeReason::Resource, span))?,
        span,
    )?;
    let call = match source.call() {
        PreparedForeignCall::Scalar { .. } => {
            if symbol.owner().is_some() {
                return Err(fail(ForeignBridgeReason::InvalidAuthority, span));
            }
            TargetBridgeCall::Scalar
        }
        PreparedForeignCall::Owner(role) => {
            let owner = symbol
                .owner()
                .ok_or_else(|| fail(ForeignBridgeReason::InvalidAuthority, span))?;
            match role {
                PreparedOwnerCall::Acquire {
                    initialized_bytes, ..
                } => {
                    if !matches!(
                        (owner.owner().representation(), initialized_bytes),
                        (PreparedAddressRepresentation::Opaque, None)
                            | (PreparedAddressRepresentation::Bytes, Some(_))
                    ) || source.result()
                        != PreparedAbiResult::Address(owner.owner().representation())
                    {
                        return Err(fail(ForeignBridgeReason::UnsupportedRepresentation, span));
                    }
                    TargetBridgeCall::OwnerAcquire
                }
                PreparedOwnerCall::Teardown {
                    current_operand, ..
                }
                | PreparedOwnerCall::StatusTeardown {
                    current_operand, ..
                } => {
                    // Host destruction uses pre-admitted Current/Enclosing
                    // addresses; it performs no late scalar narrowing.
                    if !matches!(
                        source.result(),
                        PreparedAbiResult::Void | PreparedAbiResult::Scalar(_)
                    ) || !source
                        .operands()
                        .get(*current_operand)
                        .is_some_and(|operand| {
                            matches!(operand.source(), PreparedOperandSource::Current(_))
                                && operand.representation()
                                    == PreparedRepresentation::Address(
                                        owner.owner().representation(),
                                    )
                        })
                    {
                        return Err(fail(ForeignBridgeReason::UnsupportedRepresentation, span));
                    }
                    TargetBridgeCall::OwnerTeardown
                }
            }
        }
    };
    let mut operands = Vec::new();
    operands
        .try_reserve_exact(source.operands().len())
        .map_err(|_| fail(ForeignBridgeReason::Resource, span))?;
    for operand in source.operands() {
        let target = match (operand.source(), operand.representation()) {
            (
                PreparedOperandSource::Sentinel(index),
                PreparedRepresentation::FunctionAddressSentinel,
            ) => {
                let sentinel = symbol
                    .prepared()
                    .sentinels()
                    .get(*index)
                    .ok_or_else(|| fail(ForeignBridgeReason::InvalidAuthority, span))?;
                if symbol
                    .prepared()
                    .representations()
                    .get(sentinel.representation_index())
                    .is_none_or(|value| {
                        value.representation() != PreparedRepresentation::FunctionAddressSentinel
                    })
                {
                    return Err(fail(ForeignBridgeReason::InvalidAuthority, span));
                }
                TargetOperand::FunctionAddressSentinel
            }
            (
                PreparedOperandSource::Constant(index),
                PreparedRepresentation::Scalar(representation),
            ) => {
                if symbol
                    .prepared()
                    .constants()
                    .get(*index)
                    .is_none_or(|constant| constant.representation() != representation)
                {
                    return Err(fail(ForeignBridgeReason::InvalidAuthority, span));
                }
                TargetOperand::Scalar(target_scalar(representation, span)?)
            }

            (PreparedOperandSource::Source(_), PreparedRepresentation::Scalar(_))
                if call == TargetBridgeCall::OwnerTeardown =>
            {
                // The source contract is valid, but this target's infallible
                // host destructor has only pre-admitted guarded addresses.
                return Err(fail(ForeignBridgeReason::UnsupportedRepresentation, span));
            }
            (PreparedOperandSource::Source(_), PreparedRepresentation::Scalar(representation))
                if call != TargetBridgeCall::OwnerTeardown =>
            {
                TargetOperand::Scalar(target_scalar(representation, span)?)
            }
            (PreparedOperandSource::Enclosing(_), PreparedRepresentation::Address(_))
                if call != TargetBridgeCall::Scalar =>
            {
                TargetOperand::Address
            }
            (PreparedOperandSource::Current(_), PreparedRepresentation::Address(_))
                if call == TargetBridgeCall::OwnerTeardown =>
            {
                TargetOperand::Address
            }
            _ => return Err(fail(ForeignBridgeReason::InvalidAuthority, span)),
        };
        operands.push(target);
    }
    let result = match source.result() {
        PreparedAbiResult::Void => TargetResult::Void,
        PreparedAbiResult::Scalar(representation) => {
            TargetResult::Scalar(target_scalar(representation, span)?)
        }
        PreparedAbiResult::Address(_) if call == TargetBridgeCall::OwnerAcquire => {
            TargetResult::OwnerAddress
        }
        PreparedAbiResult::Address(_) => {
            return Err(fail(ForeignBridgeReason::UnsupportedRepresentation, span));
        }
    };
    let rust_function_name = operation_name(symbol.operation(), work, span)?;
    Ok(TargetResolvedForeignBridge {
        symbol,
        target: ForeignBridgeTarget::X86_64LinuxGnu,
        operands: operands.into_boxed_slice(),
        result,
        call,
        rust_function_name,
        span,
    })
}

fn prepared_span(
    symbol: &CheckedForeignSymbol,
    work: &mut TypeWorkBudget,
) -> Result<Span, ForeignBridgeFailure> {
    let fallback = symbol.call_codec().source();
    let mut origin = symbol.prepared().origin();
    loop {
        charge(work, 1, fallback)?;
        match origin {
            Origin::Source(span) => return Ok(*span),
            Origin::Generated { cause, .. } => origin = cause,
            Origin::Related { primary, related } => {
                charge(work, related.len(), fallback)?;
                origin = primary;
            }
        }
    }
}

fn operation_name(
    operation: OperationId,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<String, ForeignBridgeFailure> {
    fn digits(mut value: u32) -> usize {
        let mut count = 1;
        while value >= 10 {
            value /= 10;
            count += 1;
        }
        count
    }
    // The complete namespace/graph/value display is bounded by three u32
    // coordinates and a fixed namespace. Hex encoding is injective and only
    // makes a Rust identifier; it grants no binding authority.
    struct Identity {
        bytes: [u8; 96],
        len: usize,
    }
    impl Write for Identity {
        fn write_str(&mut self, text: &str) -> fmt::Result {
            let end = self.len.checked_add(text.len()).ok_or(fmt::Error)?;
            self.bytes
                .get_mut(self.len..end)
                .ok_or(fmt::Error)?
                .copy_from_slice(text.as_bytes());
            self.len = end;
            Ok(())
        }
    }
    charge(work, 96, span)?;
    let mut identity = Identity {
        bytes: [0; 96],
        len: 0,
    };
    write!(&mut identity, "{}", operation.owner().module())
        .map_err(|_| fail(ForeignBridgeReason::Resource, span))?;
    let capacity = identity
        .len
        .checked_mul(2)
        .and_then(|count| count.checked_add("__ash_native_m_e_o".len()))
        .and_then(|count| count.checked_add(digits(operation.owner().declaration())))
        .and_then(|count| count.checked_add(digits(operation.operation())))
        .ok_or_else(|| fail(ForeignBridgeReason::Resource, span))?;
    charge(
        work,
        capacity
            .checked_mul(2)
            .ok_or_else(|| fail(ForeignBridgeReason::Resource, span))?,
        span,
    )?;
    let mut output = String::new();
    output
        .try_reserve_exact(capacity)
        .map_err(|_| fail(ForeignBridgeReason::Resource, span))?;
    output.push_str("__ash_native_m");
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in &identity.bytes[..identity.len] {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 15)]));
    }
    write!(
        &mut output,
        "_e{}_o{}",
        operation.owner().declaration(),
        operation.operation()
    )
    .map_err(|_| fail(ForeignBridgeReason::Resource, span))?;
    debug_assert_eq!(output.len(), capacity);
    Ok(output)
}

fn render_bridge(output: &mut impl Write, plan: &TargetResolvedForeignBridge) -> fmt::Result {
    if plan.call == TargetBridgeCall::OwnerAcquire && plan.byte_owner() {
        let name = &plan.rust_function_name;
        write!(
            output,
            "pub fn {name}__read(address: *mut core::ffi::c_void, index: usize) -> u8 {{\n    // SAFETY: The original live guard admits index below its initialized byte extent.\n    unsafe {{ address.cast::<u8>().add(index).read() }}\n}}\npub fn {name}__write(address: *mut core::ffi::c_void, index: usize, byte: u8) {{\n    // SAFETY: The original unique guard admits index below its writable initialized extent.\n    unsafe {{ address.cast::<u8>().add(index).write(byte) }};\n}}\n"
        )?;
    }
    output.write_str("#[cfg(not(all(target_arch = \"x86_64\", target_os = \"linux\", target_env = \"gnu\", target_pointer_width = \"64\")))]\ncompile_error!(\"unsupported Ash native bridge target\");\nunsafe extern \"C\" {\n    #[link_name = \"")?;
    for character in plan.symbol.symbol().native_name().chars() {
        for escaped in character.escape_default() {
            output.write_char(escaped)?;
        }
    }
    write!(output, "\"]\n    fn {}__ffi(", plan.rust_function_name)?;
    for (index, scalar) in plan.operands.iter().enumerate() {
        if index > 0 {
            output.write_str(", ")?;
        }
        write!(output, "arg{index}: {}", scalar.rust_type())?;
    }
    output.write_str(")")?;
    match plan.result {
        TargetResult::Scalar(scalar) => write!(output, " -> {}", scalar.rust_type())?,
        TargetResult::OwnerAddress => output.write_str(" -> *mut core::ffi::c_void")?,
        TargetResult::Void => {}
    }
    match plan.call {
        TargetBridgeCall::Scalar => write!(
            output,
            ";\n}}\npub fn {}(arguments: &[{VALUE}]) -> Result<{REPLY}, {ERROR}> {{\n    let [",
            plan.rust_function_name
        )?,
        TargetBridgeCall::OwnerAcquire => write!(
            output,
            ";\n}}\npub fn {}(arguments: &[{OWNER_OPERAND}], readiness: {OWNER_READY}) -> Result<{OWNER_RETURNED}, {ERROR}> {{\n    let [",
            plan.rust_function_name
        )?,
        TargetBridgeCall::OwnerTeardown => {
            write!(
                output,
                ";\n}}\npub fn {}(arguments: &[{OWNER_OPERAND}])",
                plan.rust_function_name
            )?;
            if matches!(plan.result, TargetResult::Scalar(_)) {
                write!(output, " -> {REPLY}")?;
            }
            output.write_str(" {\n    let [")?;
        }
    }
    for (index, scalar) in plan.operands.iter().enumerate() {
        if index > 0 {
            output.write_str(", ")?;
        }
        match scalar {
            TargetOperand::FunctionAddressSentinel if plan.call == TargetBridgeCall::Scalar => {
                write!(output, "{VALUE}::FunctionAddressAllBitsOne")?
            }
            TargetOperand::FunctionAddressSentinel => write!(
                output,
                "{OWNER_OPERAND}::Scalar({VALUE}::FunctionAddressAllBitsOne)"
            )?,
            TargetOperand::Scalar(scalar) if plan.call == TargetBridgeCall::Scalar => {
                write!(output, "{VALUE}::{}(arg{index})", scalar.value_variant())?
            }
            TargetOperand::Scalar(scalar) => write!(
                output,
                "{OWNER_OPERAND}::Scalar({VALUE}::{}(arg{index}))",
                scalar.value_variant()
            )?,
            TargetOperand::Address => write!(output, "{OWNER_OPERAND}::Address(arg{index})")?,
        }
    }
    output.write_str("] = arguments else {\n")?;
    if plan.call == TargetBridgeCall::OwnerTeardown {
        output.write_str("        unreachable!(\"pre-admitted destruction operands\");\n")?;
    } else {
        writeln!(output, "        return Err({ERROR}::ArgumentContract);")?;
    }
    write!(
        output,
        "    }};\n    // SAFETY: Exact preflight supplies these ABI values and live guarded addresses.\n    // Linking assumes the authored synchronous native contract.\n    let value = unsafe {{ {}__ffi(",
        plan.rust_function_name
    )?;
    for index in 0..plan.operands.len() {
        if index > 0 {
            output.write_str(", ")?;
        }
        if plan.operands[index] == TargetOperand::FunctionAddressSentinel {
            // GNU64 represents this non-callable sentinel in the pointer ABI.
            // Never materialize an invalid Rust function pointer or invoke it.
            output.write_str("usize::MAX as *mut core::ffi::c_void")?;
        } else {
            write!(output, "*arg{index}")?;
        }
    }
    output.write_str(") };\n")?;
    match plan.result {
        TargetResult::Void if plan.call == TargetBridgeCall::OwnerTeardown =>
            output.write_str("    let () = value;\n}\n"),
        TargetResult::Void => write!(output, "    let () = value;\n    Ok({REPLY}::Void)\n}}\n"),
        TargetResult::Scalar(scalar) if plan.call == TargetBridgeCall::OwnerTeardown => write!(output, "    {REPLY}::Scalar({VALUE}::{}(value))\n}}\n", scalar.value_variant()),
        TargetResult::Scalar(scalar) => write!(
            output,
            "    Ok({REPLY}::Scalar({VALUE}::{}(value)))\n}}\n",
            scalar.value_variant()
        ),
        TargetResult::OwnerAddress => output.write_str(
            "    // Arm pre-admitted destruction before any Ash reporting step.\n    Ok(readiness.returned(value))\n}\n",
        ),
    }
}

/// Emits a fixed C ABI signature and one native call after exact count/tag checks.
/// The output must live in a generated bridge crate/module admitting this narrow
/// unsafe boundary; the initial Pure host still forbids unsafe code.
pub(crate) fn emit_rust_bridge(
    plan: &TargetResolvedForeignBridge,
    work: &mut TypeWorkBudget,
) -> Result<String, ForeignBridgeFailure> {
    struct Length(usize);
    impl Write for Length {
        fn write_str(&mut self, text: &str) -> fmt::Result {
            self.0 = self.0.checked_add(text.len()).ok_or(fmt::Error)?;
            Ok(())
        }
    }
    // Pay before the counting pass inspects native bytes and formats indices.
    let inspection = plan
        .symbol
        .symbol()
        .native_name()
        .len()
        .checked_mul(2)
        .and_then(|count| plan.operands.len().checked_mul(64)?.checked_add(count))
        .and_then(|count| count.checked_add(plan.rust_function_name.len().checked_mul(8)?))
        .ok_or_else(|| fail(ForeignBridgeReason::Resource, plan.span))?;
    charge(work, inspection, plan.span)?;
    let mut length = Length(0);
    render_bridge(&mut length, plan).map_err(|_| fail(ForeignBridgeReason::Resource, plan.span))?;
    charge(
        work,
        length
            .0
            .checked_mul(2)
            .ok_or_else(|| fail(ForeignBridgeReason::Resource, plan.span))?,
        plan.span,
    )?;
    let mut output = String::new();
    output
        .try_reserve_exact(length.0)
        .map_err(|_| fail(ForeignBridgeReason::Resource, plan.span))?;
    render_bridge(&mut output, plan).map_err(|_| fail(ForeignBridgeReason::Resource, plan.span))?;
    debug_assert_eq!(output.len(), length.0);
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        elaborate::check_module,
        foreign::checked_source::ForeignCallCodecIds,
        interface::InterfaceConstraintBudget,
        module::{ModuleId, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::CheckedModule,
        types::{ConstructorId, NominalTypeId},
    };
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    static IDS: AtomicU64 = AtomicU64::new(0);

    const SOURCE: &str = r#"import @builtin.foreign as Foreign
pub foreign library C {
    profile "x86_64-unknown-linux-gnu"
    repr I8 = signed(8)
    repr U8 = unsigned(8)
    repr I32 = signed(32)
    repr U32 = unsigned(32)
    repr I64 = signed(64)
    repr U64 = unsigned(64)
    repr Size = size_t
    symbol Mixed<Before : EffectRow, T, After : EffectRow, U> : (Int, Int, Int, Int, Int, Int, Int) -> Foreign.Call<Int> {
        name "odd\"symbol\\tail\nλ"
        abi (I8, U8, I32, U32, I64, U64, Size) -> Size
        operand 0 from 0 scalar
        operand 1 from 1 scalar
        operand 2 from 2 scalar
        operand 3 from 3 scalar
        operand 4 from 4 scalar
        operand 5 from 5 scalar
        operand 6 from 6 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Stop : Unit -> Foreign.Call<Unit> {
        name "stop"
        abi () -> void
        outcome otherwise {}
    }
}
main : Unit -> Int
main () = 42
"#;

    struct Fixture {
        directory: PathBuf,
        registry: ResolvedRegistry,
        common_module: ModuleId,
        common_span: Span,
        ids: ForeignCallCodecIds,
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.directory);
        }
    }

    impl Fixture {
        fn new() -> Self {
            Self::with_source(SOURCE)
        }

        fn with_source(source: &str) -> Self {
            let directory = loop {
                let number = IDS.fetch_add(1, Ordering::Relaxed);
                let directory = std::env::temp_dir()
                    .join(format!("ash-bridge-plan-{}-{number}", std::process::id()));
                match fs::create_dir(&directory) {
                    Ok(()) => break directory,
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("bridge fixture directory: {error}"),
                }
            };
            fs::write(directory.join("entry.ash"), source).unwrap();
            let graph =
                load_module_graph(&directory.join("entry.ash"), &ModuleRoots::empty()).unwrap();
            let common = graph
                .modules()
                .iter()
                .find(|module| module.id().is_builtin_foreign())
                .unwrap();
            let common_module = common.id();
            let common_span = common.surface().span;
            let call = NominalTypeId::new(common_module, 1);
            let ids = ForeignCallCodecIds {
                call,
                returned: ConstructorId::new(call, 0),
                conversion_failed: ConstructorId::new(call, 1),
                conversion_error: NominalTypeId::new(common_module, 0),
            };
            let mut checked: Vec<CheckedModule> = Vec::new();
            for module in graph.modules() {
                let dependencies: Vec<_> = module
                    .dependencies()
                    .iter()
                    .map(|edge| {
                        let dependency = checked
                            .iter()
                            .find(|checked| checked.module() == edge.target())
                            .unwrap();
                        DependencyExports::new(edge, dependency.exports()).unwrap()
                    })
                    .collect();
                let resolved = resolve_module(module, &dependencies).unwrap();
                checked.push(check_module(resolved).unwrap());
            }
            let registry = ResolvedRegistry::combine_checked(
                &checked,
                &mut TypeWorkBudget::default(),
                &mut InterfaceConstraintBudget::default(),
            )
            .unwrap();
            Self {
                directory,
                registry,
                common_module,
                common_span,
                ids,
            }
        }

        fn context(&self, work: &mut TypeWorkBudget) -> ForeignBindingContext<'_> {
            ForeignBindingContext::new(
                &self.registry,
                self.common_module,
                self.common_span,
                self.ids,
                work,
            )
            .unwrap()
        }

        fn symbol(&self, name: &str) -> Arc<CheckedForeignSymbol> {
            let effect = self
                .registry
                .effects()
                .iter()
                .find(|effect| effect.spelling == name)
                .unwrap();
            Arc::clone(effect.native_contract.as_ref().unwrap())
        }
    }

    const OWNER_SOURCE: &str = r#"import @builtin.foreign as Foreign
foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = opaque
    owner State<T, R> {
        representation Address
        owned R
        teardown Free
    }
    symbol Allocate<Delta : EffectRow, R, T> : Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<T, R>>>> {
        name "malloc"
        abi (Size) -> pointer(Address)
        operand 0 from 0 scalar
        output result as owner(State<T, R>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol Free<T, Delta : EffectRow, R> : State<T, R> -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Address)) -> void
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
}
main : Unit -> Int
main () = 42
"#;

    #[test]
    fn opaque_owner_bridges_use_separate_readiness_and_consuming_callback_roles() {
        let fixture = Fixture::with_source(OWNER_SOURCE);
        let mut work = TypeWorkBudget::default();
        let acquire =
            plan_target_bridge(fixture.symbol("Allocate"), &mut work, fixture.common_span).unwrap();
        assert_eq!(acquire.call(), TargetBridgeCall::OwnerAcquire);
        assert_eq!(acquire.native_type_projection(), &[1, 2]);
        assert_eq!(acquire.result(), TargetResult::OwnerAddress);
        let emitted = emit_rust_bridge(&acquire, &mut work).unwrap();
        assert!(emitted.contains("arg0: usize) -> *mut core::ffi::c_void"));
        assert!(emitted.contains("NativeOwnerGuardReady"));
        assert!(emitted.contains("NativeOwnerCallReturned"));
        assert!(emitted.contains("Ok(readiness.returned(value))"));
        assert!(
            emitted.find("ArgumentContract").unwrap() < emitted.find("let value = unsafe").unwrap()
        );
        assert!(!emitted.contains("NativeScalarReply"));

        let teardown =
            plan_target_bridge(fixture.symbol("Free"), &mut work, fixture.common_span).unwrap();
        assert_eq!(teardown.call(), TargetBridgeCall::OwnerTeardown);
        assert_eq!(teardown.native_type_projection(), &[0, 2]);
        let emitted = emit_rust_bridge(&teardown, &mut work).unwrap();
        assert!(emitted.contains("arg0: *mut core::ffi::c_void);"));
        assert!(emitted.contains("__ffi(*arg0)"));
        assert!(emitted.contains("arguments: &[ash::foreign::source_runtime::NativeOwnerOperand]"));
        assert!(!emitted.contains("NativeScalarValue"));
        assert!(!emitted.contains("NativeScalarReply"));
    }

    #[test]
    fn opaque_teardown_with_extra_scalar_native_operands_refuses_target_planning() {
        let source = OWNER_SOURCE
            .replace(
                "State<T, R> -> Foreign.Call<Foreign.Disposition<Unit>>",
                "(Int, State<T, R>) -> Foreign.Call<Foreign.Disposition<Unit>>",
            )
            .replace(
                "abi (pointer(Address)) -> void",
                "abi (Size, pointer(Address)) -> void",
            )
            .replace(
                "operand 0 from 0 current",
                "operand 0 from 0 scalar\n        operand 1 from 1 current",
            )
            .replace(
                "outcome otherwise { consumed 0 }",
                "outcome otherwise { consumed 1 }",
            );
        let fixture = Fixture::with_source(&source);
        let failure = plan_target_bridge(
            fixture.symbol("Free"),
            &mut TypeWorkBudget::default(),
            fixture.common_span,
        )
        .unwrap_err();
        assert_eq!(
            failure.reason(),
            ForeignBridgeReason::UnsupportedRepresentation
        );
    }

    #[test]
    fn initialized_byte_owner_bridges_retain_original_extent_and_owner_authority() {
        let source = OWNER_SOURCE
            .replace("repr Address = opaque", "repr Address = bytes")
            .replace(
                "outcome result nonnull { readable result }",
                "outcome result nonnull { readable result, initialized_bytes result from 0 }",
            );
        let fixture = Fixture::with_source(&source);
        for (name, role) in [
            ("Allocate", TargetBridgeCall::OwnerAcquire),
            ("Free", TargetBridgeCall::OwnerTeardown),
        ] {
            let symbol = fixture.symbol(name);
            let plan = plan_target_bridge(
                Arc::clone(&symbol),
                &mut TypeWorkBudget::default(),
                fixture.common_span,
            )
            .unwrap();
            assert_eq!(plan.call(), role);
            assert!(Arc::ptr_eq(plan.symbol(), &symbol));
            let emitted = emit_rust_bridge(&plan, &mut TypeWorkBudget::default()).unwrap();
            assert!(emitted.contains("*mut core::ffi::c_void"));
            assert!(!emitted.contains("NativeScalarReply"));
        }
        assert!(matches!(
            fixture.symbol("Allocate").owner_role(),
            Some(PreparedOwnerCall::Acquire { initialized_bytes: Some(extent), .. })
                if extent.extent() == [0]
        ));
    }

    #[test]
    fn public_source_plan_preserves_authority_order_projection_and_escaped_typed_calls() {
        let fixture = Fixture::new();
        let mut work = TypeWorkBudget::default();
        let context = fixture.context(&mut work);
        let symbol = fixture.symbol("Mixed");
        let plan = plan_foreign_bridge(
            Arc::clone(&symbol),
            TARGET,
            &fixture.registry,
            &context,
            &mut work,
        )
        .unwrap();
        assert!(Arc::ptr_eq(plan.symbol(), &symbol));
        assert_eq!(plan.operation(), symbol.operation());
        assert_eq!(plan.library(), symbol.library());
        assert_eq!(plan.target().triple(), TARGET);
        assert_eq!(plan.native_type_projection(), &[1, 3]);
        assert_eq!(
            plan.operands(),
            &[
                TargetOperand::Scalar(TargetScalar::I8),
                TargetOperand::Scalar(TargetScalar::U8),
                TargetOperand::Scalar(TargetScalar::I32),
                TargetOperand::Scalar(TargetScalar::U32),
                TargetOperand::Scalar(TargetScalar::I64),
                TargetOperand::Scalar(TargetScalar::U64),
                TargetOperand::Scalar(TargetScalar::USize64)
            ]
        );
        assert_eq!(plan.result(), TargetResult::Scalar(TargetScalar::USize64));
        let source = emit_rust_bridge(&plan, &mut work).unwrap();
        assert!(source.contains("#[link_name = \"odd\\\"symbol\\\\tail\\n\\u{3bb}\"]"));
        assert!(source.contains(
            "arg0: i8, arg1: u8, arg2: i32, arg3: u32, arg4: i64, arg5: u64, arg6: usize) -> usize"
        ));
        assert!(source.contains("::USize(value)"));
        assert!(source.contains(plan.rust_function_name()));
        assert_eq!(source.matches("let value = unsafe {").count(), 1);
        assert!(
            source.find("ArgumentContract").unwrap() < source.find("let value = unsafe").unwrap()
        );
        assert!(!source.contains("ForeignManifest"));
        assert!(!source.contains("ConversionFailed"));
        let stop = plan_foreign_bridge(
            fixture.symbol("Stop"),
            TARGET,
            &fixture.registry,
            &context,
            &mut work,
        )
        .unwrap();
        let source = emit_rust_bridge(&stop, &mut work).unwrap();
        assert!(source.contains("let [] = arguments else"));
        assert!(source.contains("::Void)"));
        assert!(stop.operands().is_empty());
        assert_eq!(stop.result(), TargetResult::Void);
    }

    #[test]
    fn target_and_original_registry_refusals_precede_emission_and_have_fresh_exact_retry() {
        let fixture = Fixture::new();
        let alternate = Fixture::new();
        let mut setup = TypeWorkBudget::default();
        let context = fixture.context(&mut setup);
        let symbol = fixture.symbol("Mixed");
        let error = plan_foreign_bridge(
            Arc::clone(&symbol),
            "aarch64-unknown-linux-gnu",
            &fixture.registry,
            &context,
            &mut setup,
        )
        .unwrap_err();
        assert_eq!(error.reason(), ForeignBridgeReason::UnsupportedTarget);
        assert_eq!(error.span(), symbol.prepared().origin().primary_span());
        let error = plan_foreign_bridge(
            alternate.symbol("Mixed"),
            TARGET,
            &fixture.registry,
            &context,
            &mut setup,
        )
        .unwrap_err();
        assert_eq!(error.reason(), ForeignBridgeReason::InvalidAuthority);
        let mut measured = TypeWorkBudget::unbounded();
        let plan = plan_foreign_bridge(
            Arc::clone(&symbol),
            TARGET,
            &fixture.registry,
            &context,
            &mut measured,
        )
        .unwrap();
        for limit in [0, measured.used() / 2, measured.used() - 1] {
            assert_eq!(
                plan_foreign_bridge(
                    Arc::clone(&symbol),
                    TARGET,
                    &fixture.registry,
                    &context,
                    &mut TypeWorkBudget::with_limit(limit)
                )
                .unwrap_err()
                .reason(),
                ForeignBridgeReason::Resource
            );
        }
        let retried = plan_foreign_bridge(
            Arc::clone(&symbol),
            TARGET,
            &fixture.registry,
            &context,
            &mut TypeWorkBudget::with_limit(measured.used()),
        )
        .unwrap();
        assert!(Arc::ptr_eq(retried.symbol(), &symbol));
        let mut emission = TypeWorkBudget::unbounded();
        let expected = emit_rust_bridge(&plan, &mut emission).unwrap();
        assert_eq!(
            emit_rust_bridge(&plan, &mut TypeWorkBudget::with_limit(emission.used())).unwrap(),
            expected
        );
        assert_eq!(
            emit_rust_bridge(&plan, &mut TypeWorkBudget::with_limit(emission.used() - 1))
                .unwrap_err()
                .reason(),
            ForeignBridgeReason::Resource
        );
        let alternate_context = alternate.context(&mut setup);
        let other = plan_foreign_bridge(
            alternate.symbol("Mixed"),
            TARGET,
            &alternate.registry,
            &alternate_context,
            &mut setup,
        )
        .unwrap();
        assert_ne!(plan.rust_function_name(), other.rust_function_name());
    }
}
