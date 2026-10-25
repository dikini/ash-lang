//! Typed pointer/void Rust calls for the supported source signatures.
use crate::{
    foreign::checked_source::{
        CheckedForeignSymbol, NativeArgument, NativeResult, authenticate_foreign_symbol,
    },
    source::Span,
    types::TypeWorkBudget,
};
use std::{
    fmt::{self, Write},
    sync::Arc,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ForeignBridgeReason {
    UnsupportedTarget,
    InvalidAuthority,
    Resource,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ForeignBridgeFailure {
    reason: ForeignBridgeReason,
    span: Span,
}
impl fmt::Display for ForeignBridgeFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "native bridge {:?}", self.reason)
    }
}
fn failure(reason: ForeignBridgeReason, span: Span) -> ForeignBridgeFailure {
    ForeignBridgeFailure { reason, span }
}
#[derive(Debug)]
pub(crate) struct TargetResolvedForeignBridge {
    symbol: Arc<CheckedForeignSymbol>,
    span: Span,
}
#[cfg(test)]
impl TargetResolvedForeignBridge {
    pub(crate) fn symbol(&self) -> &Arc<CheckedForeignSymbol> {
        &self.symbol
    }
}
pub(crate) fn plan_foreign_bridge_in_program(
    symbol: Arc<CheckedForeignSymbol>,
    target: &str,
    program: &crate::core::ValidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> Result<TargetResolvedForeignBridge, ForeignBridgeFailure> {
    let span = symbol.symbol().origin().primary_span();
    work.charge(target.len().saturating_add(1))
        .map_err(|()| failure(ForeignBridgeReason::Resource, span))?;
    if target != super::super::foreign::source_contract::PROFILE {
        return Err(failure(ForeignBridgeReason::UnsupportedTarget, span));
    }
    authenticate_foreign_symbol(&symbol, program.registry(), work)
        .map_err(|_| failure(ForeignBridgeReason::InvalidAuthority, span))?;
    Ok(TargetResolvedForeignBridge { symbol, span })
}
pub(super) fn admit_render_inspection_named(
    plan: &TargetResolvedForeignBridge,
    name_bytes: usize,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignBridgeFailure> {
    let count = plan
        .symbol
        .arguments()
        .len()
        .checked_mul(5)
        .and_then(|n| n.checked_add(plan.symbol.symbol().native_name().len()))
        .and_then(|n| n.checked_add(name_bytes))
        .ok_or_else(|| failure(ForeignBridgeReason::Resource, plan.span))?;
    work.charge(count)
        .map_err(|()| failure(ForeignBridgeReason::Resource, plan.span))
}
pub(super) fn render_bridge_named(
    output: &mut impl Write,
    plan: &TargetResolvedForeignBridge,
    name: &impl fmt::Display,
) -> fmt::Result {
    let arguments = plan.symbol.arguments();
    writeln!(
        output,
        "fn {name}(arguments: &[ash::foreign::source_runtime::NativeArgument]) -> Result<ash::foreign::source_runtime::NativeReply, ash::foreign::source_runtime::NativeCallError> {{"
    )?;
    output.write_str("    let [")?;
    for index in 0..arguments.len() {
        if index != 0 {
            output.write_str(", ")?;
        }
        write!(output, "a{index}")?;
    }
    output.write_str("] = arguments else { return Err(ash::foreign::source_runtime::NativeCallError); };\n    unsafe extern \"C\" {\n")?;
    writeln!(
        output,
        "        #[link_name = {:?}]",
        plan.symbol.symbol().native_name()
    )?;
    output.write_str("        fn native(")?;
    for (index, argument) in arguments.iter().enumerate() {
        if index != 0 {
            output.write_str(", ")?;
        }
        write!(
            output,
            "a{index}: {} core::ffi::c_void",
            if *argument == NativeArgument::Bytes {
                "*const"
            } else {
                "*mut"
            }
        )?;
    }
    writeln!(
        output,
        ") -> {};",
        if plan.symbol.result() == NativeResult::Void {
            "()"
        } else {
            "*mut core::ffi::c_void"
        }
    )?;
    output.write_str("    }\n    // SAFETY: the Ash declaration supplies the native signature and memory assumptions.\n    let result = unsafe { native(")?;
    for (index, argument) in arguments.iter().enumerate() {
        if index != 0 {
            output.write_str(", ")?;
        }
        write!(
            output,
            "a{index}.0{}",
            if *argument == NativeArgument::Bytes {
                ".cast_const()"
            } else {
                ""
            }
        )?;
    }
    output.write_str(") };\n")?;
    if plan.symbol.result() == NativeResult::Void {
        output.write_str(
            "    let () = result;\n    Ok(ash::foreign::source_runtime::NativeReply::Void)\n}\n",
        )
    } else {
        output.write_str("    Ok(ash::foreign::source_runtime::NativeReply::Address(result))\n}\n")
    }
}
#[cfg(test)]
pub(super) fn emit_rust_bridge_named(
    plan: &TargetResolvedForeignBridge,
    name: &impl fmt::Display,
    name_bytes: usize,
    work: &mut TypeWorkBudget,
) -> Result<String, ForeignBridgeFailure> {
    struct Length(usize);
    impl Write for Length {
        fn write_str(&mut self, value: &str) -> fmt::Result {
            self.0 = self.0.checked_add(value.len()).ok_or(fmt::Error)?;
            Ok(())
        }
    }
    admit_render_inspection_named(plan, name_bytes, work)?;
    let mut length = Length(0);
    render_bridge_named(&mut length, plan, name)
        .map_err(|_| failure(ForeignBridgeReason::Resource, plan.span))?;
    work.charge(
        length
            .0
            .checked_mul(2)
            .ok_or_else(|| failure(ForeignBridgeReason::Resource, plan.span))?,
    )
    .map_err(|()| failure(ForeignBridgeReason::Resource, plan.span))?;
    let mut output = String::new();
    output
        .try_reserve_exact(length.0)
        .map_err(|_| failure(ForeignBridgeReason::Resource, plan.span))?;
    render_bridge_named(&mut output, plan, name)
        .map_err(|_| failure(ForeignBridgeReason::Resource, plan.span))?;
    Ok(output)
}
