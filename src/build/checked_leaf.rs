//! Exact fixed-profile opaque transport generation; no execution authority.
use super::{
    bridge::{ForeignBridgeTarget, TargetBridgeCall, TargetOperand, TargetResult, TargetScalar},
    image::NativeBuildImage,
};
use crate::{foreign::source_contract::PreparedOwnerCall, types::TypeWorkBudget};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LeafFailure {
    Resource,
    Unsupported,
    Association,
}
pub(super) struct LeafEmission {
    pub source: String,
    // Existing NativeBuildImage positions, in acquire/query/length/release order.
    // These are a projection of authenticated bridges, never another registry.
    pub members: Vec<usize>,
    pub profile: LeafProfile,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LeafProfile { InitializedBytes, OutputStatus, DependentOutputStatus }
impl LeafProfile {
    fn tag(self) -> u8 { match self { Self::InitializedBytes => 0, Self::OutputStatus => 1, Self::DependentOutputStatus => 2 } }
}
const OUTPUT_TEMPLATE: &str = include_str!("checked_owner_output_status.rs.in");
const TEMPLATE: &str = include_str!("checked_owner_leaf.rs.in");
const ROOT_SHIM: &str = include_str!("checked_owner_root_shim.rs.in");

/// The fixed private root shim names only opaque leaf types. Its complete bytes
/// are code/config identity inputs, never an excluded program-data payload.
pub(super) fn render_root_shim(work: &mut TypeWorkBudget) -> Result<String, LeafFailure> {
    pay(work, ROOT_SHIM.len().checked_mul(2).ok_or(LeafFailure::Resource)?)?;
    let mut source = String::new();
    source.try_reserve_exact(ROOT_SHIM.len()).map_err(|_| LeafFailure::Resource)?;
    source.push_str(ROOT_SHIM);
    Ok(source)
}

/// Passive role coordinates emitted from the same authenticated projection as
/// the four native names. Root-local restoration must independently admit all
/// original types/ABIs and scope relationships before using these DATA fields.
pub(super) fn render_admitted_root_shim(
    image: &NativeBuildImage,
    leaf: &LeafEmission,
    work: &mut TypeWorkBudget,
) -> Result<String, LeafFailure> {
    use std::fmt::Write;
    let [library] = image.libraries.as_slice() else { return Err(LeafFailure::Association); };
    let count = match leaf.profile { LeafProfile::InitializedBytes => 4, LeafProfile::OutputStatus => 2, LeafProfile::DependentOutputStatus => 4 };
    if leaf.members.len() != count { return Err(LeafFailure::Association); }
    let mut source = render_root_shim(work)?;
    // Exactly32 u32 decimal fields (at most10 digits each), punctuation and
    // fixed declaration:1024 bytes bounds all output; prepay formatting/storage.
    pay(work, 2048 + 32)?;
    source.try_reserve_exact(1024).map_err(|_| LeafFailure::Resource)?;
    let start = source.len();
    source.push_str("\n// image-library, library-module, library-ordinal, image-symbol, symbol-index, operation-module, effect, local\n");
    writeln!(&mut source, "pub(crate) const CHECKED_PROFILE: u8 = {};", leaf.profile.tag()).map_err(|_|LeafFailure::Resource)?;
    writeln!(&mut source, "pub(crate) const CHECKED_ROLES: [[u32; 8]; {}] = [", leaf.members.len()).map_err(|_|LeafFailure::Resource)?;
    for &index in &leaf.members {
        let member = image.bridges.get(index).ok_or(LeafFailure::Association)?;
        if !library.members.contains(&index) { return Err(LeafFailure::Association); }
        writeln!(&mut source, "[{}, {}, {}, {}, {}, {}, {}, {}],", library.image_library,
            library.module, library.ordinal, member.image_symbol, member.symbol_index,
            member.operation_module, member.operation_effect, member.operation_local)
            .map_err(|_| LeafFailure::Resource)?;
    }
    source.push_str("];\n");
    if source.len() - start > 1024 { return Err(LeafFailure::Resource); }
    Ok(source)
}

const MARKERS: [&str; 4] = [
    "__ACQUIRE_NAME__",
    "__QUERY_NAME__",
    "__LENGTH_NAME__",
    "__RELEASE_NAME__",
];
fn pay(work: &mut TypeWorkBudget, n: usize) -> Result<(), LeafFailure> {
    work.charge(n).map_err(|()| LeafFailure::Resource)
}
fn quoted(name: &str, work: &mut TypeWorkBudget) -> Result<String, LeafFailure> {
    pay(work, name.len())?;
    let escaped = name.chars().flat_map(char::escape_default).count();
    let size = escaped.checked_add(2).ok_or(LeafFailure::Resource)?;
    pay(
        work,
        name.len().checked_add(size).ok_or(LeafFailure::Resource)?,
    )?;
    let mut value = String::new();
    value
        .try_reserve_exact(size)
        .map_err(|_| LeafFailure::Resource)?;
    value.push('"');
    for character in name.chars().flat_map(char::escape_default) {
        value.push(character);
    }
    value.push('"');
    Ok(value)
}
/// Select only four exact original checked bridges. Unknown/extra/same-shaped
/// donor plans refuse; the current native transaction still proves actual ABI
/// header correspondence and retains all generated input bytes separately.
pub(super) fn render(
    image: &NativeBuildImage,
    work: &mut TypeWorkBudget,
) -> Result<LeafEmission, LeafFailure> {
    pay(work, image.bridges.len())?;
    if image.bridges.len() == 2 { return render_output_status(image, work); }
    if image.bridges.len() == 4 && image.bridges.iter().any(|member|
        matches!(member.plan.symbol().owner_role(), Some(PreparedOwnerCall::OutputAcquire { offset: Some(_), .. }))) {
        return render_dependent_output_status(image, work);
    }
    if image.bridges.len() != 4 || image.libraries.len() != 1 {
        return Err(LeafFailure::Unsupported);
    }
    let mut selected = [None; 4];
    for (index, member) in image.bridges.iter().enumerate() {
        let plan = &member.plan;
        pay(
            work,
            8usize
                .checked_add(plan.operands().len())
                .ok_or(LeafFailure::Resource)?,
        )?;
        if plan.target() != ForeignBridgeTarget::X86_64LinuxGnu
            || !plan.byte_owner()
            || plan.symbol().prepared().checked_contract().is_none()
        {
            return Err(LeafFailure::Unsupported);
        }
        let role = match (plan.call(), plan.operands(), plan.result()) {
            (
                TargetBridgeCall::OwnerAcquire,
                [
                    TargetOperand::Scalar(TargetScalar::USize64),
                    TargetOperand::Scalar(TargetScalar::USize64),
                ],
                TargetResult::OwnerAddress,
            ) => {
                if !matches!(plan.symbol().owner_role(), Some(PreparedOwnerCall::Acquire {
                    initialized_bytes: Some(initialized), first_nonnull: true, ..
                }) if initialized.extent() == [1])
                {
                    return Err(LeafFailure::Unsupported);
                }
                0
            }
            (
                TargetBridgeCall::WindowView,
                [
                    TargetOperand::Address,
                    TargetOperand::Scalar(TargetScalar::USize64),
                ],
                TargetResult::ViewAddress,
            ) => 1,
            (
                TargetBridgeCall::OwnerBorrow,
                [
                    TargetOperand::Address,
                    TargetOperand::Scalar(TargetScalar::USize64),
                ],
                TargetResult::Scalar(TargetScalar::USize64),
            ) => 2,
            (TargetBridgeCall::OwnerTeardown, [TargetOperand::Address], TargetResult::Void) => {
                if !matches!(
                    plan.symbol().owner_role(),
                    Some(PreparedOwnerCall::Teardown {
                        current_operand: 0,
                        consumes: true,
                        ..
                    })
                ) {
                    return Err(LeafFailure::Unsupported);
                }
                3
            }
            _ => return Err(LeafFailure::Unsupported),
        };
        if selected[role].replace(index).is_some() {
            return Err(LeafFailure::Association);
        }
    }
    let members = selected.map(|member| member.ok_or(LeafFailure::Association));
    let members = [members[0]?, members[1]?, members[2]?, members[3]?];
    let first = &image.bridges[members[0]].plan;
    let owner = first.symbol().owner().ok_or(LeafFailure::Association)?;
    for index in members {
        pay(work, 3)?;
        let plan = &image.bridges[index].plan;
        if plan.library() != first.library()
            || !plan
                .symbol()
                .owner()
                .is_some_and(|candidate| Arc::ptr_eq(candidate, owner))
        {
            return Err(LeafFailure::Association);
        }
    }
    let mut names = Vec::new();
    pay(work, 4)?;
    names
        .try_reserve_exact(4)
        .map_err(|_| LeafFailure::Resource)?;
    for index in members {
        names.push(quoted(
            image.bridges[index].plan.symbol().symbol().native_name(),
            work,
        )?);
    }
    // Prepay four whole-template marker counts and all four bounded split scans
    // before allocation or writes.
    pay(
        work,
        TEMPLATE.len().checked_mul(8).ok_or(LeafFailure::Resource)?,
    )?;
    let mut size = TEMPLATE.len();
    for (marker, value) in MARKERS.iter().zip(&names) {
        if TEMPLATE.matches(marker).count() != 1 {
            return Err(LeafFailure::Association);
        }
        size = size
            .checked_sub(marker.len())
            .and_then(|n| n.checked_add(value.len()))
            .ok_or(LeafFailure::Resource)?;
    }
    pay(work, size)?;
    let mut source = String::new();
    source
        .try_reserve_exact(size)
        .map_err(|_| LeafFailure::Resource)?;
    let mut remainder = TEMPLATE;
    for (marker, value) in MARKERS.iter().zip(names) {
        let (prefix, suffix) = remainder
            .split_once(marker)
            .ok_or(LeafFailure::Association)?;
        source.push_str(prefix);
        source.push_str(&value);
        remainder = suffix;
    }
    source.push_str(remainder);
    if source.len() != size {
        return Err(LeafFailure::Association);
    }
    pay(work, 4)?;
    let mut retained = Vec::new();
    retained.try_reserve_exact(4).map_err(|_|LeafFailure::Resource)?;
    retained.extend_from_slice(&members);
    Ok(LeafEmission { source, members: retained, profile: LeafProfile::InitializedBytes })
}

/// The independent opaque output/status profile has exactly two original
/// members. Operand shape is closed; constants/outcome predicates are emitted
/// from those originals, never supplied as runtime invocation parameters.
fn render_output_status(image: &NativeBuildImage, work: &mut TypeWorkBudget) -> Result<LeafEmission, LeafFailure> {
    use crate::foreign::source_contract::{PreparedAbiResult as Abi, PreparedAddressRepresentation as Address,
        PreparedNativePosition, PreparedOperandSource as Source, PreparedScalarRepresentation as Repr};
    use std::fmt::Write;
    if image.libraries.len() != 1 { return Err(LeafFailure::Unsupported); }
    let mut acquire = None;
    let mut teardown = None;
    for (index, member) in image.bridges.iter().enumerate() {
        let plan = &member.plan;
        pay(work, plan.operands().len().checked_add(8).ok_or(LeafFailure::Resource)?)?;
        if plan.target() != ForeignBridgeTarget::X86_64LinuxGnu || plan.byte_owner()
            || plan.symbol().prepared().checked_contract().is_none() { return Err(LeafFailure::Unsupported); }
        let ops = plan.symbol().symbol().operands();
        match (plan.call(), plan.symbol().owner_role(), plan.operands(), plan.result()) {
            (TargetBridgeCall::OwnerOutputAcquire, Some(PreparedOwnerCall::OutputAcquire { output_operand: 1, offset: None, .. }),
                [TargetOperand::Address, TargetOperand::OwnerOutput, TargetOperand::Scalar(TargetScalar::I32), TargetOperand::Address],
                TargetResult::Scalar(_))
                if ops.len() == 4 && matches!(ops[0].source(), Source::Nul(_))
                    && matches!(ops[1].source(), Source::OwnerOutput)
                    && matches!(ops[2].source(), Source::Constant(_))
                    && matches!(ops[3].source(), Source::Null) => {
                if acquire.replace(index).is_some() { return Err(LeafFailure::Association); }
            }
            (TargetBridgeCall::OwnerTeardown, Some(PreparedOwnerCall::StatusTeardown { current_operand: 0, .. }),
                [TargetOperand::Address], TargetResult::Scalar(_))
                if ops.len() == 1 && matches!(ops[0].source(), Source::Current(_)) => {
                if teardown.replace(index).is_some() { return Err(LeafFailure::Association); }
            }
            _ => return Err(LeafFailure::Unsupported),
        }
    }
    let members = [acquire.ok_or(LeafFailure::Association)?, teardown.ok_or(LeafFailure::Association)?];
    let open = &image.bridges[members[0]].plan;
    let close = &image.bridges[members[1]].plan;
    let owner = open.symbol().owner().ok_or(LeafFailure::Association)?;
    pay(work, 4)?;
    if owner.owner().representation() != Address::Opaque || !owner.owner().retained_parameters().is_empty()
        || open.library() != close.library()
        || !close.symbol().owner().is_some_and(|other| Arc::ptr_eq(owner, other)) {
        return Err(LeafFailure::Association);
    }
    let Source::Constant(constant) = open.symbol().symbol().operands()[2].source() else { return Err(LeafFailure::Association); };
    let constant = open.symbol().prepared().constants().get(*constant).ok_or(LeafFailure::Association)?;
    if constant.representation() != Repr::Signed(32) { return Err(LeafFailure::Unsupported); }
    let value = constant.value();
    let flags = if value.negative { -i128::from(value.magnitude) } else { i128::from(value.magnitude) };
    let flags = i32::try_from(flags).map_err(|_|LeafFailure::Unsupported)?;
    let TargetResult::Scalar(open_scalar) = open.result() else { return Err(LeafFailure::Association); };
    let TargetResult::Scalar(close_scalar) = close.result() else { return Err(LeafFailure::Association); };
    if !matches!(open.symbol().symbol().result(), Abi::Scalar(_)) { return Err(LeafFailure::Association); }
    let Some(PreparedOwnerCall::StatusTeardown { outcomes, .. }) = close.symbol().owner_role() else { return Err(LeafFailure::Association); };
    if outcomes.is_empty() || outcomes.len() > 64 { return Err(LeafFailure::Unsupported); }
    // Each predicate writes at most128 ASCII bytes; final branches at most64.
    // Charge and reserve before formatting or traversing dynamic predicate lists.
    let mut outcome_source = String::new();
    let mut otherwise = false;
    pay(work, outcomes.len())?;
    for outcome in outcomes {
        let count = outcome.predicates.len();
        if count > 1 || otherwise { return Err(LeafFailure::Unsupported); }
        pay(work, 512)?;
        outcome_source.try_reserve(256).map_err(|_|LeafFailure::Resource)?;
        if let Some(predicate) = outcome.predicates.first() {
            if predicate.position != PreparedNativePosition::Result { return Err(LeafFailure::Unsupported); }
            let value = predicate.value;
            let value = if value.negative { -i128::from(value.magnitude) } else { i128::from(value.magnitude) };
            if !scalar_contains(close_scalar, value) { return Err(LeafFailure::Association); }
            write!(&mut outcome_source, "if status == ({value} as {}) {{ Some(({}, {})) }} else ",
                close_scalar.rust_type(), outcome.consumes, outcome.readable).map_err(|_|LeafFailure::Resource)?;
        } else {
            otherwise = true;
            write!(&mut outcome_source, "{{ Some(({}, {})) }}", outcome.consumes, outcome.readable).map_err(|_|LeafFailure::Resource)?;
        }
    }
    if !otherwise { return Err(LeafFailure::Unsupported); }
    let acquire_name = quoted(open.symbol().symbol().native_name(), work)?;
    let release_name = quoted(close.symbol().symbol().native_name(), work)?;
    pay(work, 128)?;
    let flags = format!("{flags}_i32");
    let replacements = [
        ("__ACQUIRE_NAME__", acquire_name.as_str()), ("__ACQUIRE_TYPE__", open_scalar.rust_type()),
        ("__RELEASE_NAME__", release_name.as_str()), ("__RELEASE_TYPE__", close_scalar.rust_type()),
        ("__FLAGS__", flags.as_str()), ("__ACQUIRE_VARIANT__", open_scalar.value_variant()),
        ("__OUTCOMES__", outcome_source.as_str()), ("__RELEASE_VARIANT__", close_scalar.value_variant()),
    ];
    let source = replace_template(OUTPUT_TEMPLATE, &replacements, work)?;
    pay(work, 2)?;
    let mut retained = Vec::new(); retained.try_reserve_exact(2).map_err(|_|LeafFailure::Resource)?;
    retained.extend_from_slice(&members);
    Ok(LeafEmission { source, members: retained, profile: LeafProfile::OutputStatus })
}
// The two-owner profile selects exact existing originals, never native names.
fn render_dependent_output_status(image: &NativeBuildImage, work: &mut TypeWorkBudget) -> Result<LeafEmission, LeafFailure> {
    use crate::foreign::{checked_source, source_contract::{PreparedOwnerCall as Role, PreparedOperandSource as Source,
        PreparedScalarRepresentation as Scalar}};
    if image.libraries.len() != 1 || image.bridges.len() != 4 { return Err(LeafFailure::Unsupported); }
    let mut members = [None; 4];
    for (index, member) in image.bridges.iter().enumerate() {
        let plan = &member.plan;
        pay(work, 24)?;
        if plan.target() != ForeignBridgeTarget::X86_64LinuxGnu || plan.byte_owner()
            || plan.symbol().prepared().checked_contract().is_none()
            || plan.result() != TargetResult::Scalar(TargetScalar::I32) { return Err(LeafFailure::Unsupported); }
        let role = match plan.symbol().owner_role() {
            Some(Role::OutputAcquire { .. }) if checked_source::independent_output_acquire(plan.symbol().symbol()) => 0,
            Some(Role::StatusTeardown { .. }) if plan.symbol().owner().is_some_and(|owner|owner.owner().retained_parameters().is_empty())
                && checked_source::independent_status_teardown(plan.symbol().symbol()) => 1,
            Some(Role::OutputAcquire { .. }) if checked_source::dependent_output_acquire(plan.symbol().prepared(), plan.symbol().symbol()) => 2,
            Some(Role::StatusTeardown { .. }) if checked_source::dependent_status_teardown(plan.symbol().prepared(), plan.symbol().symbol()) => 3,
            _ => return Err(LeafFailure::Unsupported),
        };
        let expected: &[TargetOperand] = match role {
            0 => &[TargetOperand::Address, TargetOperand::OwnerOutput, TargetOperand::Scalar(TargetScalar::I32), TargetOperand::Address],
            2 => &[TargetOperand::Address, TargetOperand::Address, TargetOperand::Scalar(TargetScalar::I32), TargetOperand::OwnerOutput, TargetOperand::OffsetOutput],
            _ => &[TargetOperand::Address],
        };
        if plan.operands() != expected || members[role].replace(index).is_some() { return Err(LeafFailure::Association); }
    }
    let [Some(parent_acquire), Some(parent_teardown), Some(child_acquire), Some(child_teardown)] = members
        else { return Err(LeafFailure::Association); };
    let members = [parent_acquire, parent_teardown, child_acquire, child_teardown];
    let plans = members.map(|index|&image.bridges[index].plan);
    pay(work, 16)?;
    let parent = plans[0].symbol().owner().ok_or(LeafFailure::Association)?;
    let child = plans[2].symbol().owner().ok_or(LeafFailure::Association)?;
    if Arc::ptr_eq(parent, child)
        || !plans[1].symbol().owner().is_some_and(|owner|Arc::ptr_eq(owner, parent))
        || !plans[3].symbol().owner().is_some_and(|owner|Arc::ptr_eq(owner, child))
        || plans.iter().any(|plan|plan.library() != plans[0].library()
            || !Arc::ptr_eq(plan.symbol().prepared(), plans[0].symbol().prepared())) { return Err(LeafFailure::Association); }
    let Source::Constant(constant) = plans[0].symbol().symbol().operands()[2].source() else { return Err(LeafFailure::Association); };
    let constant = plans[0].symbol().prepared().constants().get(*constant).ok_or(LeafFailure::Association)?;
    if constant.representation() != Scalar::Signed(32) { return Err(LeafFailure::Unsupported); }
    let value = constant.value();
    let flags = if value.negative { -i128::from(value.magnitude) } else { i128::from(value.magnitude) };
    let flags = i32::try_from(flags).map_err(|_|LeafFailure::Unsupported)?;
    let Some(Role::OutputAcquire { offset: Some(offset), .. }) = plans[2].symbol().owner_role() else { return Err(LeafFailure::Association); };
    let value = offset.status;
    let status = if value.negative { -i128::from(value.magnitude) } else { i128::from(value.magnitude) };
    let status = i32::try_from(status).map_err(|_|LeafFailure::Unsupported)?;
    let names = [
        quoted(plans[0].symbol().symbol().native_name(), work)?, quoted(plans[1].symbol().symbol().native_name(), work)?,
        quoted(plans[2].symbol().symbol().native_name(), work)?, quoted(plans[3].symbol().symbol().native_name(), work)?,
    ];
    let parent_outcomes = render_status_outcomes(plans[1], work)?;
    let child_outcomes = render_status_outcomes(plans[3], work)?;
    pay(work, 256)?;
    let flags = format!("{flags}_i32"); let status = format!("{status}_i32");
    let source = replace_template(include_str!("checked_owner_dependent_output_status.rs.in"), &[
        ("__PARENT_ACQUIRE_NAME__", &names[0]), ("__PARENT_RELEASE_NAME__", &names[1]),
        ("__CHILD_ACQUIRE_NAME__", &names[2]), ("__CHILD_RELEASE_NAME__", &names[3]),
        ("__FLAGS__", &flags), ("__OFFSET_STATUS__", &status),
        ("__PARENT_OUTCOMES__", &parent_outcomes), ("__CHILD_OUTCOMES__", &child_outcomes),
    ], work)?;
    pay(work, 4)?;
    let mut retained = Vec::new(); retained.try_reserve_exact(4).map_err(|_|LeafFailure::Resource)?;
    retained.extend_from_slice(&members);
    Ok(LeafEmission { source, members: retained, profile: LeafProfile::DependentOutputStatus })
}
fn render_status_outcomes(plan: &super::bridge::TargetResolvedForeignBridge, work: &mut TypeWorkBudget) -> Result<String, LeafFailure> {
    use crate::foreign::source_contract::PreparedNativePosition;
    use std::fmt::Write;
    let Some(PreparedOwnerCall::StatusTeardown { outcomes, .. }) = plan.symbol().owner_role() else { return Err(LeafFailure::Association); };
    if outcomes.is_empty() || outcomes.len() > 64 { return Err(LeafFailure::Unsupported); }
    let mut source = String::new(); let mut otherwise = false;
    pay(work, outcomes.len())?;
    for outcome in outcomes {
        if outcome.predicates.len() > 1 || otherwise { return Err(LeafFailure::Unsupported); }
        pay(work, 512)?; source.try_reserve(256).map_err(|_|LeafFailure::Resource)?;
        if let Some(predicate) = outcome.predicates.first() {
            if predicate.position != PreparedNativePosition::Result { return Err(LeafFailure::Unsupported); }
            let value = predicate.value;
            let value = if value.negative { -i128::from(value.magnitude) } else { i128::from(value.magnitude) };
            if !scalar_contains(TargetScalar::I32, value) { return Err(LeafFailure::Association); }
            write!(&mut source, "if status == ({value} as i32) {{ Some(({}, {})) }} else ", outcome.consumes, outcome.readable).map_err(|_|LeafFailure::Resource)?;
        } else {
            otherwise = true;
            write!(&mut source, "{{ Some(({}, {})) }}", outcome.consumes, outcome.readable).map_err(|_|LeafFailure::Resource)?;
        }
    }
    if !otherwise { return Err(LeafFailure::Unsupported); }
    Ok(source)
}
fn scalar_contains(scalar: TargetScalar, value: i128) -> bool {
    match scalar {
        TargetScalar::I8 => i8::try_from(value).is_ok(), TargetScalar::U8 => u8::try_from(value).is_ok(),
        TargetScalar::I32 => i32::try_from(value).is_ok(), TargetScalar::U32 => u32::try_from(value).is_ok(),
        TargetScalar::I64 => i64::try_from(value).is_ok(), TargetScalar::U64 | TargetScalar::USize64 => u64::try_from(value).is_ok(),
    }
}
fn replace_template(template: &str, replacements: &[(&str, &str)], work: &mut TypeWorkBudget) -> Result<String, LeafFailure> {
    // Separate paid replacements keep each scan/allocation bounded by actual
    // bytes, and check exactly one occurrence before each mutation.
    pay(work, template.len())?;
    let mut source = String::new(); source.try_reserve_exact(template.len()).map_err(|_|LeafFailure::Resource)?;
    source.push_str(template);
    for &(marker, value) in replacements {
        pay(work, source.len().checked_mul(2).and_then(|n|n.checked_add(value.len())).ok_or(LeafFailure::Resource)?)?;
        if source.matches(marker).count() != 1 { return Err(LeafFailure::Association); }
        let (left, right) = source.split_once(marker).ok_or(LeafFailure::Association)?;
        let size = left.len().checked_add(value.len()).and_then(|n|n.checked_add(right.len())).ok_or(LeafFailure::Resource)?;
        pay(work, size)?;
        let mut next = String::new(); next.try_reserve_exact(size).map_err(|_|LeafFailure::Resource)?;
        next.push_str(left); next.push_str(value); next.push_str(right); source = next;
    }
    Ok(source)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> NativeBuildImage {
        let (program, sources) = crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
        );
        super::super::image::encode_checked_preparation(
            &program,
            &sources,
            super::super::host::NATIVE_TARGET,
            &mut super::super::gas::preparation(&sources, program.node_count()).unwrap(),
        )
        .unwrap()
    }
    fn output_status_fixture() -> NativeBuildImage {
        let (program,sources)=crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../tests/fixtures/checked-owner-lifecycle/output-status.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Int, Unit, Unit>\nmain () = Producer.run ()\n",
        );
        super::super::image::encode_checked_preparation(&program,&sources,super::super::host::NATIVE_TARGET,
            &mut super::super::gas::preparation(&sources,program.node_count()).unwrap()).unwrap()
    }

    #[test]
    fn dependent_leaf_keeps_original_parent_output_offset_and_dispositions() {
        let (program, sources) = crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../libraries/sqlite_checked.ash"),
            include_str!("../../tests/fixtures/checked-sqlite/dependent-physical-entry.ash"),
        );
        let mut image = super::super::image::encode_checked_preparation(&program, &sources,
            super::super::host::NATIVE_TARGET, &mut super::super::gas::preparation(&sources, program.node_count()).unwrap()).unwrap();
        let leaf = render(&image, &mut TypeWorkBudget::default()).unwrap();
        assert_eq!(leaf.profile, LeafProfile::DependentOutputStatus);
        assert_eq!(leaf.members.len(), 4);
        assert!(leaf.source.contains("prepare_dependent_output_acquire"));
        assert!(leaf.source.contains("sqlite3_prepare_v2"));
        assert!(leaf.source.contains("sqlite3_finalize"));
        assert!(!leaf.source.contains("impl Drop"));
        let mut measured = TypeWorkBudget::default();
        let canonical = render(&image, &mut measured).unwrap();
        let cost = measured.used();
        let mut short = TypeWorkBudget::with_limit(cost - 1);
        assert!(matches!(render(&image, &mut short), Err(LeafFailure::Resource)));
        let mut exact = TypeWorkBudget::with_limit(cost);
        assert_eq!(render(&image, &mut exact).unwrap().source, canonical.source);
        assert_eq!(exact.used(), cost);
        assert!(matches!(render(&image, &mut exact), Err(LeafFailure::Resource)));
        let mut fresh = TypeWorkBudget::with_limit(cost);
        assert_eq!(render(&image, &mut fresh).unwrap().members, canonical.members);
        let shim = render_admitted_root_shim(&image, &canonical, &mut TypeWorkBudget::default()).unwrap();
        assert!(shim.contains("const CHECKED_PROFILE: u8 = 2"));
        assert!(shim.contains("const CHECKED_ROLES: [[u32; 8]; 4]"));
        // A genuine donor graph of the same source has different original owners.
        for index in &canonical.members {
            let (program, sources) = crate::elaborate::checked_owner_passive_program_for_source(
                include_str!("../../libraries/sqlite_checked.ash"),
                include_str!("../../tests/fixtures/checked-sqlite/dependent-physical-entry.ash"));
            let mut donor = super::super::image::encode_checked_preparation(&program, &sources,
                super::super::host::NATIVE_TARGET, &mut super::super::gas::preparation(&sources, program.node_count()).unwrap()).unwrap();
            std::mem::swap(&mut donor.bridges[*index].plan, &mut image.bridges[*index].plan);
            assert!(render(&donor, &mut TypeWorkBudget::default()).is_err());
            std::mem::swap(&mut donor.bridges[*index].plan, &mut image.bridges[*index].plan);
        }
    }
    #[test]
    fn two_role_leaf_binds_total_originals_and_exact_render_work() {
        let mut image=output_status_fixture();
        let mut measured=TypeWorkBudget::default();
        let canonical=render(&image,&mut measured).unwrap();
        assert_eq!(canonical.members.len(),2);
        assert!(canonical.source.contains("#[link_name = \"sqlite3_open_v2\"]"));
        assert!(canonical.source.contains("#[link_name = \"sqlite3_close\"]"));
        assert!(canonical.source.contains("6_i32"));
        assert!(canonical.source.contains("context: *const u8"));
        assert!(canonical.source.contains("6_i32, std::ptr::null()"));
        assert!(canonical.source.contains("Some((true, true))"));
        assert!(canonical.source.contains("Some((false, true))"));
        assert!(!canonical.source.contains("impl Drop"));
        let cost=measured.used();
        for prefix in [0,7] {
            let mut short=TypeWorkBudget::with_limit(prefix+cost-1); short.charge(prefix).unwrap();
            assert!(matches!(render(&image,&mut short),Err(LeafFailure::Resource)));
            let mut exact=TypeWorkBudget::with_limit(prefix+cost); exact.charge(prefix).unwrap();
            assert_eq!(render(&image,&mut exact).unwrap().source,canonical.source);
            assert_eq!(exact.used(),prefix+cost);
            assert!(matches!(render(&image,&mut exact),Err(LeafFailure::Resource)));
        }
        let root=render_admitted_root_shim(&image,&canonical,&mut TypeWorkBudget::default()).unwrap();
        assert!(root.contains("const CHECKED_ROLES: [[u32; 8]; 2]"));
        let mut donor=output_status_fixture();
        std::mem::swap(&mut image.bridges[canonical.members[1]].plan,&mut donor.bridges[canonical.members[1]].plan);
        assert!(matches!(render(&image,&mut TypeWorkBudget::default()),Err(LeafFailure::Association)));
    }

    #[test]
    fn root_role_data_binds_original_coordinates_and_paid_rendering() {
        let mut image = fixture();
        let leaf = render(&image, &mut TypeWorkBudget::default()).unwrap();
        let mut work = TypeWorkBudget::default();
        let source = render_admitted_root_shim(&image, &leaf, &mut work).unwrap();
        assert!(source.contains("const CHECKED_ROLES: [[u32; 8]; 4]"));
        let cost = work.used();
        assert!(render_admitted_root_shim(&image, &leaf, &mut TypeWorkBudget::with_limit(cost - 1)).is_err());
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(cost);
            assert_eq!(render_admitted_root_shim(&image, &leaf, &mut exact).unwrap(), source);
            assert_eq!(exact.used(), cost);
        }
        let index = leaf.members[0];
        image.bridges[index].operation_local ^= 1;
        assert_ne!(render_admitted_root_shim(&image, &leaf, &mut TypeWorkBudget::default()).unwrap(), source);
    }
    #[test]
    fn checked_leaf_uses_exact_four_original_abis_and_refuses_independent_donors() {
        let mut image = fixture();
        let mut measured = TypeWorkBudget::default();
        let canonical = render(&image, &mut measured).unwrap();
        assert_eq!(canonical.members.len(), 4);
        for name in [
            "ash_checked_owner_acquire",
            "ash_checked_owner_view",
            "ash_checked_owner_length",
            "ash_checked_owner_release",
        ] {
            assert!(
                canonical
                    .source
                    .contains(&format!("#[link_name = {name:?}]"))
            );
        }
        assert!(!canonical.source.contains("__ACQUIRE_NAME__"));
        assert!(!canonical.source.contains("ash::"));
        assert!(!canonical.source.contains("impl Drop for Owner"));
        let cost = measured.used();
        for prefix in [0, 13] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(
                render(&image, &mut short),
                Err(LeafFailure::Resource)
            ));
            assert!(matches!(
                render(&image, &mut short),
                Err(LeafFailure::Resource)
            ));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert_eq!(render(&image, &mut exact).unwrap().source, canonical.source);
                assert_eq!(exact.used(), prefix + cost);
            }
        }
        // An independently authenticated same-ABI donor has a different complete
        // original owner; keeping its spelling and target cannot substitute it.
        let mut donor = fixture();
        let release = canonical.members[3];
        std::mem::swap(
            &mut image.bridges[release].plan,
            &mut donor.bridges[release].plan,
        );
        assert!(matches!(
            render(&image, &mut TypeWorkBudget::default()),
            Err(LeafFailure::Association)
        ));
        std::mem::swap(
            &mut image.bridges[release].plan,
            &mut donor.bridges[release].plan,
        );
        assert_eq!(
            render(&image, &mut TypeWorkBudget::default())
                .unwrap()
                .source,
            canonical.source
        );
        image.bridges.pop();
        assert!(matches!(
            render(&image, &mut TypeWorkBudget::default()),
            Err(LeafFailure::Unsupported)
        ));
    }
    #[test]
    fn root_transport_moves_into_vacant_destination_with_exact_render_work() {
        let mut work = TypeWorkBudget::default();
        let source = render_root_shim(&mut work).unwrap();
        assert_eq!(source, ROOT_SHIM);
        assert!(source.contains("destination.owner = leaf::invoke_acquire(native); // FIRST root action"));
        assert!(source.contains("destination: &'cell mut OwnerCell"));
        let vacancy = source.find("if self.owner.is_some() { return Err(AcquirePreparationFailure::DestinationOccupied);").unwrap();
        let preparation = source.find("let native = leaf::prepare_acquire(capacity, initialized)").unwrap();
        assert!(vacancy < preparation);
        assert!(!source.contains("unsafe"));
        assert!(!source.contains("impl Drop"));
        let required = work.used();
        assert_eq!(required, ROOT_SHIM.len() * 2);
        let mut short = TypeWorkBudget::with_limit(required - 1);
        assert!(matches!(render_root_shim(&mut short), Err(LeafFailure::Resource)));
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(required);
            assert_eq!(render_root_shim(&mut exact).unwrap(), source);
            assert_eq!(exact.used(), required);
            assert!(matches!(render_root_shim(&mut exact), Err(LeafFailure::Resource)));
        }
    }

    #[test]
    fn leaf_link_name_escaping_is_paid_and_cannot_inject_rust_items() {
        let name = "a\"\\\n\u{2603}";
        let mut work = TypeWorkBudget::default();
        let value = quoted(name, &mut work).unwrap();
        assert_eq!(value, "\"a\\\"\\\\\\n\\u{2603}\"");
        let required = work.used();
        assert!(matches!(
            quoted(name, &mut TypeWorkBudget::with_limit(required - 1)),
            Err(LeafFailure::Resource)
        ));
        assert_eq!(
            quoted(name, &mut TypeWorkBudget::with_limit(required)).unwrap(),
            value
        );
    }
}
