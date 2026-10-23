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
    pub members: [usize; 4],
}
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
    Ok(LeafEmission { source, members })
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
        assert!(source.contains("self.owner = returned; // FIRST root action"));
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
