//! Validation of untrusted private-image access declarations. These normalized
//! records have no checked nominal, selected call or live-window authority.

use super::*;

fn source_span(origin: &Origin, enclosing: Span) -> Result<Span, ForeignContractError> {
    let Origin::Source(span) = origin else {
        return Err(failure(ForeignContractReason::SourceSignature, enclosing));
    };
    if !private_span_within(enclosing, *span) {
        return Err(failure(ForeignContractReason::SourceSignature, *span));
    }
    Ok(*span)
}

fn tagged(argument: PreparedOwnerArgument, kind: &Kind) -> bool {
    matches!(
        (argument, kind),
        (PreparedOwnerArgument::Type(_), Kind::Type)
            | (PreparedOwnerArgument::EffectRow(_), Kind::EffectRow)
    )
}

pub(super) fn validate_accesses(
    parts: &PrivatePreparedLibraryParts,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignContractError> {
    for access in &parts.accesses {
        let span = source_span(access.origin(), parts.span)?;
        charge(work, access.parameters().len().saturating_add(4), span)?;
        let window = access
            .parameters()
            .get(access.window_parameter())
            .ok_or_else(|| failure(ForeignContractReason::InvalidParameters, span))?;
        if window.kind() != &Kind::Type
            || !private_span_within(span, access.window_span())
            || !private_span_within(span, access.extent_span())
            || !private_span_within(span, access.owner().span())
        {
            return Err(failure(ForeignContractReason::InvalidParameters, span));
        }
        for (index, parameter) in access.parameters().iter().enumerate() {
            source_span(parameter.origin(), span)?;
            if parameter.name().is_empty()
                || !matches!(parameter.kind(), Kind::Type | Kind::EffectRow)
            {
                return Err(failure(ForeignContractReason::InvalidParameters, span));
            }
            for previous in &access.parameters()[..index] {
                if names_equal(previous.name(), parameter.name(), span, work)? {
                    return Err(failure(ForeignContractReason::InvalidParameters, span));
                }
            }
        }
        let owner = parts
            .owners
            .get(access.owner().owner())
            .ok_or_else(|| failure(ForeignContractReason::UnknownMember, span))?;
        if owner.parameters.len() != access.owner().arguments().len() {
            return Err(failure(ForeignContractReason::InvalidParameters, span));
        }
        for (argument, expected) in access.owner().arguments().iter().zip(&owner.parameters) {
            charge(work, 1, span)?;
            let actual = access
                .parameters()
                .get(argument.parameter())
                .ok_or_else(|| failure(ForeignContractReason::InvalidParameters, span))?;
            let expected = match expected.kind {
                PrivatePreparedParameterKind::Type => &Kind::Type,
                PrivatePreparedParameterKind::EffectRow => &Kind::EffectRow,
            };
            if argument.parameter() == access.window_parameter()
                || !tagged(*argument, actual.kind())
                || !tagged(*argument, expected)
            {
                return Err(failure(ForeignContractReason::InvalidParameters, span));
            }
        }
        for (index, (member, written)) in access.preserving_members().iter().enumerate() {
            charge(work, parts.symbols.len().saturating_add(index), span)?;
            let symbol = parts
                .symbols
                .iter()
                .find(|symbol| symbol.member_index == *member)
                .ok_or_else(|| failure(ForeignContractReason::UnknownMember, *written))?;
            if !private_span_within(span, *written)
                || access.preserving_members()[..index]
                    .iter()
                    .any(|(previous, _)| previous == member)
                || matches!(symbol.call, PrivatePreparedCall::Owner(ref call) if !matches!(call, PreparedOwnerCall::Borrow { .. }))
            {
                return Err(failure(ForeignContractReason::OperandRole, *written));
            }
        }
    }
    Ok(())
}

pub(super) fn validate_result(
    parts: &PrivatePreparedLibraryParts,
    symbol: &PrivatePreparedSymbolParts,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignContractError> {
    let Some(result) = &symbol.access_result else {
        return Ok(());
    };
    let span = result.span();
    let app = result.application();
    let access = parts
        .accesses
        .get(app.family())
        .ok_or_else(|| failure(ForeignContractReason::UnknownMember, span))?;
    let PrivatePreparedCall::Owner(PreparedOwnerCall::Borrow {
        application: owner, ..
    }) = &symbol.call
    else {
        return Err(failure(ForeignContractReason::OutputRole, span));
    };
    charge(
        work,
        app.arguments()
            .len()
            .saturating_add(access.preserving_members().len())
            .saturating_add(4),
        span,
    )?;
    if !private_span_within(symbol.span, span)
        || !private_span_within(symbol.span, app.span())
        || app.arguments().len() != access.parameters().len()
        || !access
            .preserving_members()
            .iter()
            .any(|(member, _)| *member == symbol.member_index)
        || owner.owner() != access.owner().owner()
        || owner.arguments().len() != access.owner().arguments().len()
    {
        return Err(failure(ForeignContractReason::OutputRole, span));
    }
    for (argument, expected) in app.arguments().iter().zip(access.parameters()) {
        let parameter = symbol
            .parameters
            .get(argument.parameter())
            .ok_or_else(|| failure(ForeignContractReason::InvalidParameters, span))?;
        let kind = match parameter.kind {
            PrivatePreparedParameterKind::Type => &Kind::Type,
            PrivatePreparedParameterKind::EffectRow => &Kind::EffectRow,
        };
        if !tagged(*argument, kind) || !tagged(*argument, expected.kind()) {
            return Err(failure(ForeignContractReason::InvalidParameters, span));
        }
    }
    for (actual, projected) in owner.arguments().iter().zip(access.owner().arguments()) {
        charge(work, 1, span)?;
        if app.arguments().get(projected.parameter()) != Some(actual) {
            return Err(failure(ForeignContractReason::OutputRole, span));
        }
    }
    let keys = match result {
        PreparedAccessResult::View { keys, .. } => {
            if symbol.result != PreparedAbiResult::Address(PreparedAddressRepresentation::Bytes) {
                return Err(failure(ForeignContractReason::OutputRole, span));
            }
            keys
        }
        PreparedAccessResult::Extent { view, keys, .. } => {
            charge(work, view.len().saturating_add(1), span)?;
            if view.is_empty()
                || access.extent() != PreparedForeignExtent::Bytes
                || !matches!(symbol.result, PreparedAbiResult::Scalar(_))
            {
                return Err(failure(ForeignContractReason::OutputRole, span));
            }
            keys
        }
    };
    for path in keys {
        charge(work, path.len().saturating_add(1), span)?;
        if path.is_empty() {
            return Err(failure(ForeignContractReason::SourcePosition, span));
        }
    }
    Ok(())
}

pub(super) fn same_result(
    left: Option<&PreparedAccessResult>,
    right: Option<&PreparedAccessResult>,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignContractError> {
    charge(work, 1, span)?;
    let (Some(left), Some(right)) = (left, right) else {
        return Ok(left.is_none() && right.is_none());
    };
    let (left_keys, right_keys) = match (left, right) {
        (
            PreparedAccessResult::View { keys: a, .. },
            PreparedAccessResult::View { keys: b, .. },
        ) => (a, b),
        (
            PreparedAccessResult::Extent {
                view: a, keys: ak, ..
            },
            PreparedAccessResult::Extent {
                view: b, keys: bk, ..
            },
        ) => {
            charge(work, a.len().saturating_add(b.len()), span)?;
            if a != b {
                return Ok(false);
            }
            (ak, bk)
        }
        _ => return Ok(false),
    };
    let a = left.application();
    let b = right.application();
    charge(
        work,
        a.arguments()
            .len()
            .saturating_add(b.arguments().len())
            .saturating_add(left_keys.len()),
        span,
    )?;
    if left.span() != right.span()
        || a.family() != b.family()
        || a.span() != b.span()
        || a.arguments() != b.arguments()
        || left_keys.len() != right_keys.len()
    {
        return Ok(false);
    }
    for (a, b) in left_keys.iter().zip(right_keys) {
        charge(work, a.len().saturating_add(b.len()), span)?;
        if a != b {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn same_accesses(
    left: &[PreparedForeignAccess],
    right: &[PreparedForeignAccess],
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignContractError> {
    charge(work, left.len().saturating_add(1), span)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (a, b) in left.iter().zip(right) {
        let bspan = source_span(b.origin(), span)?;
        charge(
            work,
            a.owner()
                .arguments()
                .len()
                .saturating_add(a.preserving_members().len())
                .saturating_add(8),
            bspan,
        )?;
        if a.member_index() != b.member_index()
            || !names_equal(a.name(), b.name(), bspan, work)?
            || !private_same_source_origin(a.origin(), bspan, work)?
            || a.window_parameter() != b.window_parameter()
            || a.window_span() != b.window_span()
            || a.extent() != b.extent()
            || a.extent_span() != b.extent_span()
            || a.owner().owner() != b.owner().owner()
            || a.owner().span() != b.owner().span()
            || a.owner().arguments() != b.owner().arguments()
            || a.preserving_members() != b.preserving_members()
            || a.parameters().len() != b.parameters().len()
        {
            return Ok(false);
        }
        for (a, b) in a.parameters().iter().zip(b.parameters()) {
            let bspan = source_span(b.origin(), span)?;
            if !crate::types::same_kind_with_budget(a.kind(), b.kind(), work)
                .map_err(|()| failure(ForeignContractReason::WorkExhausted, bspan))?
                || !names_equal(a.name(), b.name(), bspan, work)?
                || !private_same_source_origin(a.origin(), bspan, work)?
            {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::super::owner_normalization_tests::{parts, source};
    use super::*;

    #[test]
    fn access_image_parts_keep_all_roles_and_refuse_changed_coordinates_at_exact_work() {
        let (module, surface) = source(&super::super::access_contract::tests::view_source());
        let original = prepare_foreign_library(module, &surface.foreign_libraries[0]).unwrap();
        let mut measured = TypeWorkBudget::unbounded();
        restore_prepared_library(parts(&original), &mut measured).unwrap();
        let needed = measured.used();
        for prefix in [0, 17] {
            let mut short = TypeWorkBudget::with_limit(prefix + needed - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                restore_prepared_library(parts(&original), &mut short)
                    .unwrap_err()
                    .reason(),
                ForeignContractReason::WorkExhausted
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + needed);
                exact.charge(prefix).unwrap();
                let restored = restore_prepared_library(parts(&original), &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + needed);
                assert!(
                    same_prepared_library_parts(
                        &restored,
                        &parts(&original),
                        &mut TypeWorkBudget::unbounded()
                    )
                    .unwrap()
                );
            }
        }
        for mutate in 0..7 {
            let mut changed = parts(&original);
            match mutate {
                0 => changed.accesses[0].window_parameter = 1,
                1 => changed.accesses[0].owner.owner = 7,
                2 => changed.accesses[0].member_index = changed.symbols[0].member_index,
                3 => {
                    changed.accesses[0].preserving_members[0].0 =
                        changed.symbols.last().unwrap().member_index
                }
                4 => {
                    let result = changed
                        .symbols
                        .iter_mut()
                        .find_map(|symbol| symbol.access_result.as_mut())
                        .unwrap();
                    match result {
                        PreparedAccessResult::View { application, .. }
                        | PreparedAccessResult::Extent { application, .. } => {
                            application.family = 9
                        }
                    }
                }
                5 => {
                    let result = changed
                        .symbols
                        .iter_mut()
                        .find_map(|symbol| symbol.access_result.as_mut())
                        .unwrap();
                    match result {
                        PreparedAccessResult::View { application, .. }
                        | PreparedAccessResult::Extent { application, .. } => {
                            application.arguments[0] = PreparedOwnerArgument::EffectRow(0)
                        }
                    }
                }
                _ => changed.accesses[0].extent = PreparedForeignExtent::Nul,
            }
            assert!(
                !same_prepared_library_parts(&original, &changed, &mut TypeWorkBudget::unbounded())
                    .unwrap()
            );
            assert!(
                restore_prepared_library(changed, &mut TypeWorkBudget::unbounded()).is_err(),
                "mutation={mutate}"
            );
        }
        let mut changed = parts(&original);
        let Some(PreparedAccessResult::Extent { keys, view, .. }) = changed
            .symbols
            .iter_mut()
            .find_map(|symbol| match symbol.access_result.as_mut() {
                Some(result @ PreparedAccessResult::Extent { .. }) => Some(result),
                _ => None,
            })
        else {
            panic!("extent result");
        };
        keys[0][0] = 0;
        view[0] = 1;
        assert!(
            !same_prepared_library_parts(&original, &changed, &mut TypeWorkBudget::unbounded())
                .unwrap()
        );
        // Structurally valid alternate paths still require exact original fact
        // comparison and independent source-signature binding, not this decoder.
    }
}
