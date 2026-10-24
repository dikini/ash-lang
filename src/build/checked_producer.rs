//! Private checked producer preparation. These bytes and finite capacities are
//! unaccepted producer data, never protected policy or executable authority.
#![allow(
    dead_code,
    reason = "TASK0053 checked producer has no public activation path"
)]

use super::checked_receipt::{ArtifactPin, ReceiptFailure};
use crate::{
    core::{
        EffectExprKind, EffectOperation, PureComputation, PureExprKind, ValidatedEffectProgram,
    },
    foreign::{
        scalar_preflight::ForeignScalarPreflightRole as Role, source_runtime::CheckedOwnerLimits,
    },
    types::TypeWorkBudget,
};

fn pay(work: &mut TypeWorkBudget, n: usize) -> Result<(), ReceiptFailure> {
    work.charge(n).map_err(|()| ReceiptFailure::Resource)
}

/// A complete paid census of the supported single dependency-free owner path.
/// The validated image still carries every original, argument, row and mapping;
/// these counts do not replace independent Core/image admission.
pub(super) fn observation_minimum(
    program: &ValidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> Result<(usize, usize), ReceiptFailure> {
    let scopes = admitted_scopes(program, work)?;
    let mut total = 0usize;
    for (_, scope) in &scopes {
        let mut supported = true;
        let mut copies = 0usize;
        let mut exhausted = false;
        scope
            .visit_byte_calls(
                |call, work| {
                    if work.charge(2).is_err() {
                        exhausted = true;
                        return Ok(());
                    }
                    if call.apply.is_some() {
                        match program
                            .registry()
                            .scalar_preflight(call.function)
                            .map(|fact| fact.role())
                        {
                            Some(Role::CheckedCopyBytes) => match copies.checked_add(1) {
                                Some(n) => copies = n,
                                None => exhausted = true,
                            },
                            Some(
                                Role::CheckedByteRead
                                | Role::CheckedByteWrite
                                | Role::CheckedCopyNul,
                            ) => supported = false,
                            _ => {}
                        }
                    }
                    Ok(())
                },
                work,
            )
            .map_err(core_failure)?;
        let mut windows = 0usize;
        scope
            .visit_window_calls(
                |_, _, symbol, work| {
                    if work.charge(3).is_err() {
                        exhausted = true;
                        return Ok(());
                    }
                    if !symbol
                        .owner()
                        .is_some_and(|owner| std::sync::Arc::ptr_eq(owner, &scope.header().owner))
                        || !matches!(
                            symbol.owner_role(),
                            Some(crate::foreign::source_contract::PreparedOwnerCall::Borrow { .. })
                        )
                    {
                        supported = false;
                    }
                    match windows.checked_add(1) {
                        Some(n) => windows = n,
                        None => exhausted = true,
                    }
                    Ok(())
                },
                work,
            )
            .map_err(core_failure)?;
        if exhausted {
            return Err(ReceiptFailure::Resource);
        }
        let independent_output = matches!(scope.header().acquire.owner_role(),
            Some(crate::foreign::source_contract::PreparedOwnerCall::OutputAcquire { .. }))
            && matches!(scope.header().teardown.owner_role(),
                Some(crate::foreign::source_contract::PreparedOwnerCall::StatusTeardown { .. }));
        if !supported || (copies == 0 && !independent_output) || (independent_output && (copies != 0 || windows != 0)) {
            return Err(ReceiptFailure::Association);
        }
        let minimum = scope
            .native_interpretations()
            .len()
            .max(2)
            .checked_add(windows)
            .and_then(|n| n.checked_add(copies))
            .ok_or(ReceiptFailure::Resource)?;
        total = total.checked_add(minimum).ok_or(ReceiptFailure::Resource)?;
    }
    pay(work, scopes.len())?;
    let mut references = Vec::new(); references.try_reserve_exact(scopes.len()).map_err(|_|ReceiptFailure::Resource)?;
    references.extend(scopes.iter().map(|(_, scope)|*scope));
    complete_association(program, &references, work)?;
    Ok((scopes[0].0, total))
}

/// Reconstruct the supported scope census from exact Core originals. Profile tags
/// do not authorize a scope; the bound image must prove this relation itself.
pub(super) fn admitted_scopes<'a>(program: &'a ValidatedEffectProgram, work: &mut TypeWorkBudget)
    -> Result<Vec<(usize, &'a crate::core::source_resource::SourceResourceScopeNode)>, ReceiptFailure> {
    use crate::{foreign::checked_source, types::{KindedArgument, Type}};
    pay(work, program.node_count().checked_add(2).ok_or(ReceiptFailure::Resource)?)?;
    let mut scopes = Vec::new(); scopes.try_reserve_exact(2).map_err(|_|ReceiptFailure::Resource)?;
    for (slot, node) in program.nodes().iter().enumerate() {
        if let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) = &node.kind {
            if scopes.len() == 2 || scope.header().original.host.is_none() { return Err(ReceiptFailure::Association); }
            scopes.push((slot, scope.as_ref()));
        }
    }
    if scopes.is_empty() { return Err(ReceiptFailure::Association); }
    if scopes.len() == 1 {
        if !scopes[0].1.header().dependencies.is_empty() { return Err(ReceiptFailure::Association); }
        return Ok(scopes);
    }
    if !scopes[0].1.header().dependencies.is_empty() { scopes.swap(0,1); }
    let (parent, child) = (scopes[0].1, scopes[1].1);
    let (p, c) = (parent.header(), child.header());
    pay(work, 32)?;
    if !p.dependencies.is_empty() || c.dependencies.len() != 1
        || !checked_source::independent_output_acquire(p.acquire.symbol())
        || !checked_source::independent_status_teardown(p.teardown.symbol())
        || !checked_source::dependent_output_acquire(c.owner.prepared(), c.acquire.symbol())
        || !checked_source::dependent_status_teardown(c.owner.prepared(), c.teardown.symbol())
        || !std::sync::Arc::ptr_eq(p.owner.prepared(), c.owner.prepared())
        || std::sync::Arc::ptr_eq(&p.owner, &c.owner) { return Err(ReceiptFailure::Association); }
    let retained = c.original.parameters.iter().position(|parameter|parameter.id == c.dependencies[0]).ok_or(ReceiptFailure::Association)?;
    // Only original Type formal positions select H and the retained owned C.
    for (left, right) in [
        (parent.arguments().get(p.original.host.ok_or(ReceiptFailure::Association)?.position), child.arguments().get(c.original.host.ok_or(ReceiptFailure::Association)?.position)),
        (parent.arguments().get(p.original.owned_position), child.arguments().get(retained)),
    ] {
        let (Some(KindedArgument::TypeArg(left @ Type::Variable(_))), Some(KindedArgument::TypeArg(right @ Type::Variable(_)))) = (left,right)
            else { return Err(ReceiptFailure::Association); };
        if !crate::types::same_type_with_budget(left,right,work).map_err(|()|ReceiptFailure::Resource)? {
            return Err(ReceiptFailure::Association);
        }
    }
    Ok(scopes)
}

fn complete_association(
    program: &ValidatedEffectProgram,
    scopes: &[&crate::core::source_resource::SourceResourceScopeNode],
    work: &mut TypeWorkBudget,
) -> Result<(), ReceiptFailure> {
    use crate::core::source_resource::SourceResourcePhase as Phase;
    use crate::types::{KindedArgument, Type};
    use std::collections::HashSet;
    let scope = scopes.first().ok_or(ReceiptFailure::Association)?;
    let host = scope
        .header()
        .original
        .host
        .ok_or(ReceiptFailure::Association)?;
    let Some(KindedArgument::TypeArg(Type::Variable(host_identity))) =
        scope.arguments().get(host.position)
    else {
        return Err(ReceiptFailure::Association);
    };
    let mut requests = HashSet::new();
    let mut windows = HashSet::new();
    let mut primitives = HashSet::new();
    let mut failed = None;
    for scope in scopes {
    let mut insert = |set: &mut HashSet<usize>, id, work: &mut TypeWorkBudget| {
        if work.charge(3).is_err() {
            failed = Some(ReceiptFailure::Resource);
            return;
        }
        let Some(index) = node_index(program, id) else {
            failed = Some(ReceiptFailure::Association);
            return;
        };
        if set.try_reserve(1).is_err() {
            failed = Some(ReceiptFailure::Resource);
            return;
        }
        set.insert(index);
    };

    scope
        .visit_windows(
            |id, work| {
                insert(&mut windows, id, work);
                Ok(())
            },
            work,
        )
        .map_err(core_failure)?;
    scope
        .visit_window_calls(
            |request, _, _, work| {
                insert(&mut requests, request, work);
                Ok(())
            },
            work,
        )
        .map_err(core_failure)?;
    scope
        .visit_byte_calls(
            |call, work| {
                insert(&mut primitives, call.application, work);
                Ok(())
            },
            work,
        )
        .map_err(core_failure)?;
    if let Some(error) = failed {
        return Err(error);
    }
    for (index, claim) in scope.copy_claims().iter().enumerate() {
        let phase = [Phase::Acquire, Phase::Finish, Phase::Handler][index];
        pay(work, claim.nodes.len())?;
        for (_, id) in claim.nodes {
            let Some(node) = program.node(*id) else {
                return Err(ReceiptFailure::Association);
            };
            let EffectExprKind::Operation(EffectOperation::Request(call)) = &node.kind else {
                continue;
            };
            pay(work, 1)?;
            if !program
                .registry()
                .native_symbol(call.operation())
                .is_some_and(|symbol| symbol.prepared().checked_contract().is_some())
            {
                continue;
            }
            if scope
                .contains_phase_request(&program.shared(), *id, phase, work)
                .map_err(core_failure)?
            {
                pay(work, 3)?;
                requests
                    .try_reserve(1)
                    .map_err(|_| ReceiptFailure::Resource)?;
                requests.insert(node_index(program, *id).ok_or(ReceiptFailure::Association)?);
            }
        }
    }
    }
    let mut hosts = 0usize;
    pay(work, program.node_count())?;
    for (index, node) in program.nodes().iter().enumerate() {
        match &node.kind {
            EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) => {
                if let Some(actual) = boundary.host() {
                    hosts = hosts.checked_add(1).ok_or(ReceiptFailure::Resource)?;
                    if hosts != 1
                        || actual.identity() != *host_identity
                        || !boundary.interpretations().is_empty()
                    {
                        return Err(ReceiptFailure::Association);
                    }
                } else if !boundary.interpretations().is_empty() {
                    return Err(ReceiptFailure::Association);
                }
            }
            EffectExprKind::Operation(EffectOperation::Request(call)) => {
                pay(work, 2)?;
                if program
                    .registry()
                    .native_symbol(call.operation())
                    .is_some_and(|symbol| symbol.prepared().checked_contract().is_some())
                    && !requests.contains(&index)
                {
                    return Err(ReceiptFailure::Association);
                }
            }
            EffectExprKind::Operation(EffectOperation::SourceCopyWindow(_)) => {
                pay(work, 1)?;
                if !windows.contains(&index) {
                    return Err(ReceiptFailure::Association);
                }
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                application,
            ))) => {
                pay(work, 2)?;
                if let Some(EffectExprKind::Pure(PureExprKind::Variable(function))) =
                    program.node(application.function()).map(|node| &node.kind)
                    && matches!(
                        program
                            .registry()
                            .scalar_preflight(function.binder())
                            .map(|fact| fact.role()),
                        Some(
                            Role::CheckedByteRead
                                | Role::CheckedByteWrite
                                | Role::CheckedCopyBytes
                                | Role::CheckedCopyNul
                        )
                    )
                    && !primitives.contains(&index)
                {
                    return Err(ReceiptFailure::Association);
                }
            }
            _ => {}
        }
    }
    if hosts != 1 {
        return Err(ReceiptFailure::Association);
    }
    Ok(())
}

// Validate the complete arena-bearing handle before using its numeric image
// position. A donor arena with the same local number is never a match.
fn node_index(program: &ValidatedEffectProgram, id: crate::core::NodeId) -> Option<usize> {
    program.node(id)?;
    usize::try_from(id.value()).ok()
}

fn core_failure(error: crate::core::ValidationError) -> ReceiptFailure {
    if error.reason() == crate::core::ValidationReason::Resource {
        ReceiptFailure::Resource
    } else {
        ReceiptFailure::Association
    }
}

/// Fixed-endian policy DATA bound to the complete actual image/facts. The six
/// limits apply per prepared boundary; repetition is still dynamically metered
/// and may refuse. They cannot supply any missing protected approval/context.
pub(super) fn policy_bytes(
    program: &ValidatedEffectProgram,
    image: ArtifactPin,
    facts: ArtifactPin,
    limits: CheckedOwnerLimits,
    work: &mut TypeWorkBudget,
) -> Result<Vec<u8>, ReceiptFailure> {
    let (_, minimum) = observation_minimum(program, work)?;
    pay(work, 8)?;
    if limits.groups != 1
        || limits.owners != 1
        || limits.pending < 1
        || limits.continuations < 1
        || limits.observations < minimum
        || limits.history
            < limits
                .observations
                .checked_add(1)
                .ok_or(ReceiptFailure::Resource)?
    {
        return Err(ReceiptFailure::Resource);
    }
    const SIZE: usize = 8 + 4 + 2 * 40 + 8 * 8;
    pay(work, SIZE * 2)?;
    let mut out = Vec::new();
    out.try_reserve_exact(SIZE)
        .map_err(|_| ReceiptFailure::Resource)?;
    out.extend_from_slice(b"ASHPOL01");
    out.extend_from_slice(&1u32.to_le_bytes());
    for pin in [image, facts] {
        out.extend_from_slice(&pin.bytes.to_le_bytes());
        out.extend_from_slice(&pin.sha256);
    }
    // Ordinal zero retains its original meaning: the primary admitted scope.
    // The dependent profile derives its second scope from the bound Core image.
    for n in [
        0,
        minimum,
        limits.groups,
        limits.owners,
        limits.pending,
        limits.observations,
        limits.history,
        limits.continuations,
    ] {
        out.extend_from_slice(
            &u64::try_from(n)
                .map_err(|_| ReceiptFailure::Resource)?
                .to_le_bytes(),
        );
    }
    Ok(out)
}

/// Independent bounded decoding of policy data. This returns capacities only;
/// no execution/approval constructor accepts this value as authority.
pub(super) fn decode_policy(
    bytes: &[u8],
    image: ArtifactPin,
    facts: ArtifactPin,
    work: &mut TypeWorkBudget,
) -> Result<CheckedOwnerLimits, ReceiptFailure> {
    const SIZE: usize = 8 + 4 + 2 * 40 + 8 * 8;
    pay(
        work,
        bytes
            .len()
            .checked_add(12)
            .ok_or(ReceiptFailure::Resource)?,
    )?;
    if bytes.len() != SIZE || &bytes[..8] != b"ASHPOL01" || bytes[8..12] != 1u32.to_le_bytes() {
        return Err(ReceiptFailure::Malformed);
    }
    for (at, expected) in [(12, image), (52, facts)] {
        let size = u64::from_le_bytes(
            bytes[at..at + 8]
                .try_into()
                .map_err(|_| ReceiptFailure::Malformed)?,
        );
        if size != expected.bytes || bytes[at + 8..at + 40] != expected.sha256 {
            return Err(ReceiptFailure::Association);
        }
    }
    let mut numbers = [0usize; 8];
    for (i, n) in numbers.iter_mut().enumerate() {
        *n = usize::try_from(u64::from_le_bytes(
            bytes[92 + i * 8..100 + i * 8]
                .try_into()
                .map_err(|_| ReceiptFailure::Malformed)?,
        ))
        .map_err(|_| ReceiptFailure::Resource)?;
    }
    let limits = CheckedOwnerLimits {
        groups: numbers[2],
        owners: numbers[3],
        pending: numbers[4],
        observations: numbers[5],
        history: numbers[6],
        continuations: numbers[7],
    };
    if numbers[0] != 0
        || limits.groups != 1
        || limits.owners != 1
        || limits.pending < 1
        || limits.continuations < 1
        || numbers[1] < 2
        || limits.observations < numbers[1]
        || limits.history
            < limits
                .observations
                .checked_add(1)
                .ok_or(ReceiptFailure::Resource)?
    {
        return Err(ReceiptFailure::Resource);
    }
    Ok(limits)
}

#[cfg(test)]
mod tests {
    use super::*;
    type ProgramAndSources = (
        ValidatedEffectProgram,
        Vec<(
            crate::module::ModuleId,
            std::sync::Arc<crate::source::SourceFile>,
        )>,
    );
    pub(super) fn genuine() -> ProgramAndSources {
        crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
        )
    }
    #[test]
    fn checked_producer_genuine_initialized_eight_byte_emission_is_not_activation() {
        let (program, provenance) = genuine();
        assert!(matches!(
            super::super::image::encode_effect_for_build(
                &program,
                &provenance,
                super::super::host::NATIVE_TARGET,
                &mut TypeWorkBudget::default()
            ),
            Err(super::super::image::NativeImageFailure::Image(
                super::super::image::ImageFailure::Unsupported(
                    super::super::image::Unsupported::EffectOperation
                )
            ))
        ));
        let mut work = super::super::gas::preparation(&provenance, program.node_count()).unwrap();
        let build = super::super::image::encode_checked_preparation(
            &program,
            &provenance,
            super::super::host::NATIVE_TARGET,
            &mut work,
        )
        .unwrap();
        assert_eq!(build.bridges.len(), 4);
        let emission = super::super::emit::checked_native_host(
            &build,
            &program,
            policy(&program),
            &super::super::runtime_fingerprint(),
            &mut work,
        )
        .unwrap();
        assert!(!emission.payloads.bytes().0.is_empty());
        assert!(!emission.payloads.bytes().1.is_empty());
        assert!(emission.payloads.checked_policy().is_some());
        assert!(emission.rust_source.contains("__run_private_effect_image"));
        assert!(emission.rust_source.contains("std::hint::black_box"));
        assert_eq!(
            observation_minimum(&program, &mut TypeWorkBudget::default())
                .unwrap()
                .1,
            5
        );
    }
    fn policy(program: &ValidatedEffectProgram) -> CheckedOwnerLimits {
        let minimum = observation_minimum(program, &mut TypeWorkBudget::default())
            .unwrap()
            .1;
        CheckedOwnerLimits {
            groups: 1,
            owners: 1,
            pending: 1,
            observations: minimum,
            history: minimum + 1,
            continuations: 1,
        }
    }
    fn receipt_limits() -> super::super::checked_receipt::ProducerReceiptLimits {
        super::super::checked_receipt::ProducerReceiptLimits {
            artifact_bytes: 128 * 1024 * 1024,
            receipt_bytes: 4096,
            records: 16,
            work: 512 * 1024 * 1024,
        }
    }
    fn emitted(
        program: &ValidatedEffectProgram,
        sources: &[(
            crate::module::ModuleId,
            std::sync::Arc<crate::source::SourceFile>,
        )],
    ) -> (
        super::super::image::NativeBuildImage,
        super::super::emit::NativeHostEmission,
    ) {
        let mut work = super::super::gas::preparation(sources, program.node_count()).unwrap();
        let build = super::super::image::encode_checked_preparation(
            program,
            sources,
            super::super::host::NATIVE_TARGET,
            &mut work,
        )
        .unwrap();
        let emission = super::super::emit::checked_native_host(
            &build,
            program,
            policy(program),
            &super::super::runtime_fingerprint(),
            &mut work,
        )
        .unwrap();
        (build, emission)
    }
    fn seed(
        program: &ValidatedEffectProgram,
        sources: &[(
            crate::module::ModuleId,
            std::sync::Arc<crate::source::SourceFile>,
        )],
        build: &super::super::image::NativeBuildImage,
        emission: &super::super::emit::NativeHostEmission,
    ) -> Result<super::super::checked_receipt::ReceiptSeed, ReceiptFailure> {
        super::super::checked_receipt::ReceiptSeed::from_checked_emission(
            build,
            program,
            sources,
            emission,
            super::super::host::NATIVE_TARGET.as_bytes(),
            receipt_limits(),
            policy(program),
        )
    }
    #[test]
    fn dependent_two_scope_policy_and_image_substitution_refusals() {
        let source = include_str!("../../libraries/sqlite_checked.ash");
        let entry = include_str!("../../tests/fixtures/checked-sqlite/dependent-physical-entry.ash");
        let (program, sources) = crate::elaborate::checked_owner_passive_program_for_source(source, entry);
        let scopes = admitted_scopes(&program, &mut TypeWorkBudget::default()).unwrap();
        assert_eq!(scopes.len(), 2);
        assert!(scopes[0].1.header().dependencies.is_empty());
        assert_eq!(scopes[1].1.header().dependencies.len(), 1);
        let (build, mut emission) = emitted(&program, &sources);
        let canonical = seed(&program, &sources, &build, &emission).unwrap();
        assert_eq!(policy(&program).groups, 1);
        assert_eq!(policy(&program).owners, 1, "capacity remains local to each boundary");
        canonical.receipt().matches_checked_policy(emission.payloads.checked_policy().unwrap(), receipt_limits()).unwrap();
        let (image, facts) = emission.payloads.bytes();
        let mut work = TypeWorkBudget::with_limit(receipt_limits().work);
        let image = super::super::checked_receipt::pin(image, &mut work).unwrap();
        let facts = super::super::checked_receipt::pin(facts, &mut work).unwrap();
        let bytes = emission.payloads.checked_policy().unwrap();
        let decoded = decode_policy(bytes, image, facts, &mut work).unwrap();
        let expected = policy(&program);
        assert_eq!((decoded.groups, decoded.owners, decoded.pending, decoded.observations, decoded.history, decoded.continuations),
            (expected.groups, expected.owners, expected.pending, expected.observations, expected.history, expected.continuations));
        for (offset, value) in [(8, 2), (92, 1), (108, 2), (116, 2)] {
            let mut changed = bytes.to_vec();
            changed[offset] = value;
            assert!(decode_policy(&changed, image, facts, &mut work).is_err(),
                "mixed version/ordinal/aggregate-capacity interpretation at byte {offset}");
        }
        emission.payloads.test_change_policy();
        assert!(matches!(seed(&program, &sources, &build, &emission), Err(ReceiptFailure::Association)));
        emission.payloads.test_change_policy();
        emission.payloads.test_change_image();
        assert!(matches!(seed(&program, &sources, &build, &emission), Err(ReceiptFailure::Association)));
        emission.payloads.test_change_image();
        seed(&program, &sources, &build, &emission).unwrap();
        // A second genuine graph is not a donor for this image/policy, even
        // when both have the exact two-scope owner census.
        let donor_source = source.replace("name \"sqlite3_prepare_v2\"", "name \"donor_prepare\"");
        assert_ne!(donor_source, source);
        let (donor, donor_sources) = crate::elaborate::checked_owner_passive_program_for_source(&donor_source, entry);
        let (donor_build, donor_emission) = emitted(&donor, &donor_sources);
        seed(&donor, &donor_sources, &donor_build, &donor_emission).unwrap();
        assert!(matches!(seed(&program, &sources, &build, &donor_emission), Err(ReceiptFailure::Association)));
        // Adding a third real source scope cannot widen this private profile.
        let extra_entry = entry.replace("SQLite.prepared_status statement",
            "resource SQLite.Connection<H, D> extra = \":memory:\" {\n SQLite.prepared_status statement\n }")
            .replace("Foreign.CheckedScope<Foreign.CheckedScope<Int, SQLite.PrepareError, SQLite.FinalizeError>",
                "Foreign.CheckedScope<Foreign.CheckedScope<Foreign.CheckedScope<Int, SQLite.InitError, SQLite.CloseError>, SQLite.PrepareError, SQLite.FinalizeError>");
        let (extra, _) = crate::elaborate::checked_owner_passive_program_for_source(source, &extra_entry);
        assert!(matches!(admitted_scopes(&extra, &mut TypeWorkBudget::default()), Err(ReceiptFailure::Association)));
    }
    #[test]
    fn checked_producer_complete_host_and_unsupported_role_census() {
        let (program, sources) = genuine();
        emitted(&program, &sources);
        let text = include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash")
            .replace(
                "run () = handle (foreign host H {",
                "run () = handle (foreign host Extra {\n    foreign host H {",
            )
            .replace("}) with Trace", "}\n}) with Trace");
        let (extra, _) = crate::elaborate::checked_owner_passive_program_for_source(
            &text,
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
        );
        assert_eq!(
            observation_minimum(&extra, &mut TypeWorkBudget::default()),
            Err(ReceiptFailure::Association)
        );
        let (wider, _) = crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../tests/fixtures/checked-byte-windows/owner.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<(Foreign.CheckedCall<Int>, Foreign.CheckedCall<Unit>, Producer.CopyProbe, Producer.CopyProbe), Unit, Unit>\nmain () = Producer.run ()\n",
        );
        assert_eq!(
            observation_minimum(&wider, &mut TypeWorkBudget::default()),
            Err(ReceiptFailure::Association)
        );
    }
    #[test]
    fn checked_producer_receipt_policy_and_independent_substitution_refusals() {
        use super::super::checked_receipt::{ProducerReceipt, ProducerRole, ReceiptField};
        let (program, sources) = genuine();
        let (build, mut emission) = emitted(&program, &sources);
        let good = seed(&program, &sources, &build, &emission).unwrap();
        let bytes = good
            .receipt()
            .encode(
                &mut TypeWorkBudget::with_limit(receipt_limits().work),
                receipt_limits(),
            )
            .unwrap();
        let decoded = ProducerReceipt::decode(&bytes, receipt_limits()).unwrap();
        assert_eq!(decoded.role(), ProducerRole::CheckedPreparation);
        decoded
            .matches_expected(good.receipt(), receipt_limits())
            .unwrap();
        decoded
            .matches_checked_policy(
                emission.payloads.checked_policy().unwrap(),
                receipt_limits(),
            )
            .unwrap();
        assert!(decoded.pin(ReceiptField::CheckedContracts).is_some());
        for field in [
            ReceiptField::NativeClosure,
            ReceiptField::RuntimeClosure,
            ReceiptField::HeaderClosure,
            ReceiptField::ToolClosure,
            ReceiptField::Premises,
            ReceiptField::Context,
        ] {
            assert_eq!(decoded.pin(field), None);
        }
        assert_eq!(
            decoded.check_checked_applicability(),
            Err(ReceiptFailure::IncompleteClosure)
        );
        assert_eq!(
            decoded.activate(),
            Err(ReceiptFailure::ProtectedAuthorityUnavailable)
        );
        let mut self_claimed = bytes.clone();
        let start = 54 + super::super::host::NATIVE_TARGET.len();
        for record in self_claimed[start..].chunks_exact_mut(42) {
            if record[1] == 0 {
                record[1] = 1;
                record[2..10].copy_from_slice(&32u64.to_le_bytes());
                record[10..42].fill(7);
            }
        }
        let self_claimed = ProducerReceipt::decode(&self_claimed, receipt_limits()).unwrap();
        self_claimed
            .matches_expected(&self_claimed, receipt_limits())
            .unwrap();
        assert_eq!(
            self_claimed.check_checked_applicability(),
            Err(ReceiptFailure::IncompleteClosure)
        );
        assert_eq!(
            self_claimed.activate(),
            Err(ReceiptFailure::ProtectedAuthorityUnavailable)
        );

        let mut role = bytes.clone();
        role[12] = 255;
        assert!(ProducerReceipt::decode(&role, receipt_limits()).is_err());
        let start = 54 + super::super::host::NATIVE_TARGET.len();
        for offset in [start, start + 42] {
            let mut malformed = bytes.clone();
            malformed[offset] = if offset == start { 255 } else { 0 };
            assert!(ProducerReceipt::decode(&malformed, receipt_limits()).is_err());
        }
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(ProducerReceipt::decode(&trailing, receipt_limits()).is_err());
        let mut too_short = receipt_limits();
        too_short.receipt_bytes = bytes.len() - 1;
        assert_eq!(
            ProducerReceipt::decode(&bytes, too_short),
            Err(ReceiptFailure::Resource)
        );
        role[12] = 0;
        let legacy_claim = ProducerReceipt::decode(&role, receipt_limits()).unwrap();
        assert_eq!(
            legacy_claim.matches_expected(&decoded, receipt_limits()),
            Err(ReceiptFailure::Association)
        );
        let mut wrong = emission.payloads.checked_policy().unwrap().to_vec();
        wrong[12] ^= 1;
        assert_eq!(
            decoded.matches_checked_policy(&wrong, receipt_limits()),
            Err(ReceiptFailure::Association)
        );
        emission.payloads.test_change_policy();
        assert!(matches!(
            seed(&program, &sources, &build, &emission),
            Err(ReceiptFailure::Association)
        ));
        emission.payloads.test_change_policy();
        seed(&program, &sources, &build, &emission).unwrap();
        emission.payloads.test_change_image();
        assert!(matches!(
            seed(&program, &sources, &build, &emission),
            Err(ReceiptFailure::Association)
        ));
        emission.payloads.test_change_image();
        emission.payloads.test_change_facts();
        assert!(matches!(
            seed(&program, &sources, &build, &emission),
            Err(ReceiptFailure::Association)
        ));
        emission.payloads.test_change_facts();
        seed(&program, &sources, &build, &emission).unwrap();
        let mut changed = policy(&program);
        changed.observations += 1;
        changed.history += 1;
        assert!(matches!(
            super::super::checked_receipt::ReceiptSeed::from_checked_emission(
                &build,
                &program,
                &sources,
                &emission,
                super::super::host::NATIVE_TARGET.as_bytes(),
                receipt_limits(),
                changed
            ),
            Err(ReceiptFailure::Association)
        ));
    }
    #[test]
    fn checked_producer_real_image_donor_and_paid_policy_budgets() {
        let (program, sources) = genuine();
        let (build, emission) = emitted(&program, &sources);
        seed(&program, &sources, &build, &emission).unwrap();
        let altered = include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash")
            .replace("owner = (8, 8)", "owner = (8, 7)");
        let (donor, donor_sources) = crate::elaborate::checked_owner_passive_program_for_source(
            &altered,
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
        );
        let (donor_build, donor_emission) = emitted(&donor, &donor_sources);
        seed(&donor, &donor_sources, &donor_build, &donor_emission).unwrap();
        assert!(matches!(
            seed(&program, &sources, &build, &donor_emission),
            Err(ReceiptFailure::Association)
        ));
        let (image, facts) = emission.payloads.bytes();
        let mut hashing = TypeWorkBudget::with_limit(receipt_limits().work);
        let image = super::super::checked_receipt::pin(image, &mut hashing).unwrap();
        let facts = super::super::checked_receipt::pin(facts, &mut hashing).unwrap();
        let mut measured = TypeWorkBudget::default();
        let expected =
            policy_bytes(&program, image, facts, policy(&program), &mut measured).unwrap();
        let cost = measured.used();
        for prefix in [0, 7] {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            assert_eq!(
                policy_bytes(&program, image, facts, policy(&program), &mut exact).unwrap(),
                expected
            );
            assert_eq!(exact.used(), prefix + cost);
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                policy_bytes(&program, image, facts, policy(&program), &mut short),
                Err(ReceiptFailure::Resource)
            );
            assert!(policy_bytes(&program, image, facts, policy(&program), &mut short).is_err());
            let mut fresh = TypeWorkBudget::with_limit(cost);
            assert_eq!(
                policy_bytes(&program, image, facts, policy(&program), &mut fresh).unwrap(),
                expected
            );
        }
    }
    #[test]
    #[ignore = "requires an explicitly assigned compile/link-only native tool slot"]
    fn checked_producer_real_static_artifact_and_receipt_without_execution() {
        use super::super::{
            checked_receipt::{ProducerReceipt, ProducerRole, ReceiptField},
            host::{BuildConfiguration, NativeLinkInput},
        };
        use sha2::{Digest, Sha256};
        use std::{fs, io::Read, process::Command};
        let target = std::env::var_os("CARGO_TARGET_DIR")
            .map(std::path::PathBuf::from)
            .expect("explicit shared target required");
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = target.join(format!(
            "checked-owner-producer-artifact-{}-{nonce}",
            std::process::id()
        ));
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            fs::DirBuilder::new()
                .mode(0o700)
                .create(&directory)
                .unwrap();
        }
        fs::write(
            directory.join("owner.c"),
            include_bytes!("../../tests/fixtures/checked-owner-runtime/owner.c"),
        )
        .unwrap();
        fs::write(
            directory.join("owner.h"),
            include_bytes!("../../tests/fixtures/checked-owner-runtime/owner.h"),
        )
        .unwrap();
        let mut cc = Command::new("/usr/bin/cc");
        cc.args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"])
            .arg(directory.join("owner.c"))
            .arg("-o")
            .arg(directory.join("owner.o"));
        let result = cc.output().unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let archive = directory.join("libchecked-owner.a");
        let mut ar = Command::new("/usr/bin/ar");
        ar.arg("crs").arg(&archive).arg(directory.join("owner.o"));
        let result = ar.output().unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let (program, sources) = genuine();
        let mut config = BuildConfiguration::new(directory.join("program"));
        config.cargo_target_directory = Some(target);
        config.native_inputs = vec![NativeLinkInput::StaticArchive(archive)];
        config.producer_receipt = Some(receipt_limits());
        let prepared = super::super::host::prepare_checked_program(
            &program,
            &sources,
            config,
            policy(&program),
        )
        .unwrap();
        assert_eq!(
            prepared.producer_receipt().unwrap().role(),
            ProducerRole::CheckedPreparation
        );
        assert_eq!(
            prepared
                .producer_receipt()
                .unwrap()
                .pin(ReceiptField::FinalElf),
            None
        );
        assert!(
            prepared
                .generated_rust()
                .contains("__run_private_effect_image")
        );
        let built = super::super::host::build_prepared(prepared).unwrap();
        assert_eq!(
            built.compilation_work(),
            crate::compiler_work::CompilationWork::default()
        );
        let raw = fs::read(built.producer_receipt().unwrap()).unwrap();
        assert!(raw.len() <= receipt_limits().receipt_bytes);
        let receipt = ProducerReceipt::decode(&raw, receipt_limits()).unwrap();
        assert_eq!(receipt.role(), ProducerRole::CheckedPreparation);
        let generated = built.generated_source().parent().unwrap();
        let policy = fs::read(generated.join("checked-policy.bin")).unwrap();
        receipt
            .matches_checked_policy(&policy, receipt_limits())
            .unwrap();
        let mut pins = serde_json::Map::new();
        for (field, path) in [
            (
                ReceiptField::ProgramImage,
                generated.join("program-image.bin"),
            ),
            (
                ReceiptField::ExpectedFacts,
                generated.join("expected-facts.bin"),
            ),
            (
                ReceiptField::GeneratedRust,
                built.generated_source().to_path_buf(),
            ),
            (ReceiptField::FinalElf, built.executable().to_path_buf()),
        ] {
            let mut file = fs::File::open(&path).unwrap();
            let before = file.metadata().unwrap();
            assert!(before.len() <= receipt_limits().artifact_bytes as u64);
            let mut sha = Sha256::new();
            let mut buffer = [0u8; 65536];
            let mut bytes = 0u64;
            loop {
                let n = file.read(&mut buffer).unwrap();
                if n == 0 {
                    break;
                }
                bytes += n as u64;
                assert!(bytes <= receipt_limits().artifact_bytes as u64);
                sha.update(&buffer[..n]);
            }
            assert_eq!(before.len(), file.metadata().unwrap().len());
            let observed = ArtifactPin {
                bytes,
                sha256: sha.finalize().into(),
            };
            assert_eq!(receipt.pin(field), Some(observed));
            pins.insert(format!("{field:?}"),serde_json::json!({"path":path,"bytes":bytes,"sha256":observed.sha256.iter().map(|byte|format!("{byte:02x}")).collect::<String>()}));
        }
        assert_eq!(
            receipt.check_checked_applicability(),
            Err(ReceiptFailure::IncompleteClosure)
        );
        assert_eq!(
            receipt.activate(),
            Err(ReceiptFailure::ProtectedAuthorityUnavailable)
        );
        fs::write(directory.join("observation.json"),serde_json::to_vec_pretty(&serde_json::json!({"purpose":"compile/link-only; output never executed","cc":format!("{cc:?}"),"ar":format!("{ar:?}"),"output":built.executable(),"receipt":built.producer_receipt(),"pins":pins,"source_phase_measurements":"absent, not fabricated public-driver history"})).unwrap()).unwrap();
        println!(
            "checked producer original artifact retained at {}",
            directory.display()
        );
    }
}
