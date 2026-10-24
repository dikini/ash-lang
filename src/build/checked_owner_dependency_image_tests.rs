//! Real private checked dependency reconstruction, without executable admission.
use super::super::{NativeImageFailure, PureImage, encode_effect_for_build, encode_program};
use super::*;

fn retain_encoded_inputs(bytes: &[u8], expectations: &[u8]) {
    use std::io::Write;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let Some(directory) = std::env::var_os("ASH_CHECKED_DEPENDENCY_CAPTURE") else {
        return;
    };
    const MAX_BYTES: usize = 16 * 1024 * 1024;
    assert!(bytes.len() <= MAX_BYTES && expectations.len() <= MAX_BYTES);
    let thread = std::thread::current();
    let selector = thread.name().expect("named exact test thread");
    assert!(matches!(
        selector,
        "elaborate::checked_owner_lifecycle_tests::checked_owner_dependency_tests::checked_owner_dependency_private_static_image_roundtrip_and_bounds"
            | "elaborate::checked_owner_lifecycle_tests::checked_owner_dependency_tests::checked_owner_dependency_retained_access_borrow_requires_exact_window"
            | "elaborate::checked_owner_lifecycle_tests::checked_sqlite_dependent_tests::checked_sqlite_dependent_source_preserves_original_parent_core_and_transforms"
    ));
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let ordinal = NEXT.fetch_add(1, Ordering::Relaxed);
    assert!(ordinal < 2, "bounded exact-selector image captures");
    let directory = std::path::PathBuf::from(directory);
    assert!(
        directory.is_dir(),
        "runner creates a fresh capture directory"
    );
    for (extension, data) in [("image", bytes), ("expectations", expectations)] {
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(directory.join(format!("{ordinal}.{extension}")))
            .unwrap();
        file.write_all(data).unwrap();
    }
    let mut association = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(directory.join(format!("{ordinal}.txt")))
        .unwrap();
    writeln!(
        association,
        "selector={selector}\nordinal={ordinal}\nimage_bytes={}\nexpectation_bytes={}",
        bytes.len(),
        expectations.len()
    )
    .unwrap();
    eprintln!(
        "retained checked dependency input ordinal={ordinal} image_bytes={} expectation_bytes={}",
        bytes.len(),
        expectations.len()
    );
}

pub(crate) fn controls(
    program: &crate::core::ValidatedEffectProgram,
    provenance: &[(super::super::ModuleId, Arc<super::super::SourceFile>)],
    standalone: crate::build::CheckedDependencyStandalone,
) {
    // A fixture label selects the same already-authenticated dependent header
    // for hostile mutation; it supplies no binding or restoration authority.
    let dependent_name = program
        .nodes()
        .iter()
        .find_map(|node| match &node.kind {
            crate::core::EffectExprKind::Operation(
                crate::core::EffectOperation::SourceResourceScope(scope),
            ) if !scope.header().dependencies.is_empty() => {
                Some(scope.header().original.spelling.as_str())
            }
            _ => None,
        })
        .expect("genuine dependent resource from the validated Core input");
    assert!(matches!(
        encode_effect_for_build(
            program,
            provenance,
            super::super::super::NATIVE_TARGET,
            &mut TypeWorkBudget::default()
        ),
        Err(NativeImageFailure::Image(ImageFailure::Unsupported(
            Unsupported::EffectOperation
        )))
    ));
    let mut encoding = TypeWorkBudget::default();
    let encoder = encode_program(
        program,
        provenance,
        &mut encoding,
        true,
        |encoder| {
            for node in program.nodes() {
                charge(encoder.work, 1)?;
                if let crate::core::EffectExprKind::Operation(
                    crate::core::EffectOperation::SourceResourceScope(scope),
                ) = &node.kind
                {
                    encoder.encode_source_registry_view(scope.original(), program.registry())?;
                }
            }
            Ok(())
        },
        |encoder, kind| encoder.encode_effect_node(kind),
    )
    .unwrap();
    let image = encoder.image;
    let owner = image
        .prepared_owners
        .iter()
        .position(|o| o.retains.len > 0)
        .unwrap();
    assert_eq!(image.prepared_owners[owner].retains.len, 1);
    let has_offset = image.prepared_symbols.iter().any(|symbol| {
        matches!(
            symbol.owner_call,
            Some(PreparedOwnerCallRecord::OutputAcquire {
                offset: Some(_),
                ..
            })
        )
    });
    let bytes = image.encode_bytes(&mut TypeWorkBudget::default()).unwrap();
    let expectations = image
        .encode_native_expectations(&mut TypeWorkBudget::default())
        .unwrap();
    retain_encoded_inputs(&bytes, &expectations);
    drop(image);
    let decode = || PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
    let canonical = decode();
    canonical
        .compare_native_expectations(&expectations, &mut TypeWorkBudget::default())
        .unwrap();
    let mut standalone_work = TypeWorkBudget::default();
    let standalone_result = canonical.restore_effect(&mut standalone_work);
    match (standalone, standalone_result) {
        (crate::build::CheckedDependencyStandalone::Fits, Ok(restored)) => drop(restored),
        (crate::build::CheckedDependencyStandalone::Resource, Err(error)) => {
            assert!(
                matches!(&error, ImageFailure::Resource)
                    || matches!(&error, ImageFailure::Validation(error) if error.reason() == crate::core::ValidationReason::Resource)
                    || matches!(
                        &error,
                        ImageFailure::CoreAdmission(crate::core::BuildError::TypeWorkExceeded)
                    ),
                "standalone refusal must be exhausted work, not a semantic error: {error:?}"
            );
            println!(
                "checked dependency standalone refusal used={} limit={} actual={error:?}",
                standalone_work.used(),
                standalone_work.limit()
            );
        }
        (_, Err(error)) => {
            panic!("smaller baseline must fit unchanged standalone default: {error:?}")
        }
        (_, Ok(restored)) => {
            drop(restored);
            panic!("larger standalone exhaustion premise changed; review the observed result");
        }
    }
    let startup = || super::super::super::gas::startup(bytes.len(), expectations.len()).unwrap();
    // This is the actual startup reconstruction segment: one meter covers
    // canonical decoding, expected-fact admission and independent restoration.
    // Executable library/member binding and activation remain outside this test.
    let restore = |work: &mut TypeWorkBudget| {
        let image = PureImage::decode_bytes(&bytes, work)?;
        let _facts = image.admit_expected_native_facts(&expectations, work)?;
        image.restore_effect(work)
    };
    let mut measured = startup();
    let allowance = measured.limit();
    let restored = restore(&mut measured)
        .expect("actual dependent checked reconstruction segment fits existing startup policy");
    assert!(restored.program.nodes().iter().any(|n| matches!(&n.kind, crate::core::EffectExprKind::Operation(crate::core::EffectOperation::SourceResourceScope(s)) if !s.header().dependencies.is_empty())));
    let cost = measured.used();
    drop(restored);
    for prefix in [0, 7] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        match restore(&mut short) {
            Err(ImageFailure::Resource) => {}
            Err(ImageFailure::Validation(e))
                if e.reason() == crate::core::ValidationReason::Resource => {}
            _ => panic!("one-short requires Resource, not semantic/setup refusal"),
        }
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            restore(&mut exact).unwrap();
            assert_eq!(exact.used(), prefix + cost);
            match restore(&mut exact) {
                Err(ImageFailure::Resource) => {}
                Err(ImageFailure::Validation(e))
                    if e.reason() == crate::core::ValidationReason::Resource => {}
                _ => panic!("spent operation requires Resource refusal"),
            }
        }
    }
    for mutation in 0..3 + 2 * usize::from(has_offset) {
        let mut hostile_work = startup();
        let mut hostile = PureImage::decode_bytes(&bytes, &mut hostile_work).unwrap();
        // The mutation is deliberately inside the restored-image seam, after
        // the same original fact-admission stage as the production caller.
        {
            let _facts = hostile
                .admit_expected_native_facts(&expectations, &mut hostile_work)
                .unwrap();
        }
        match mutation {
            0 => hostile.prepared_owners[owner].retains.len = 0,
            1 => {
                let start = hostile.prepared_owners[owner].retains.start as usize;
                hostile.prepared_projections[start] =
                    hostile.prepared_owners[owner].owned_parameter;
            }
            2 => {
                let slot = hostile
                    .resource_headers
                    .iter()
                    .position(|h| {
                        h.spelling.get(&hostile.bytes).unwrap() == dependent_name.as_bytes()
                    })
                    .expect("same original dependent resource label");
                let owned = hostile.resource_headers[slot].owned_position;
                assert_ne!(hostile.resource_headers[slot].host.unwrap().position, owned);
                hostile.resource_headers[slot]
                    .host
                    .as_mut()
                    .unwrap()
                    .position = owned;
            }
            3 => {
                let offset = hostile
                    .prepared_symbols
                    .iter_mut()
                    .find_map(|symbol| match &mut symbol.owner_call {
                        Some(PreparedOwnerCallRecord::OutputAcquire {
                            offset: Some(offset),
                            ..
                        }) => Some(offset),
                        _ => None,
                    })
                    .expect("original dependent output offset");
                assert_eq!(offset.input_operand, 1);
                offset.input_operand = 0;
            }
            4 => {
                let outcomes = hostile
                    .prepared_symbols
                    .iter()
                    .find_map(|symbol| match symbol.owner_call {
                        Some(PreparedOwnerCallRecord::StatusTeardown { outcomes, .. })
                            if outcomes.len == 1 =>
                        {
                            Some(outcomes)
                        }
                        _ => None,
                    })
                    .expect("original total consumed status teardown");
                let outcome = &mut hostile.prepared_owner_status_outcomes[outcomes.start as usize];
                assert!(outcome.consumes && outcome.readable);
                outcome.consumes = false;
            }
            _ => unreachable!(),
        }
        let error = match hostile.restore_effect(&mut hostile_work) {
            Ok(_) => panic!("dependency wire substitution must refuse"),
            Err(e) => e,
        };
        match error {
            ImageFailure::Resource => panic!("no Resource hostile credit"),
            ImageFailure::Validation(e) => {
                assert_ne!(e.reason(), crate::core::ValidationReason::Resource)
            }
            ImageFailure::Unsupported(_) | ImageFailure::CoreAdmission(_) => {
                panic!("no unsupported/setup hostile credit")
            }
            _ => {}
        }
    }
    println!(
        "checked dependency reconstruction-segment work={cost} allowance={allowance} remaining={} remaining_percent={:.2}; exact/prefix/short/spent/two fresh, erased/substituted retained parameter and wrong Host refuse; no executable binding/native entry",
        allowance - cost,
        100.0 * (allowance - cost) as f64 / allowance as f64
    );
}
