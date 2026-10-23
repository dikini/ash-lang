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
) {
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
    let mut measured = TypeWorkBudget::default();
    let restored = canonical
        .restore_effect(&mut measured)
        .expect("actual dependent checked private image restores independently");
    assert!(restored.program.nodes().iter().any(|n| matches!(&n.kind, crate::core::EffectExprKind::Operation(crate::core::EffectOperation::SourceResourceScope(s)) if !s.header().dependencies.is_empty())));
    let cost = measured.used();
    drop(restored);
    for prefix in [0, 7] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        match canonical.restore_effect(&mut short) {
            Err(ImageFailure::Resource) => {}
            Err(ImageFailure::Validation(e))
                if e.reason() == crate::core::ValidationReason::Resource => {}
            _ => panic!("one-short requires Resource, not semantic/setup refusal"),
        }
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            canonical.restore_effect(&mut exact).unwrap();
            assert_eq!(exact.used(), prefix + cost);
            match canonical.restore_effect(&mut exact) {
                Err(ImageFailure::Resource) => {}
                Err(ImageFailure::Validation(e))
                    if e.reason() == crate::core::ValidationReason::Resource => {}
                _ => panic!("spent operation requires Resource refusal"),
            }
        }
    }
    for mutation in 0..3 {
        let mut hostile = decode();
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
                    .position(|h| h.spelling.get(&hostile.bytes).unwrap() == b"Child")
                    .expect("actual dependent Child header");
                let owned = hostile.resource_headers[slot].owned_position;
                assert_ne!(hostile.resource_headers[slot].host.unwrap().position, owned);
                hostile.resource_headers[slot]
                    .host
                    .as_mut()
                    .unwrap()
                    .position = owned;
            }
            _ => unreachable!(),
        }
        let error = match hostile.restore_effect(&mut TypeWorkBudget::default()) {
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
        "checked dependency private image work={cost}; exact/prefix/short/spent/two fresh, erased/substituted retained parameter and wrong Host refuse"
    );
}
