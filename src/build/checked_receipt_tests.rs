//! Product receipt tests use real existing-profile Core and emission. No linker
//! or candidate is executed; final-file observations use ordinary text fixtures.
use super::*;

#[test]
fn settled_configuration_reobserves_all_files_without_replacing_build_data_pin() {
    with_seed(|mut seed| {
        let nonce=std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let dir=std::env::temp_dir().join(format!("ash-root-config-observation-{}-{nonce}",std::process::id()));
        std::fs::create_dir(&dir).unwrap();
        let paths=[dir.join("Cargo.toml"),dir.join("rust-toolchain.toml"),dir.join("Cargo.lock")];
        for (i,path) in paths.iter().enumerate() {std::fs::write(path,format!("actual config {i}")).unwrap();}
        assert_eq!(seed.verify_settled_configuration(&paths),Err(ReceiptFailure::Association));
        seed.observe_configuration(&paths).unwrap();
        let pin=seed.receipt().pin(ReceiptField::BuildConfiguration);
        seed.verify_settled_configuration(&paths).unwrap();
        assert_eq!(seed.receipt().pin(ReceiptField::BuildConfiguration),pin);
        for path in &paths {
            let original=std::fs::read(path).unwrap();let mut donor=original.clone();donor[0]^=1;
            std::fs::write(path,donor).unwrap();
            assert_eq!(seed.verify_settled_configuration(&paths),Err(ReceiptFailure::Association));
            std::fs::write(path,original).unwrap();
            seed.verify_settled_configuration(&paths).unwrap();
            assert_eq!(seed.receipt().pin(ReceiptField::BuildConfiguration),pin);
        }
        std::fs::remove_dir_all(dir).unwrap();
    });
}

fn limits() -> ProducerReceiptLimits {
    ProducerReceiptLimits {
        artifact_bytes: 2_000_000,
        receipt_bytes: 4096,
        records: 16,
        work: 8_000_000,
    }
}

fn with_seed(test: impl FnOnce(ReceiptSeed)) {
    super::super::checked_admission::tests::with_program(
        super::super::checked_admission::tests::SOURCE,
        |program, provenance| {
            let build = super::super::image::encode_effect_for_build(
                program,
                provenance,
                super::super::host::NATIVE_TARGET,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            let emission = super::super::emit::native_host(
                &build,
                &super::super::runtime_fingerprint(),
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            let seed = ReceiptSeed::from_emission(
                &build,
                program,
                provenance,
                &emission,
                b"actual test build configuration",
                limits(),
            )
            .unwrap();
            test(seed);
        },
    );
}

#[test]
fn receipt_real_emission_decode_and_matching_claims_are_not_approval() {
    with_seed(|seed| {
        let encoded = seed
            .receipt
            .encode(&mut TypeWorkBudget::with_limit(limits().work), limits())
            .unwrap();
        let decoded = ProducerReceipt::decode(&encoded, limits()).unwrap();
        assert_eq!(decoded, seed.receipt);
        decoded.matches_expected(&seed.receipt, limits()).unwrap();
        let mut substituted = encoded.clone();
        substituted[54 + super::super::host::NATIVE_TARGET.len() + 10] ^= 1;
        let substituted = ProducerReceipt::decode(&substituted, limits()).unwrap();
        assert_eq!(
            substituted.matches_expected(&decoded, limits()),
            Err(ReceiptFailure::Association)
        );
        assert_eq!(
            decoded.check_checked_applicability(),
            Err(ReceiptFailure::IncompleteClosure)
        );
        assert_eq!(
            decoded.activate(),
            Err(ReceiptFailure::ProtectedAuthorityUnavailable)
        );
        assert!(decoded.pin(ReceiptField::ProgramImage).is_some());
        assert!(decoded.pin(ReceiptField::ExpectedFacts).is_some());
        assert_eq!(decoded.pin(ReceiptField::FinalElf), None);
        let mut complete_claim = decoded.clone();
        for field in &mut complete_claim.fields {
            if field.is_none() {
                *field = Some(ArtifactPin {
                    bytes: 32,
                    sha256: [7; 32],
                });
            }
        }
        let wire = complete_claim
            .encode(&mut TypeWorkBudget::with_limit(limits().work), limits())
            .unwrap();
        let independently_decoded = ProducerReceipt::decode(&wire, limits()).unwrap();
        independently_decoded
            .matches_expected(&complete_claim, limits())
            .unwrap();
        assert_eq!(
            independently_decoded.check_checked_applicability(),
            Err(ReceiptFailure::IncompleteClosure)
        );
        assert_eq!(
            independently_decoded.activate(),
            Err(ReceiptFailure::ProtectedAuthorityUnavailable)
        );
        with_directory(|directory| {
            let path = directory.join("same-uid-producer-receipt.bin");
            std::fs::write(&path, &encoded).unwrap();
            let from_same_uid =
                ProducerReceipt::read(&mut std::fs::File::open(path).unwrap(), limits()).unwrap();
            from_same_uid.matches_expected(&decoded, limits()).unwrap();
            assert_eq!(
                from_same_uid.activate(),
                Err(ReceiptFailure::ProtectedAuthorityUnavailable)
            );
        });
    });
}

#[test]
fn receipt_independent_decode_refuses_unknown_duplicate_trailing_and_short_work() {
    with_seed(|seed| {
        let mut work = TypeWorkBudget::with_limit(limits().work);
        let encoded = seed.receipt.encode(&mut work, limits()).unwrap();
        ProducerReceipt::decode(&encoded, limits()).unwrap();
        let declared = 22 + super::super::host::NATIVE_TARGET.len();
        for (offset, value) in [
            (declared + 8, encoded.len() - 1),
            (declared + 16, FIELDS - 1),
        ] {
            let mut inconsistent = encoded.clone();
            inconsistent[offset..offset + 8].copy_from_slice(&(value as u64).to_le_bytes());
            assert_eq!(
                ProducerReceipt::decode(&inconsistent, limits()),
                Err(ReceiptFailure::Resource)
            );
            ProducerReceipt::decode(&encoded, limits()).unwrap();
        }
        for index in [0, 8, 12] {
            let mut wrong = encoded.clone();
            wrong[index] = 255;
            assert!(ProducerReceipt::decode(&wrong, limits()).is_err());
        }
        let mut duplicate = encoded.clone();
        duplicate[54 + super::super::host::NATIVE_TARGET.len() + RECORD_BYTES] = 0; // second field repeats the first missing/present field tag
        assert!(ProducerReceipt::decode(&duplicate, limits()).is_err());
        let mut unknown = encoded.clone();
        unknown[54 + super::super::host::NATIVE_TARGET.len()] = 255;
        assert_eq!(
            ProducerReceipt::decode(&unknown, limits()),
            Err(ReceiptFailure::Malformed)
        );
        let mut trailing = encoded.clone();
        trailing.push(0);
        assert_eq!(
            ProducerReceipt::decode(&trailing, limits()),
            Err(ReceiptFailure::Malformed)
        );
        let mut measured = TypeWorkBudget::with_limit(limits().work);
        ProducerReceipt::decode_with_work(&encoded, limits(), &mut measured).unwrap();
        for prefix in [0, 7] {
            let mut exact = TypeWorkBudget::with_limit(prefix + measured.used());
            exact.charge(prefix).unwrap();
            assert!(ProducerReceipt::decode_with_work(&encoded, limits(), &mut exact).is_ok());
            let mut short = TypeWorkBudget::with_limit(prefix + measured.used() - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                ProducerReceipt::decode_with_work(&encoded, limits(), &mut short),
                Err(ReceiptFailure::Resource)
            );
            assert_eq!(
                ProducerReceipt::decode_with_work(&encoded, limits(), &mut short),
                Err(ReceiptFailure::Resource)
            );
        }
        let mut small = limits();
        small.receipt_bytes = encoded.len() - 1;
        assert_eq!(
            ProducerReceipt::decode(&encoded, small),
            Err(ReceiptFailure::Resource)
        );
        let mut fresh = TypeWorkBudget::with_limit(limits().work);
        assert!(ProducerReceipt::decode_with_work(&encoded, limits(), &mut fresh).is_ok());
    });
}

#[test]
fn receipt_genuine_emission_donor_payload_and_mapping_refuse() {
    super::super::checked_admission::tests::with_program(
        super::super::checked_admission::tests::SOURCE,
        |program, provenance| {
            let mut build = super::super::image::encode_effect_for_build(
                program,
                provenance,
                super::super::host::NATIVE_TARGET,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            let mut emission = super::super::emit::native_host(
                &build,
                &super::super::runtime_fingerprint(),
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            assert!(
                ReceiptSeed::from_emission(
                    &build,
                    program,
                    provenance,
                    &emission,
                    b"config",
                    limits()
                )
                .is_ok()
            );
            let mut seed = ReceiptSeed::from_emission(
                &build,
                program,
                provenance,
                &emission,
                b"config",
                limits(),
            )
            .unwrap();
            with_directory(|directory| {
                let paths = [
                    directory.join("main.rs"),
                    directory.join("program-image.bin"),
                    directory.join("expected-facts.bin"),
                ];
                let (image, facts) = emission.payloads.bytes();
                for (path, bytes) in
                    paths
                        .iter()
                        .zip([emission.rust_source.as_bytes(), image, facts])
                {
                    std::fs::write(path, bytes).unwrap();
                }
                seed.verify_emitted_files(&paths).unwrap();
                std::fs::write(&paths[2], b"substituted fact payload").unwrap();
                assert_eq!(
                    seed.verify_emitted_files(&paths),
                    Err(ReceiptFailure::Association)
                );
                assert_eq!(
                    seed.verify_emitted_files(&paths),
                    Err(ReceiptFailure::Association)
                );
            });
            build.bridges[0].operation_local += 1;
            assert!(matches!(
                ReceiptSeed::from_emission(
                    &build,
                    program,
                    provenance,
                    &emission,
                    b"config",
                    limits()
                ),
                Err(ReceiptFailure::Association)
            ));
            build.bridges[0].operation_local -= 1;
            emission.payloads.test_change_image();
            assert!(matches!(
                ReceiptSeed::from_emission(
                    &build,
                    program,
                    provenance,
                    &emission,
                    b"config",
                    limits()
                ),
                Err(ReceiptFailure::Association)
            ));
        },
    );
}

fn with_directory(test: impl FnOnce(&Path)) {
    use std::sync::atomic::{AtomicU64, Ordering};
    static IDS: AtomicU64 = AtomicU64::new(0);
    struct Directory(std::path::PathBuf);
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let directory = loop {
        let path = std::env::temp_dir().join(format!(
            "ash-producer-receipt-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        match std::fs::create_dir(&path) {
            Ok(()) => break Directory(path),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("receipt fixture: {error}"),
        }
    };
    test(&directory.0);
}

#[test]
fn receipt_post_link_object_observation_is_bounded_and_not_immutable_authority() {
    with_seed(|mut seed| {
        with_directory(|directory| {
            // Synthetic data with the admitted target header. It is never executed
            // and is not credited as a linked/native image or ABI proof.
            let mut elf = [0_u8; 64];
            elf[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
            elf[16..18].copy_from_slice(&2_u16.to_le_bytes());
            elf[18..20].copy_from_slice(&62_u16.to_le_bytes());
            elf[20..24].copy_from_slice(&1_u32.to_le_bytes());
            elf[52..54].copy_from_slice(&64_u16.to_le_bytes());
            let linked = directory.join("linked-program");
            std::fs::write(&linked, elf).unwrap();
            let paths = [
                directory.join("Cargo.toml"),
                directory.join("rust-toolchain.toml"),
                directory.join("Cargo.lock"),
            ];
            for path in &paths {
                std::fs::write(path, b"initial configuration").unwrap();
            }
            seed.observe_configuration(&paths).unwrap();
            std::fs::write(&paths[2], b"resolved root lock").unwrap();
            seed.verify_configuration(&paths).unwrap();
            seed.observe_native_inputs(&[]).unwrap();
            seed.verify_native_inputs(&[]).unwrap();
            let encoded = seed.finalize(&linked).unwrap();
            let receipt = ProducerReceipt::read(&mut encoded.as_slice(), limits()).unwrap();
            assert_eq!(
                receipt.pin(ReceiptField::FinalElf),
                Some(ArtifactPin {
                    bytes: 64,
                    sha256: Sha256::digest(elf).into()
                })
            );
            assert_eq!(
                receipt.activate(),
                Err(ReceiptFailure::ProtectedAuthorityUnavailable)
            );
            assert_eq!(
                receipt.check_checked_applicability(),
                Err(ReceiptFailure::IncompleteClosure)
            );
            std::fs::write(&linked, b"replacement after observation").unwrap();
            assert_ne!(
                observe_file(
                    &linked,
                    limits().artifact_bytes,
                    &mut TypeWorkBudget::default()
                )
                .unwrap(),
                receipt.pin(ReceiptField::FinalElf).unwrap()
            );
            assert_eq!(
                observe_elf(
                    &linked,
                    limits().artifact_bytes,
                    &mut TypeWorkBudget::default()
                ),
                Err(ReceiptFailure::Input)
            );
            assert_eq!(
                observe_file(&linked, 1, &mut TypeWorkBudget::default()),
                Err(ReceiptFailure::Resource)
            );
            assert_eq!(
                observe_file(
                    directory,
                    limits().artifact_bytes,
                    &mut TypeWorkBudget::default()
                ),
                Err(ReceiptFailure::Input)
            );
            let mut cap = limits();
            cap.receipt_bytes = encoded.len() - 1;
            assert_eq!(
                ProducerReceipt::read(&mut encoded.as_slice(), cap),
                Err(ReceiptFailure::Resource)
            );
        })
    });
}

#[test]
fn receipt_real_second_program_is_not_the_first_programs_emitted_payload() {
    super::super::checked_admission::tests::with_program(
        super::super::checked_admission::tests::SOURCE,
        |program, provenance| {
            let build = super::super::image::encode_effect_for_build(
                program,
                provenance,
                super::super::host::NATIVE_TARGET,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            let canonical = super::super::emit::native_host(
                &build,
                &super::super::runtime_fingerprint(),
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            assert!(
                ReceiptSeed::from_emission(
                    &build,
                    program,
                    provenance,
                    &canonical,
                    b"config",
                    limits()
                )
                .is_ok()
            );
            let donor =
                super::super::checked_admission::tests::SOURCE.replace("call 42", "call 43");
            super::super::checked_admission::tests::with_program(
                &donor,
                |other, other_provenance| {
                    let other_build = super::super::image::encode_effect_for_build(
                        other,
                        other_provenance,
                        super::super::host::NATIVE_TARGET,
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
                    let other_emission = super::super::emit::native_host(
                        &other_build,
                        &super::super::runtime_fingerprint(),
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
                    assert!(
                        ReceiptSeed::from_emission(
                            &other_build,
                            other,
                            other_provenance,
                            &other_emission,
                            b"config",
                            limits()
                        )
                        .is_ok()
                    );
                    assert!(matches!(
                        ReceiptSeed::from_emission(
                            &build,
                            program,
                            provenance,
                            &other_emission,
                            b"config",
                            limits()
                        ),
                        Err(ReceiptFailure::Association)
                    ));
                },
            );
        },
    );
}

#[test]
fn receipt_native_input_and_generated_configuration_substitution_refuse() {
    with_seed(|mut seed| {
        with_directory(|directory| {
            let input = directory.join("archive.a");
            std::fs::write(&input, b"observed native bytes").unwrap();
            let inputs = [super::super::host::NativeLinkInput::StaticArchive(
                input.clone(),
            )];
            seed.observe_native_inputs(&inputs).unwrap();
            seed.verify_native_inputs(&inputs).unwrap();
            std::fs::write(&input, b"changed native bytes").unwrap();
            assert_eq!(
                seed.verify_native_inputs(&inputs),
                Err(ReceiptFailure::Association)
            );
            let paths = [
                directory.join("Cargo.toml"),
                directory.join("rust-toolchain.toml"),
                directory.join("Cargo.lock"),
            ];
            for path in &paths {
                std::fs::write(path, b"initial").unwrap();
            }
            seed.observe_configuration(&paths).unwrap();
            std::fs::write(&paths[0], b"substituted manifest").unwrap();
            assert_eq!(
                seed.verify_configuration(&paths),
                Err(ReceiptFailure::Association)
            );
        })
    });
}

#[test]
fn receipt_public_preparation_is_explicit_and_preserves_legacy_work() {
    super::super::checked_admission::tests::with_driver_result(
        super::super::checked_admission::tests::SOURCE,
        |result| {
            let program = result.unwrap();
            let configuration =
                || super::super::host::BuildConfiguration::new("unused-receipt-test-output".into());
            let ordinary = super::super::host::prepare_program(&program, configuration()).unwrap();
            assert!(ordinary.producer_receipt().is_none());
            let mut requested = configuration();
            requested.producer_receipt = Some(limits());
            let observed = super::super::host::prepare_program(&program, requested).unwrap();
            assert_eq!(ordinary.preparation_work(), observed.preparation_work());
            let receipt = observed.producer_receipt().unwrap();
            assert!(receipt.pin(ReceiptField::ProgramImage).is_some());
            assert_eq!(receipt.pin(ReceiptField::FinalElf), None);
            assert_eq!(
                receipt.activate(),
                Err(ReceiptFailure::ProtectedAuthorityUnavailable)
            );
            let mut short = configuration();
            short.producer_receipt = Some(ProducerReceiptLimits {
                work: 0,
                ..limits()
            });
            assert_eq!(
                super::super::host::prepare_program(&program, short)
                    .unwrap_err()
                    .reason(),
                "build.producer-receipt"
            );
        },
    );
}
