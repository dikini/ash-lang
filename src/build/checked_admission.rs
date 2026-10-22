//! Passive applicability metadata using existing image and bridge admission.
//! No protected approval/context implementation or executable capability exists.
#![allow(
    dead_code,
    reason = "TASK0053 passive plan is not executable admission"
)]

use super::image::{ExpectedNativeFacts, NativeBuildImage};
use crate::{core::ValidatedEffectProgram, types::TypeWorkBudget};
use sha2::{Digest, Sha256};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Failure {
    Resource,
    Version,
    Mode,
    Target,
    Association,
    BuildUnavailable,
    ProtectedAuthorityUnavailable,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Mode {
    InProcess,
    Isolated,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Limits {
    pub(super) image: usize,
    pub(super) facts: usize,
    pub(super) bridges: usize,
    pub(super) metadata: usize,
}

/// These are claimed applicability inputs, not accepted native premises or an
/// administrator-established context. Deterministic encoding never approves them.
pub(super) struct Applicability<'a> {
    pub(super) version: u32,
    pub(super) mode: Mode,
    pub(super) target: &'a str,
    pub(super) runtime: [u8; 32],
    pub(super) native_closure: [u8; 32],
    pub(super) premises: [u8; 32],
    pub(super) context: Option<[u8; 32]>,
    pub(super) limits: Limits,
}

pub(super) struct PassivePlan<'a> {
    build: &'a NativeBuildImage,
    program: &'a ValidatedEffectProgram,
    facts: ExpectedNativeFacts<'a>,
    image_digest: [u8; 32],
    facts_digest: [u8; 32],
    metadata: Vec<u8>,
}

fn pay(work: &mut TypeWorkBudget, cells: usize) -> Result<(), Failure> {
    work.charge(cells).map_err(|()| Failure::Resource)
}
fn image_failure(failure: super::image::ImageFailure) -> Failure {
    match failure {
        super::image::ImageFailure::Resource => Failure::Resource,
        super::image::ImageFailure::Validation(error)
            if error.reason() == crate::core::ValidationReason::Resource =>
        {
            Failure::Resource
        }
        _ => Failure::Association,
    }
}
fn build_failure(failure: super::image::NativeImageFailure) -> Failure {
    match failure {
        super::image::NativeImageFailure::Image(super::image::ImageFailure::Unsupported(_)) => {
            Failure::BuildUnavailable
        }
        super::image::NativeImageFailure::Image(error) => image_failure(error),
        super::image::NativeImageFailure::Bridge(error) => {
            if error.is_resource() {
                Failure::Resource
            } else {
                Failure::Association
            }
        }
    }
}
fn digest(bytes: &[u8], work: &mut TypeWorkBudget) -> Result<[u8; 32], Failure> {
    pay(work, bytes.len())?;
    Ok(Sha256::digest(bytes).into())
}

impl Applicability<'_> {
    fn encode(&self, work: &mut TypeWorkBudget) -> Result<Vec<u8>, Failure> {
        pay(work, 8)?;
        if self.version != 1 {
            return Err(Failure::Version);
        }
        if self.mode != Mode::InProcess {
            return Err(Failure::Mode);
        }
        pay(work, self.target.len())?;
        if self.target != super::host::NATIVE_TARGET {
            return Err(Failure::Target);
        }
        if self.runtime != super::runtime_fingerprint() {
            return Err(Failure::Association);
        }
        // Fixed-endian length-delimited schema. No digest is an accepted flag.
        let size = 4_usize
            .checked_add(1)
            .and_then(|n| n.checked_add(4))
            .and_then(|n| n.checked_add(self.target.len()))
            .and_then(|n| n.checked_add(32 * 3 + 1 + self.context.map_or(0, |_| 32) + 8 * 4))
            .ok_or(Failure::Resource)?;
        if size > self.limits.metadata {
            return Err(Failure::Resource);
        }
        pay(work, size)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(size)
            .map_err(|_| Failure::Resource)?;
        bytes.extend_from_slice(&1_u32.to_le_bytes());
        bytes.push(0); // InProcess only; Isolated is not silently reinterpreted.
        bytes.extend_from_slice(
            &u32::try_from(self.target.len())
                .map_err(|_| Failure::Resource)?
                .to_le_bytes(),
        );
        bytes.extend_from_slice(self.target.as_bytes());
        for hash in [&self.runtime, &self.native_closure, &self.premises] {
            bytes.extend_from_slice(hash);
        }
        bytes.push(u8::from(self.context.is_some()));
        if let Some(context) = self.context {
            bytes.extend_from_slice(&context);
        }
        for limit in [
            self.limits.image,
            self.limits.facts,
            self.limits.bridges,
            self.limits.metadata,
        ] {
            bytes.extend_from_slice(
                &u64::try_from(limit)
                    .map_err(|_| Failure::Resource)?
                    .to_le_bytes(),
            );
        }
        Ok(bytes)
    }
}

impl<'a> PassivePlan<'a> {
    pub(super) fn admit(
        build: &'a NativeBuildImage,
        program: &'a ValidatedEffectProgram,
        provenance: &[(
            crate::module::ModuleId,
            std::sync::Arc<crate::source::SourceFile>,
        )],
        payload: &[u8],
        expected: &[u8],
        applicability: &Applicability<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        let metadata = applicability.encode(work)?;
        pay(work, 3)?;
        if payload.len() > applicability.limits.image
            || expected.len() > applicability.limits.facts
            || build.bridges.len() > applicability.limits.bridges
        {
            return Err(Failure::Resource);
        }
        // Reuse the actual product constructor, including its checked Host
        // refusal. A passive caller cannot substitute another image or bypass
        // that guard by supplying matching digest claims.
        let canonical_build =
            super::image::encode_effect_for_build(program, provenance, applicability.target, work)
                .map_err(build_failure)?;
        let canonical = canonical_build
            .image
            .encode_bytes(work)
            .map_err(image_failure)?;
        pay(work, payload.len())?;
        if canonical.as_slice() != payload {
            return Err(Failure::Association);
        }
        // Existing independent full fact-byte comparison, not a new registry.
        let supplied = build.image.encode_bytes(work).map_err(image_failure)?;
        pay(work, supplied.len())?;
        if supplied.len() > applicability.limits.image || supplied.as_slice() != payload {
            return Err(Failure::Association);
        }
        let facts = build
            .image
            .admit_expected_native_facts(expected, work)
            .map_err(image_failure)?;
        pay(work, 2)?;
        if build.bridges.len() != canonical_build.bridges.len()
            || build.libraries.len() != canonical_build.libraries.len()
        {
            return Err(Failure::Association);
        }
        for (left, right) in build.libraries.iter().zip(&canonical_build.libraries) {
            pay(
                work,
                left.members.len().checked_add(4).ok_or(Failure::Resource)?,
            )?;
            if left.image_library != right.image_library
                || left.module != right.module
                || left.ordinal != right.ordinal
                || left.members != right.members
            {
                return Err(Failure::Association);
            }
        }
        for (bridge, canonical) in build.bridges.iter().zip(&canonical_build.bridges) {
            pay(work, 6)?;
            if bridge.image_symbol != canonical.image_symbol
                || bridge.symbol_index != canonical.symbol_index
                || bridge.operation_module != canonical.operation_module
                || bridge.operation_effect != canonical.operation_effect
                || bridge.operation_local != canonical.operation_local
                || bridge.plan.operation() != canonical.plan.operation()
            {
                return Err(Failure::Association);
            }
            bridge
                .plan
                .authenticate_in_program(applicability.target, program, work)
                .map_err(|error| {
                    if error.is_resource() {
                        Failure::Resource
                    } else {
                        Failure::Association
                    }
                })?;
        }
        Ok(Self {
            build,
            program,
            facts,
            image_digest: digest(payload, work)?,
            facts_digest: digest(expected, work)?,
            metadata,
        })
    }

    pub(super) fn activate(&self) -> Result<std::convert::Infallible, Failure> {
        // Deliberately no constructor for protected authority and no caller
        // boolean/token that could turn this applicability plan into approval.
        Err(Failure::ProtectedAuthorityUnavailable)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    const SOURCE: &str = r#"import @builtin.foreign as Foreign
foreign library C {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    symbol Measure : Int -> Foreign.Call<Int> {
        name "ash_passive_measure"
        abi (Size) -> Size
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
main : Unit -> Int ! {Measure}
main () = match perform Measure.call 42 {
    Foreign.Returned(value) => value
    Foreign.ConversionFailed(_) => 0
}
"#;

    fn with_driver_result(
        source: &str,
        test: impl FnOnce(Result<crate::driver::CompiledProgram, crate::driver::FileFailure>),
    ) {
        static IDS: AtomicU64 = AtomicU64::new(0);
        struct Directory(std::path::PathBuf);
        impl Drop for Directory {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let directory = loop {
            let path = std::env::temp_dir().join(format!(
                "ash-passive-admission-{}-{}",
                std::process::id(),
                IDS.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => break Directory(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("passive admission fixture: {error}"),
            }
        };
        std::fs::write(directory.0.join("entry.ash"), source).unwrap();
        test(crate::driver::compile_path(
            crate::driver::RunConfiguration {
                entry: directory.0.join("entry.ash"),
                roots: crate::module::ModuleRoots::empty(),
            },
        ));
    }

    fn with_program(
        source: &str,
        test: impl FnOnce(
            &ValidatedEffectProgram,
            &[(
                crate::module::ModuleId,
                std::sync::Arc<crate::source::SourceFile>,
            )],
        ),
    ) {
        with_driver_result(source, |result| {
            let compiled = result.expect("actual existing-profile public driver source");
            let (program, provenance) = compiled.effect_build_input().unwrap();
            test(program, provenance);
        });
    }

    fn applicability() -> Applicability<'static> {
        Applicability {
            version: 1,
            mode: Mode::InProcess,
            target: super::super::host::NATIVE_TARGET,
            runtime: super::super::runtime_fingerprint(),
            native_closure: [0; 32],
            premises: [0; 32],
            context: None,
            limits: Limits {
                image: 1_048_576,
                facts: 1_048_576,
                bridges: 16,
                metadata: 4096,
            },
        }
    }

    #[test]
    fn checked_admission_genuine_image_binding_is_passive_and_never_approval() {
        with_program(SOURCE, |program, provenance| {
            let build = super::super::image::encode_effect_for_build(
                program,
                provenance,
                super::super::host::NATIVE_TARGET,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            assert!(!build.bridges.is_empty());
            let payload = build
                .image
                .encode_bytes(&mut TypeWorkBudget::default())
                .unwrap();
            let expected = build
                .image
                .encode_native_expectations(&mut TypeWorkBudget::default())
                .unwrap();
            let mut measured = TypeWorkBudget::default();
            let plan = PassivePlan::admit(
                &build,
                program,
                provenance,
                &payload,
                &expected,
                &applicability(),
                &mut measured,
            )
            .unwrap();
            assert_eq!(plan.activate(), Err(Failure::ProtectedAuthorityUnavailable));
            let mut arbitrary_context = applicability();
            arbitrary_context.context = Some([7; 32]); // claimed context is still not protected authority
            let claimed = PassivePlan::admit(
                &build,
                program,
                provenance,
                &payload,
                &expected,
                &arbitrary_context,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            assert_eq!(
                claimed.activate(),
                Err(Failure::ProtectedAuthorityUnavailable)
            );
            for prefix in [0, 7] {
                let mut exact = TypeWorkBudget::with_limit(prefix + measured.used());
                exact.charge(prefix).unwrap();
                assert!(
                    PassivePlan::admit(
                        &build,
                        program,
                        provenance,
                        &payload,
                        &expected,
                        &applicability(),
                        &mut exact
                    )
                    .is_ok()
                );
                let mut short = TypeWorkBudget::with_limit(prefix + measured.used() - 1);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    PassivePlan::admit(
                        &build,
                        program,
                        provenance,
                        &payload,
                        &expected,
                        &applicability(),
                        &mut short
                    ),
                    Err(Failure::Resource)
                ));
                assert!(matches!(
                    PassivePlan::admit(
                        &build,
                        program,
                        provenance,
                        &payload,
                        &expected,
                        &applicability(),
                        &mut short
                    ),
                    Err(Failure::Resource)
                ));
            }
            assert!(
                PassivePlan::admit(
                    &build,
                    program,
                    provenance,
                    &payload,
                    &expected,
                    &applicability(),
                    &mut TypeWorkBudget::default()
                )
                .is_ok()
            );
        });
    }

    #[test]
    fn checked_admission_payload_facts_mapping_and_target_substitutions_refuse() {
        with_program(SOURCE, |program, provenance| {
            let mut build = super::super::image::encode_effect_for_build(
                program,
                provenance,
                super::super::host::NATIVE_TARGET,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            let mut payload = build
                .image
                .encode_bytes(&mut TypeWorkBudget::default())
                .unwrap();
            let mut expected = build
                .image
                .encode_native_expectations(&mut TypeWorkBudget::default())
                .unwrap();
            assert!(
                PassivePlan::admit(
                    &build,
                    program,
                    provenance,
                    &payload,
                    &expected,
                    &applicability(),
                    &mut TypeWorkBudget::default()
                )
                .is_ok()
            );
            payload[0] ^= 1;
            assert!(matches!(
                PassivePlan::admit(
                    &build,
                    program,
                    provenance,
                    &payload,
                    &expected,
                    &applicability(),
                    &mut TypeWorkBudget::default()
                ),
                Err(Failure::Association)
            ));
            payload[0] ^= 1;
            expected[0] ^= 1;
            assert!(matches!(
                PassivePlan::admit(
                    &build,
                    program,
                    provenance,
                    &payload,
                    &expected,
                    &applicability(),
                    &mut TypeWorkBudget::default()
                ),
                Err(Failure::Association)
            ));
            expected[0] ^= 1;
            let index = build.bridges[0].symbol_index;
            build.bridges[0].symbol_index = u32::MAX;
            assert!(matches!(
                PassivePlan::admit(
                    &build,
                    program,
                    provenance,
                    &payload,
                    &expected,
                    &applicability(),
                    &mut TypeWorkBudget::default()
                ),
                Err(Failure::Association)
            ));
            build.bridges[0].symbol_index = index;
            let mut wrong = applicability();
            wrong.target = "not-the-target";
            assert!(matches!(
                PassivePlan::admit(
                    &build,
                    program,
                    provenance,
                    &payload,
                    &expected,
                    &wrong,
                    &mut TypeWorkBudget::default()
                ),
                Err(Failure::Target)
            ));
            wrong = applicability();
            wrong.version = 2;
            assert!(matches!(
                PassivePlan::admit(
                    &build,
                    program,
                    provenance,
                    &payload,
                    &expected,
                    &wrong,
                    &mut TypeWorkBudget::default()
                ),
                Err(Failure::Version)
            ));
            wrong = applicability();
            wrong.mode = Mode::Isolated;
            assert!(matches!(
                PassivePlan::admit(
                    &build,
                    program,
                    provenance,
                    &payload,
                    &expected,
                    &wrong,
                    &mut TypeWorkBudget::default()
                ),
                Err(Failure::Mode)
            ));
        });
    }

    #[test]
    fn checked_admission_genuine_donor_image_and_original_bridge_refuse() {
        with_program(SOURCE, |program, provenance| {
            let mut build = super::super::image::encode_effect_for_build(
                program,
                provenance,
                super::super::host::NATIVE_TARGET,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            let payload = build
                .image
                .encode_bytes(&mut TypeWorkBudget::default())
                .unwrap();
            let expected = build
                .image
                .encode_native_expectations(&mut TypeWorkBudget::default())
                .unwrap();
            assert!(
                PassivePlan::admit(
                    &build,
                    program,
                    provenance,
                    &payload,
                    &expected,
                    &applicability(),
                    &mut TypeWorkBudget::default()
                )
                .is_ok()
            );
            with_program(
                &SOURCE.replace("42", "43"),
                |donor_program, donor_provenance| {
                    let mut donor = super::super::image::encode_effect_for_build(
                        donor_program,
                        donor_provenance,
                        super::super::host::NATIVE_TARGET,
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
                    std::mem::swap(&mut build.image, &mut donor.image);
                    let donor_expected = build
                        .image
                        .encode_native_expectations(&mut TypeWorkBudget::default())
                        .unwrap();
                    assert!(matches!(
                        PassivePlan::admit(
                            &build,
                            program,
                            provenance,
                            &payload,
                            &donor_expected,
                            &applicability(),
                            &mut TypeWorkBudget::default()
                        ),
                        Err(Failure::Association)
                    ));
                    std::mem::swap(&mut build.image, &mut donor.image);
                    std::mem::swap(&mut build.bridges[0].plan, &mut donor.bridges[0].plan);
                    assert!(matches!(
                        PassivePlan::admit(
                            &build,
                            program,
                            provenance,
                            &payload,
                            &expected,
                            &applicability(),
                            &mut TypeWorkBudget::default()
                        ),
                        Err(Failure::Association)
                    ));
                    std::mem::swap(&mut build.bridges[0].plan, &mut donor.bridges[0].plan);
                },
            );
            build.bridges.pop();
            assert!(matches!(
                PassivePlan::admit(
                    &build,
                    program,
                    provenance,
                    &payload,
                    &expected,
                    &applicability(),
                    &mut TypeWorkBudget::default()
                ),
                Err(Failure::Association)
            ));
        });
    }

    #[test]
    fn checked_admission_public_driver_refuses_checked_preparation_separately() {
        let source = format!(
            "{}\nmain : Unit -> Foreign.CheckedScope<Int, Unit, Unit>\nmain () = run ()\n",
            include_str!("../../tests/fixtures/checked-owner-lifecycle/owner.ash")
        );
        with_driver_result(&source, |result| {
            let error = match result {
                Err(error) => error,
                Ok(_) => panic!("default public preparation must remain refused"),
            };
            assert!(matches!(error.pipeline_failure(),
                Some(crate::driver::PipelineFailure::Resolution(diagnostic))
                    if diagnostic.reason == crate::resolve::ResolveReason::ForeignContract));
        });
    }

    #[test]
    fn checked_admission_checked_owner_public_build_gate_remains_closed() {
        let (program, provenance) = crate::elaborate::checked_owner_passive_program();
        // Genuine checked Core precedes this LATER public-build guard. The
        // default driver's earlier preparation refusal is a distinct control.
        assert!(
            program
                .registry()
                .source_resource_facts()
                .any(|fact| fact.host.is_some())
        );
        assert!(matches!(
            super::super::image::encode_effect_for_build(
                &program,
                &provenance,
                super::super::host::NATIVE_TARGET,
                &mut TypeWorkBudget::default()
            ),
            Err(super::super::image::NativeImageFailure::Image(
                super::super::image::ImageFailure::Unsupported(_)
            ))
        ));
    }
}
