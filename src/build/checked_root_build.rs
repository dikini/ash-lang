//! Owned compile/link transaction for the canonical safe binary root and leaf.
//! The returned artifact and request are observations, never startup authority.
use super::{
    checked_receipt::{ProducerReceiptLimits, ReceiptFailure, ReceiptSeed},
    checked_root_project::Project,
};
use crate::{
    core::ValidatedEffectProgram, module::ModuleId, source::SourceFile, types::TypeWorkBudget,
};
use std::{
    fs,
    path::{Path, PathBuf},
    sync::Arc,
};

pub(super) struct Request<'a> {
    pub program: &'a ValidatedEffectProgram,
    pub provenance: &'a [(ModuleId, Arc<SourceFile>)],
    /// Fresh, nonexistent generated-package path within the owned transaction.
    pub project: PathBuf,
    pub target: &'a Path,
    pub output: &'a Path,
    pub native: super::checked_native_build::Request<'a>,
    pub receipt: ProducerReceiptLimits,
    pub policy: crate::foreign::source_runtime::CheckedOwnerLimits,
}

pub(super) struct Artifact {
    pub executable: PathBuf,
    pub receipt: PathBuf,
    pub request: PathBuf,
    pub project: PathBuf,
}

fn input<T>(r: std::io::Result<T>) -> Result<T, ReceiptFailure> {
    r.map_err(|_| ReceiptFailure::Input)
}
fn project_error(e: super::checked_root_identity::Failure) -> ReceiptFailure {
    match e {
        super::checked_root_identity::Failure::Resource => ReceiptFailure::Resource,
        _ => ReceiptFailure::Association,
    }
}

fn child(root: &Path, name: &str, work: &mut TypeWorkBudget) -> Result<PathBuf, ReceiptFailure> {
    let bytes = root
        .as_os_str()
        .len()
        .checked_add(name.len())
        .and_then(|n| n.checked_add(1))
        .ok_or(ReceiptFailure::Resource)?;
    // PathBuf::join may copy the root again while extending its allocation.
    work.charge(
        bytes
            .checked_mul(2)
            .and_then(|n| n.checked_add(64))
            .ok_or(ReceiptFailure::Resource)?,
    )
    .map_err(|()| ReceiptFailure::Resource)?;
    Ok(root.join(name))
}

/// Uses the existing owned Cargo and linker observers. No resulting executable
/// or selected helper function is started. Failed output never replaces an old
/// destination, and publication follows root cleanup and receipt admission.
pub(super) fn compile(request: Request<'_>) -> Result<Artifact, ReceiptFailure> {
    let mut work = TypeWorkBudget::with_limit(request.receipt.work);
    let output_bytes = request.output.as_os_str().len();
    if output_bytes > 4096 {
        return Err(ReceiptFailure::Resource);
    }
    work.charge(
        output_bytes
            .checked_mul(4)
            .and_then(|n| n.checked_add(64))
            .ok_or(ReceiptFailure::Resource)?,
    )
    .map_err(|()| ReceiptFailure::Resource)?;
    if !request.output.is_absolute()
        || request.output.file_name().is_none()
        || request
            .output
            .to_str()
            .is_none_or(|s| s.chars().any(char::is_control))
        || request.output.components().any(|p| {
            matches!(
                p,
                std::path::Component::ParentDir | std::path::Component::CurDir
            )
        })
    {
        return Err(ReceiptFailure::Association);
    }
    let output = request.output.to_path_buf();
    let build = super::image::encode_checked_preparation(
        request.program,
        request.provenance,
        super::host::NATIVE_TARGET,
        &mut work,
    )
    .map_err(super::checked_request::native_image_error)?;
    let emission =
        super::emit::checked_root_host(&build, request.program, request.policy, &mut work)
            .map_err(super::checked_request::emission_error)?;
    let native_limits = request.native.limits;
    let mut native = super::checked_native_build::NativeBuild::build(&build, request.native)?;
    let project = Project::create(
        request.project,
        &emission.leaf.source,
        &emission.host.rust_source,
        &mut work,
    )
    .map_err(project_error)?;
    let root = project.root();
    if root.as_os_str().len() > 4096 || native.archive().as_os_str().len() > 4096 {
        return Err(ReceiptFailure::Resource);
    }
    work.charge(
        root.as_os_str()
            .len()
            .checked_add(64)
            .ok_or(ReceiptFailure::Resource)?,
    )
    .map_err(|()| ReceiptFailure::Resource)?;
    let artifact_project = root.to_owned();
    input(fs::create_dir(child(root, "src", &mut work)?))?;
    let (image, facts) = emission.host.payloads.bytes();
    let policy = emission
        .host
        .payloads
        .checked_policy()
        .ok_or(ReceiptFailure::Association)?;
    work.charge(
        image
            .len()
            .checked_add(facts.len())
            .and_then(|n| n.checked_add(policy.len()))
            .ok_or(ReceiptFailure::Resource)?,
    )
    .map_err(|()| ReceiptFailure::Resource)?;
    for (name, bytes) in [
        ("program-image.bin", image),
        ("expected-facts.bin", facts),
        ("checked-policy.bin", policy),
    ] {
        work.charge(name.len() + 4)
            .map_err(|()| ReceiptFailure::Resource)?;
        let relative = format!("src/{name}");
        input(fs::write(child(root, &relative, &mut work)?, bytes))?;
    }
    let log = child(root, "native-build.log", &mut work)?;
    input(fs::File::create(&log))?;
    let lock_directory = child(root, "lock-cargo", &mut work)?;
    input(fs::create_dir(&lock_directory))?;
    let mut settle = project
        .settle_lock_command(&mut work)
        .map_err(project_error)?;
    let status = super::checked_native_build::run_root_cargo(
        &mut settle,
        &lock_directory,
        &log,
        native_limits.link,
        &mut work,
    )?;
    if !status.success() {
        return Err(ReceiptFailure::Input);
    }
    let data = project
        .snapshot(&emission.leaf.source, &emission.host.rust_source, &mut work)
        .map_err(project_error)?;
    let identity = data
        .reconstruct(&emission.leaf.source, &emission.host.rust_source, &mut work)
        .map_err(project_error)?;
    // Prepay the bounded serialization before retaining the complete BuildData.
    let configuration_bound = data
        .manifest
        .len()
        .checked_add(data.build_configuration.len())
        .and_then(|n| n.checked_add(data.settled_lock.len()))
        .and_then(|n| n.checked_add(data.leaf_manifest.len()))
        .and_then(|n| n.checked_add(data.leaf.len()))
        .and_then(|n| n.checked_add(data.shim.len()))
        .and_then(|n| n.checked_add(data.project_root.as_os_str().len()))
        .and_then(|n| n.checked_add(1024))
        .and_then(|n| n.checked_mul(8))
        .ok_or(ReceiptFailure::Resource)?;
    work.charge(configuration_bound)
        .map_err(|()| ReceiptFailure::Resource)?;
    let configuration = serde_json::to_vec(&data).map_err(|_| ReceiptFailure::Resource)?;
    if configuration.len() > configuration_bound {
        return Err(ReceiptFailure::Resource);
    }
    let mut seed = ReceiptSeed::from_root_emission(
        &build,
        request.program,
        request.provenance,
        &emission.host,
        &configuration,
        request.receipt,
        (&identity, request.policy),
    )?;
    let configuration_paths = [
        child(root, "Cargo.toml", &mut work)?,
        child(root, "rust-toolchain.toml", &mut work)?,
        child(root, "Cargo.lock", &mut work)?,
    ];
    seed.observe_configuration(&configuration_paths)?;
    work.charge(
        native
            .archive()
            .as_os_str()
            .len()
            .checked_add(64)
            .ok_or(ReceiptFailure::Resource)?,
    )
    .map_err(|()| ReceiptFailure::Resource)?;
    let inputs = [super::host::NativeLinkInput::StaticArchive(
        native.archive().to_owned(),
    )];
    seed.observe_native_inputs(&inputs)?;
    let mut capture = super::checked_link::Capture::prepare(root, native_limits.link, &inputs)?;
    let mut command = project
        .compile_command(request.target, &capture.linker(), &mut work)
        .map_err(project_error)?;
    for i in &inputs {
        work.charge(
            i.path()
                .as_os_str()
                .len()
                .checked_add(16)
                .and_then(|n| n.checked_mul(2))
                .ok_or(ReceiptFailure::Resource)?,
        )
        .map_err(|()| ReceiptFailure::Resource)?;
        let mut argument = std::ffi::OsString::from("link-arg=");
        argument.push(i.path());
        command.arg("-C").arg(argument);
    }
    native.verify()?;
    let status = capture.run_cargo(&mut command, &log);
    let receipt_path = child(root, "producer-receipt.bin", &mut work)?;
    let request_path = child(root, "applicability-request.json", &mut work)?;
    let mut result = Ok(());
    let mut state = (capture, work);
    let finished = super::artifacts::GeneratedArtifacts {
        project: root,
        target_directory: request.target,
        package_name: "ash-checked-owner-root",
        target: super::host::NATIVE_TARGET,
        profile: "dev",
        private_target: false,
    }
    .finish_with_state(
        status.as_ref().is_ok_and(|s| s.success()),
        &output,
        &log,
        &mut state,
        (
            |linked, (capture, _)| {
                capture
                    .capture(linked)
                    .map_err(|e| std::io::Error::other(format!("root capture: {e:?}")))
            },
            |_, (capture, work), log| {
                let mut clean = project.clean_command(request.target, work).map_err(|e| {
                    std::io::Error::other(format!("root clean configuration: {e:?}"))
                })?;
                if capture.run_cargo(&mut clean, log)?.success() {
                    Ok(())
                } else {
                    Err(std::io::Error::other("root cleanup failed"))
                }
            },
            |linked, (capture, work)| {
                result = (|| {
                    let after = project
                        .snapshot(&emission.leaf.source, &emission.host.rust_source, work)
                        .map_err(project_error)?;
                    work.charge(configuration_bound)
                        .map_err(|()| ReceiptFailure::Resource)?;
                    if serde_json::to_vec(&after).map_err(|_| ReceiptFailure::Resource)?
                        != configuration
                    {
                        return Err(ReceiptFailure::Association);
                    }
                    seed.verify_emitted_files(&[
                        child(root, "root-shim.rs", work)?,
                        child(root, "src/program-image.bin", work)?,
                        child(root, "src/expected-facts.bin", work)?,
                    ])?;
                    seed.verify_native_inputs(&inputs)?;
                    seed.verify_settled_configuration(&configuration_paths)?;
                    let n = native.finish(seed.receipt())?;
                    seed.bind_native_build(&n, native_limits)?;
                    native.validate_receipt(&n, seed.receipt())?;
                    let l = capture.finish(seed.receipt(), linked)?;
                    seed.bind_root_link(&l, native_limits.link)?;
                    let receipt =
                        seed.finalize_with_root_link(linked, Some((&l, native_limits.link)))?;
                    let request_bytes = super::checked_request::encode_root(
                        [
                            &receipt,
                            image,
                            facts,
                            policy,
                            emission.host.rust_source.as_bytes(),
                        ],
                        Some((&n, &l, native_limits)),
                        data,
                        super::checked_request::RequestLimits::default(),
                        work,
                    )?;
                    input(fs::write(child(root, "native-provenance.json", work)?, n))?;
                    input(fs::write(child(root, "link-provenance.json", work)?, l))?;
                    input(fs::write(&receipt_path, receipt))?;
                    input(fs::write(&request_path, request_bytes))?;
                    Ok(())
                })();
                result.map_err(|e| std::io::Error::other(format!("root receipt: {e:?}")))
            },
        ),
    );
    if !input(status)?.success() {
        return Err(ReceiptFailure::Input);
    }
    result?;
    finished.map_err(|_| ReceiptFailure::Input)?;
    if !output.is_file() {
        return Err(ReceiptFailure::Input);
    }
    Ok(Artifact {
        executable: output,
        receipt: receipt_path,
        request: request_path,
        project: artifact_project,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "assigned generated canonical-root/leaf compile-link slot; output is never executed"]
    fn genuine_root_and_leaf_compile_link_matches_receipt_without_startup() {
        let target =
            PathBuf::from(std::env::var_os("CARGO_TARGET_DIR").expect("explicit shared cache"));
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = target.join(format!(
            "checked-root-compile-{}-{nonce}",
            std::process::id()
        ));
        use std::os::unix::fs::DirBuilderExt;
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
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
        let (program, provenance) = crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
        );
        // Same explicit private observation profile as the retained actual
        // static-link gate. This is not a startup/default-work allowance.
        let receipt_limits = ProducerReceiptLimits {
            artifact_bytes: 2 * 1024 * 1024 * 1024,
            receipt_bytes: 4096,
            records: 64,
            work: 64 * 1024 * 1024 * 1024,
        };
        let limits = super::super::checked_native_build::Limits {
            file_bytes: 128 * 1024 * 1024,
            total_bytes: 4 * 1024 * 1024,
            output_bytes: 256 * 1024,
            paths: 128,
            record_bytes: 128 * 1024,
            command_seconds: 30,
            work: 2 * 1024 * 1024 * 1024,
            link: super::super::checked_link::Limits {
                file_bytes: 2 * 1024 * 1024 * 1024,
                total_bytes: 4 * 1024 * 1024 * 1024,
                map_bytes: 128 * 1024 * 1024,
                output_bytes: 1024 * 1024,
                record_bytes: 1024 * 1024,
                paths: 2048,
                arguments: 65536,
                seconds: 120,
                cargo_bytes: 16 * 1024 * 1024,
                cargo_seconds: 1800,
                work: 16 * 1024 * 1024 * 1024,
            },
        };
        let artifact = compile(Request {
            program: &program,
            provenance: &provenance,
            project: directory.join("root"),
            target: &target,
            output: &directory.join("program"),
            native: super::super::checked_native_build::Request {
                source: &directory.join("owner.c"),
                header: &directory.join("owner.h"),
                directory: &directory.join("inputs"),
                limits,
            },
            receipt: receipt_limits,
            policy: crate::foreign::source_runtime::CheckedOwnerLimits {
                groups: 1,
                owners: 1,
                pending: 1,
                observations: 5,
                history: 6,
                continuations: 1,
            },
        })
        .unwrap();
        let raw_receipt = fs::read(&artifact.receipt).unwrap();
        let receipt =
            super::super::checked_receipt::ProducerReceipt::decode(&raw_receipt, receipt_limits)
                .unwrap();
        let request = fs::read(&artifact.request).unwrap();
        let decoded = super::super::checked_request::ApplicabilityRequest::decode(
            &request,
            super::super::checked_request::RequestLimits::default(),
        )
        .unwrap();
        assert!(decoded.linked());
        assert_eq!(decoded.missing_fields().len(), 6);
        assert_eq!(
            decoded.check_complete(),
            Err(ReceiptFailure::IncompleteClosure)
        );
        assert_eq!(
            receipt.activate(),
            Err(ReceiptFailure::ProtectedAuthorityUnavailable)
        );
        use sha2::{Digest, Sha256};
        let elf = fs::read(&artifact.executable).unwrap();
        assert_eq!(
            receipt.pin(super::super::checked_receipt::ReceiptField::FinalElf),
            Some(super::super::checked_receipt::ArtifactPin {
                bytes: elf.len() as u64,
                sha256: Sha256::digest(&elf).into(),
            })
        );
        assert_eq!(&elf[..4], b"\x7fELF");
        let record: serde_json::Value = serde_json::from_slice(&request).unwrap();
        let data: super::super::checked_root_project::BuildData =
            serde_json::from_value(record["root_build"].clone()).unwrap();
        let identity = data
            .reconstruct(
                std::str::from_utf8(&data.leaf).unwrap(),
                std::str::from_utf8(&data.shim).unwrap(),
                &mut TypeWorkBudget::with_limit(receipt_limits.work),
            )
            .unwrap();
        assert!(elf.windows(32).any(|bytes| bytes == identity.bytes()));
        let manifest = String::from_utf8(data.manifest).unwrap();
        assert!(manifest.contains("src/lib.rs"));
        assert!(!manifest.contains("foreign-adapter"));
        assert!(manifest.contains("ash-trusted-preparation"));
        let leaf = fs::read_to_string(artifact.project.join("leaf/src/lib.rs")).unwrap();
        assert!(leaf.contains("pub struct Owner"));
        assert!(!leaf.contains("impl Drop"));
        // Build a fresh coherent native observation for the donor rather than
        // changing a source behind an old pin. Header/prototype compilation
        // still succeeds; only the selected release definition is absent.
        let missing = directory.join("missing-release");
        fs::create_dir(&missing).unwrap();
        let source = include_str!("../../tests/fixtures/checked-owner-runtime/owner.c");
        assert_eq!(source.matches("void ash_checked_owner_release(").count(), 1);
        fs::write(
            missing.join("owner.c"),
            source.replace(
                "void ash_checked_owner_release(",
                "void ash_checked_owner_release_missing(",
            ),
        )
        .unwrap();
        fs::write(
            missing.join("owner.h"),
            include_bytes!("../../tests/fixtures/checked-owner-runtime/owner.h"),
        )
        .unwrap();
        let refused = compile(Request {
            program: &program,
            provenance: &provenance,
            project: missing.join("root"),
            target: &target,
            output: &missing.join("program"),
            native: super::super::checked_native_build::Request {
                source: &missing.join("owner.c"),
                header: &missing.join("owner.h"),
                directory: &missing.join("inputs"),
                limits,
            },
            receipt: receipt_limits,
            policy: crate::foreign::source_runtime::CheckedOwnerLimits {
                groups: 1,
                owners: 1,
                pending: 1,
                observations: 5,
                history: 6,
                continuations: 1,
            },
        });
        assert!(matches!(refused, Err(ReceiptFailure::Input)));
        let link_error =
            fs::read_to_string(missing.join("root/checked-link/cargo-0/cargo.stderr")).unwrap();
        assert!(
            link_error.contains("undefined reference")
                && link_error.contains("ash_checked_owner_release"),
            "{link_error}"
        );
        assert!(!missing.join("program").exists());
        assert!(!missing.join("root/producer-receipt.bin").exists());
        fs::write(directory.join("observation.json"),serde_json::to_vec_pretty(&serde_json::json!({
            "purpose":"actual canonical-root/leaf compilation and static link; no output startup",
            "executable":artifact.executable,"receipt":artifact.receipt,"request":artifact.request,"project":artifact.project,
            "six_missing":true,"protected_positive":false,"selected_callbacks_executed":false,
            "missing_release":"fresh native closure reaches actual unresolved-symbol root link failure",
        })).unwrap()).unwrap();
        println!(
            "actual generated root compile retained at {}",
            directory.display()
        );
    }
}
