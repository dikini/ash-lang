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

pub(super) struct LauncherRequest<'a> {
    /// Fresh observation directory, not another Cargo package or target cache.
    pub directory: &'a Path,
    pub target: &'a Path,
    pub output: &'a Path,
    pub limits: super::checked_link::Limits,
    pub work: usize,
}
pub(super) struct LauncherArtifact {
    pub executable: PathBuf,
    pub configuration: PathBuf,
    pub provenance: PathBuf,
}
#[derive(serde::Serialize)]
struct LauncherInput {
    path: PathBuf,
    bytes: u64,
    sha256: [u8; 32],
}
#[derive(serde::Serialize)]
struct LauncherConfiguration<'a> {
    version: u32,
    role: &'static str,
    source_component: &'static str,
    compiler: &'static str,
    environment: &'a super::checked_root_environment::Environment,
    inputs: Vec<LauncherInput>,
    arguments: Vec<String>,
}
fn launcher_configuration(environment: &super::checked_root_environment::Environment,
    command: &std::process::Command, limits: super::checked_link::Limits,
    work: &mut TypeWorkBudget) -> Result<Vec<u8>, ReceiptFailure> {
    let canonical = Path::new(env!("ASH_RUNTIME_CANONICAL_SOURCE_ROOT"));
    environment.verify(canonical, work).map_err(project_error)?;
    if cfg!(feature = "resource-calibration") || env!("ASH_RUNTIME_CARGO_PROFILE") != "debug"
        || env!("ASH_RUNTIME_OPT_LEVEL") != "0" || !cfg!(debug_assertions) || cfg!(panic = "abort") {
        return Err(ReceiptFailure::Association);
    }
    let fixed: [(&str, &[u8]); 6] = [
        ("Cargo.toml", include_bytes!("../../Cargo.toml")),
        ("Cargo.lock", include_bytes!("../../Cargo.lock")),
        ("rust-toolchain.toml", include_bytes!("../../rust-toolchain.toml")),
        ("trusted-preparation/Cargo.toml", include_bytes!("../../trusted-preparation/Cargo.toml")),
        ("trusted-preparation/src/bootstrap_association.rs", include_bytes!("../../trusted-preparation/src/bootstrap_association.rs")),
        ("trusted-preparation/src/bin/ash-checked-launcher.rs", include_bytes!("../../trusted-preparation/src/bin/ash-checked-launcher.rs")),
    ];
    work.charge(8 * std::mem::size_of::<LauncherInput>()).map_err(|()| ReceiptFailure::Resource)?;
    let mut inputs = Vec::new();
    inputs.try_reserve_exact(8).map_err(|_| ReceiptFailure::Resource)?;
    for (name, expected) in fixed {
        let path = child(canonical, name, work)?;
        let actual = super::checked_receipt::observe_file(&path, limits.file_bytes, work)?;
        if actual != super::checked_receipt::pin(expected, work)? { return Err(ReceiptFailure::Association); }
        inputs.push(LauncherInput { path, bytes: actual.bytes, sha256: actual.sha256 });
    }
    for path in [&environment.cargo, &environment.rustc] {
        work.charge(path.as_os_str().len()).map_err(|()| ReceiptFailure::Resource)?;
        let observed = super::checked_receipt::observe_file(path, limits.file_bytes, work)?;
        inputs.push(LauncherInput { path: path.clone(), bytes: observed.bytes, sha256: observed.sha256 });
    }
    let count = command.get_args().count();
    work.charge(count.checked_mul(std::mem::size_of::<String>()).ok_or(ReceiptFailure::Resource)?)
        .map_err(|()| ReceiptFailure::Resource)?;
    let mut arguments = Vec::new();
    arguments.try_reserve_exact(count).map_err(|_| ReceiptFailure::Resource)?;
    for arg in command.get_args() {
        let text = arg.to_str().ok_or(ReceiptFailure::Association)?;
        work.charge(text.len()).map_err(|()| ReceiptFailure::Resource)?;
        arguments.push(text.to_owned());
    }
    // Bound integer-array escaping and every path/configuration/argument before
    // serialization, including a maximally populated admitted Cargo config.
    let raw = environment.configurations.iter().try_fold(4096usize, |n, c|
        n.checked_add(c.path.as_os_str().len())?.checked_add(c.bytes.len()))
        .and_then(|n| n.checked_add(environment.cargo.as_os_str().len()))
        .and_then(|n| n.checked_add(environment.rustc.as_os_str().len()))
        .and_then(|n| n.checked_add(environment.cargo_home.as_os_str().len()))
        .and_then(|n| n.checked_add(environment.rustup_home.as_os_str().len()))
        .ok_or(ReceiptFailure::Resource)?;
    let raw = inputs.iter().try_fold(raw, |n, p| n.checked_add(p.path.as_os_str().len())?.checked_add(512))
        .ok_or(ReceiptFailure::Resource)?;
    let bound = arguments.iter().try_fold(raw, |n, a| n.checked_add(a.len())?.checked_add(16))
        .and_then(|n| n.checked_mul(6)).ok_or(ReceiptFailure::Resource)?;
    if bound > limits.record_bytes { return Err(ReceiptFailure::Resource); }
    let bytes = super::checked_request::json_bytes(&LauncherConfiguration { version: 1,
        role: "trusted-static-launcher", source_component: env!("ASH_RUNTIME_SOURCE_COMPONENT"),
        compiler: env!("ASH_RUNTIME_COMPILER_ID"), environment, inputs, arguments }, bound, work)?;
    if bytes.len() > bound { return Err(ReceiptFailure::Resource); }
    Ok(bytes)
}

/// Build the existing fixed launcher without running it. Uses the same closed
/// Cargo environment, owned process runner, BFD observation and cleanup-before-
/// publication path as the generated root. No native archive is supplied.
pub(super) fn compile_launcher(request: LauncherRequest<'_>) -> Result<LauncherArtifact, ReceiptFailure> {
    request.limits.validate()?;
    let mut work = TypeWorkBudget::with_limit(request.work);
    let canonical = Path::new(env!("ASH_RUNTIME_CANONICAL_SOURCE_ROOT"));
    let environment = super::checked_root_environment::Environment::discover(canonical, &mut work)
        .map_err(project_error)?;
    // Validate output/cache/observation paths before IO.
    for path in [request.directory, request.target, request.output] {
        super::checked_root_environment::argument_path(path, &mut work).map_err(project_error)?;
    }
    if request.output.file_name().is_none() { return Err(ReceiptFailure::Association); }
    work.charge(request.output.as_os_str().len()).map_err(|()| ReceiptFailure::Resource)?;
    use std::os::unix::fs::DirBuilderExt;
    input(fs::DirBuilder::new().mode(0o700).create(request.directory))?;
    let log = child(request.directory, "launcher-build.log", &mut work)?;
    input(fs::File::create(&log))?;
    let mut capture = super::checked_link::Capture::prepare_launcher(request.directory, request.limits)?;
    let mut command = environment.launcher_command(canonical, request.target, &capture.linker(), &mut work)
        .map_err(project_error)?;
    let configuration = launcher_configuration(&environment, &command, request.limits, &mut work)?;
    let status = capture.run_cargo(&mut command, &log);
    let configuration_path = child(request.directory, "launcher-configuration.json", &mut work)?;
    let provenance_path = child(request.directory, "launcher-provenance.json", &mut work)?;
    let executable = request.output.to_owned();
    let mut result = Ok(());
    let mut state = (capture, work);
    let finished = super::artifacts::GeneratedArtifacts { project: request.directory,
        target_directory: request.target, package_name: "ash-checked-launcher",
        target: super::host::NATIVE_TARGET, profile: "dev", private_target: false }
        .finish_with_state(status.as_ref().is_ok_and(|s| s.success()), request.output, &log,
            &mut state, (
                |linked, (capture, _)| capture.capture(linked)
                    .map_err(|e| std::io::Error::other(format!("launcher capture: {e:?}"))),
                |_, (capture, work), log| {
                    let mut clean = environment.launcher_clean_command(canonical, request.target, work)
                        .map_err(|e| std::io::Error::other(format!("launcher clean: {e:?}")))?;
                    if capture.run_cargo(&mut clean, log)?.success() { Ok(()) }
                    else { Err(std::io::Error::other("launcher cleanup failed")) }
                },
                |linked, (capture, work)| {
                    result = (|| {
                        let after = launcher_configuration(&environment, &command, request.limits, work)?;
                        work.charge(configuration.len()).map_err(|()| ReceiptFailure::Resource)?;
                        if after != configuration { return Err(ReceiptFailure::Association); }
                        let provenance = capture.finish_launcher(&configuration, linked)?;
                        let observed = super::checked_link::launcher_matches(&provenance, &configuration, request.limits, work)?;
                        if super::checked_receipt::observe_static_image(linked, request.limits.file_bytes, work)? != observed {
                            return Err(ReceiptFailure::Association);
                        }
                        input(fs::write(&configuration_path, &configuration))?;
                        input(fs::write(&provenance_path, provenance))?;
                        Ok(())
                    })();
                    result.map_err(|e| std::io::Error::other(format!("launcher provenance: {e:?}")))
                },
            ));
    if !input(status)?.success() { return Err(ReceiptFailure::Input); }
    result?;
    finished.map_err(|_| ReceiptFailure::Input)?;
    Ok(LauncherArtifact { executable, configuration: configuration_path, provenance: provenance_path })
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
    #[ignore = "assigned existing-cache static launcher compile/link slot; output is never executed"]
    fn genuine_fixed_launcher_compile_link_has_separate_provenance_without_startup() {
        let target = PathBuf::from(std::env::var_os("CARGO_TARGET_DIR").expect("explicit existing shared cache"));
        let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let directory = target.join(format!("checked-launcher-compile-{}-{nonce}", std::process::id()));
        let output = directory.join("ash-checked-launcher");
        let limits = super::super::checked_link::Limits {
            file_bytes: 2 * 1024 * 1024 * 1024, total_bytes: 4 * 1024 * 1024 * 1024,
            map_bytes: 256 * 1024 * 1024, output_bytes: 1024 * 1024,
            record_bytes: 1024 * 1024, paths: 2048, arguments: 65536,
            seconds: 120, cargo_bytes: 16 * 1024 * 1024, cargo_seconds: 1800,
            work: 16 * 1024 * 1024 * 1024,
        };
        let artifact = compile_launcher(LauncherRequest { directory: &directory, target: &target,
            output: &output, limits, work: 16 * 1024 * 1024 * 1024 }).unwrap();
        let configuration = fs::read(&artifact.configuration).unwrap();
        let provenance = fs::read(&artifact.provenance).unwrap();
        super::super::checked_link::exercise_launcher_data_for_test(&provenance, &configuration, limits);
        let actual = super::super::checked_receipt::observe_static_image(&artifact.executable,
            limits.file_bytes, &mut TypeWorkBudget::with_limit(limits.work)).unwrap();
        assert_eq!(super::super::checked_link::launcher_matches(&provenance, &configuration, limits,
            &mut TypeWorkBudget::with_limit(limits.work)).unwrap(), actual);
        assert!(!directory.join("linked-program").exists());
        let config: serde_json::Value = serde_json::from_slice(&configuration).unwrap();
        assert_eq!(config["role"], "trusted-static-launcher");
        assert!(config["arguments"].as_array().unwrap().iter().any(|a| a == "ash-checked-launcher"));
        assert!(!String::from_utf8(configuration).unwrap().contains("ash_checked_owner_root"));
        println!("unexecuted fixed launcher compile retained at {}", directory.display());
    }

    #[test]
    #[ignore = "assigned generated canonical-root/leaf compile-link slot; output is never executed"]
    fn genuine_root_and_leaf_compile_link_matches_receipt_without_startup() {
        check_generated_compile_link(
            include_str!("../../tests/fixtures/checked-owner-runtime/owner.c"),
            include_bytes!("../../tests/fixtures/checked-owner-runtime/owner.h"),
            include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
            "void ash_checked_owner_release(", "ash_checked_owner_release", "initialized-byte",
        );
    }

    #[test]
    #[ignore = "assigned two-role generated root/leaf compile-link slot; output is never executed"]
    fn genuine_output_status_root_and_leaf_compile_link_matches_receipt_without_startup() {
        check_generated_compile_link(
            include_str!("../../tests/fixtures/checked-owner-runtime/output-status.c"),
            include_bytes!("../../tests/fixtures/checked-owner-runtime/output-status.h"),
            include_str!("../../tests/fixtures/checked-owner-lifecycle/output-status.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Int, Unit, Unit>\nmain () = Producer.run ()\n",
            "int sqlite3_close(", "sqlite3_close", "independent-output-status",
        );
    }

    fn check_generated_compile_link(native_source: &str, native_header: &[u8], producer: &str, entry: &str,
        release_definition: &str, release_name: &str, profile: &str) {
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
            native_source,
        )
        .unwrap();
        fs::write(
            directory.join("owner.h"),
            native_header,
        )
        .unwrap();
        let (program, provenance) = crate::elaborate::checked_owner_passive_program_for_source(
            producer, entry,
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
                // Connected evaluator/provider map measured 157,968,330 B in
                // passive relink 58055; supported 256 MiB leaves 41.15% headroom.
                // This selects a fixture observation bound, not a product max.
                map_bytes: 256 * 1024 * 1024,
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
        if profile == "initialized-byte" {
            super::super::checked_request::exercise_complete_closure_assembly_for_test(&request);
        }
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
        // Canonical linked admission precedes both donor controls. These are
        // untrusted DATA rewrites over this same real build, not new approvals.
        let record: serde_json::Value = serde_json::from_slice(&request).unwrap();
        let request_limits = super::super::checked_request::RequestLimits::default();
        let configuration_field = super::super::checked_receipt::ReceiptField::BuildConfiguration;
        let mut wrong_final = receipt.pin(configuration_field).unwrap();
        wrong_final.sha256[0] ^= 1;
        let replaced = receipt.substituted_configuration_data_for_test(wrong_final)
            .encode(&mut TypeWorkBudget::with_limit(receipt_limits.work), receipt_limits).unwrap();
        let mut donor = record.clone();
        donor["parts"][0]["bytes"] = serde_json::json!(replaced);
        assert!(matches!(super::super::checked_request::ApplicabilityRequest::decode(
            &serde_json::to_vec(&donor).unwrap(), request_limits,
        ), Err(ReceiptFailure::Association)));

        let mut setup = TypeWorkBudget::with_limit(receipt_limits.work);
        let native_bytes: Vec<u8> = serde_json::from_value(record["parts"][5]["bytes"].clone()).unwrap();
        let link_bytes: Vec<u8> = serde_json::from_value(record["parts"][6]["bytes"].clone()).unwrap();
        let mut native_data: serde_json::Value = serde_json::from_slice(&native_bytes).unwrap();
        let digest = native_data["configuration_before_binding"]["sha256"][0].as_u64().unwrap();
        native_data["configuration_before_binding"]["sha256"][0] = serde_json::json!(digest ^ 1);
        // Restore the actual native schema's canonical field order.
        let native_data: super::super::checked_native_build::Record = serde_json::from_value(native_data).unwrap();
        let native_bytes = serde_json::to_vec(&native_data).unwrap();
        let (wrong_original, observed_native) = super::super::checked_native_build::binding(
            &native_bytes, limits, &mut setup,
        ).unwrap();
        let native_bound = super::super::checked_native_build::configuration_binding(
            wrong_original, observed_native, &mut setup,
        ).unwrap();
        let mut link_data: serde_json::Value = serde_json::from_slice(&link_bytes).unwrap();
        link_data["configuration_before_binding"] = serde_json::json!({
            "bytes": native_bound.bytes, "sha256": native_bound.sha256,
        });
        let link_bytes = serde_json::to_vec(&link_data).unwrap();
        let observed_link = super::super::checked_receipt::pin(&link_bytes, &mut setup).unwrap();
        let final_bound = super::super::checked_link::configuration_binding(native_bound, observed_link, &mut setup).unwrap();
        let donor_receipt = receipt.substituted_configuration_data_for_test(final_bound);
        // Both existing chain proofs pass: only the independent raw BuildData
        // join distinguishes this fully rebound wrong-original configuration.
        let prior = donor_receipt.before_root_link(&link_bytes, limits.link, &mut setup).unwrap();
        super::super::checked_native_build::matches(&native_bytes, &prior, limits, &mut setup).unwrap();
        let raw_receipt = donor_receipt.encode(&mut setup, receipt_limits).unwrap();
        let original_build_data = record["root_build"].clone();
        let mut donor = record.clone();
        donor["parts"][0]["bytes"] = serde_json::json!(raw_receipt);
        donor["parts"][5]["bytes"] = serde_json::json!(native_bytes);
        donor["parts"][6]["bytes"] = serde_json::json!(link_bytes);
        assert_eq!(donor["root_build"], original_build_data);
        assert!(matches!(super::super::checked_request::ApplicabilityRequest::decode(
            &serde_json::to_vec(&donor).unwrap(), request_limits,
        ), Err(ReceiptFailure::Association)));

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
        let leaf_path = super::super::checked_root_project::leaf_source_path(
            std::str::from_utf8(&data.leaf).unwrap(), &mut setup,
        ).unwrap();
        let leaf = fs::read_to_string(artifact.project.join("leaf").join(leaf_path)).unwrap();
        assert_eq!(leaf.as_bytes(), data.leaf);
        assert!(leaf.contains("pub struct Owner"));
        assert!(!leaf.contains("impl Drop"));
        if profile == "independent-output-status" {
            assert!(leaf.contains("pub fn prepare_output_acquire"));
            assert!(leaf.contains("pub fn prepare_teardown"));
            assert!(leaf.contains("#[link_name = \"sqlite3_open_v2\"]"));
            assert!(leaf.contains("#[link_name = \"sqlite3_close\"]"));
        }
        // Build a fresh coherent native observation for the donor rather than
        // changing a source behind an old pin. Header/prototype compilation
        // still succeeds; only the selected release definition is absent.
        let missing = directory.join("missing-release");
        fs::create_dir(&missing).unwrap();
        assert_eq!(native_source.matches(release_definition).count(), 1);
        fs::write(
            missing.join("owner.c"),
            native_source.replace(release_name, &format!("{release_name}_missing")),
        )
        .unwrap();
        fs::write(
            missing.join("owner.h"),
            native_header,
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
                && link_error.contains(release_name),
            "{link_error}"
        );
        assert!(!missing.join("program").exists());
        assert!(!missing.join("root/producer-receipt.bin").exists());
        fs::write(directory.join("observation.json"),serde_json::to_vec_pretty(&serde_json::json!({
            "purpose":"actual canonical-root/leaf compilation and static link; no output startup", "profile":profile,
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
