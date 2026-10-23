//! Native tool invocation for matching-compiler evaluator hosts.

use std::{
    error::Error,
    fmt, fs, io,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
};

use crate::{
    compiler_work::CompilationWork,
    driver::{CompiledProgram, FileFailure, RunConfiguration, compile_path},
    types::TypeWorkBudget,
};

use super::{
    artifacts::{ArtifactFailure, GeneratedArtifacts},
    emit, image,
};

/// The single native target supported by the first program-build slice.
pub const NATIVE_TARGET: &str = "x86_64-unknown-linux-gnu";

/// Explicit native output and tool-cache selection.
#[derive(Debug)]
pub struct BuildConfiguration {
    /// Destination executable. An existing file is replaced only after linking succeeds.
    pub output: PathBuf,
    /// Requested native target; other profiles are refused.
    pub target: String,
    /// Optional shared Cargo cache. No cache is copied into a generated project.
    pub cargo_target_directory: Option<PathBuf>,
    /// Ordered whole-program linker dependencies; these grant no native dispatch authority.
    /// Shared libraries use the caller's ordinary loader configuration; no rpath is added.
    pub native_inputs: Vec<NativeLinkInput>,
    /// Optional bounded producer observations. These are not checked approval;
    /// absent native/header/tool/context closure remains an explicit refusal.
    pub producer_receipt: Option<super::checked_receipt::ProducerReceiptLimits>,
}

impl BuildConfiguration {
    /// Selects the supported host profile and an output executable.
    #[must_use]
    pub fn new(output: PathBuf) -> Self {
        Self {
            output,
            target: NATIVE_TARGET.to_owned(),
            cargo_target_directory: None,
            native_inputs: Vec::new(),
            producer_receipt: None,
        }
    }
}

/// Explicit native linker files for the bounded GNU64 target.
///
/// Order is preserved for the native linker, including archive dependency order.
/// File-kind checks do not certify exported symbols, headers or binary behavior.
#[derive(Clone, Debug)]
pub enum NativeLinkInput {
    /// A regular non-thin `ar` archive. Its members are checked by the linker.
    StaticArchive(PathBuf),
    /// An ordinary ELF64 little-endian x86_64 shared object.
    SharedLibrary(PathBuf),
}
impl NativeLinkInput {
    pub(super) fn path(&self) -> &Path {
        match self {
            Self::StaticArchive(path) | Self::SharedLibrary(path) => path,
        }
    }
    fn replace_path(&mut self, replacement: PathBuf) {
        match self {
            Self::StaticArchive(path) | Self::SharedLibrary(path) => *path = replacement,
        }
    }
}

/// Completed private Core preparation, generated Rust and any exact encoded
/// compile-time payloads, ready for native linking.
///
/// Preparation performs no Ash evaluation. This phase is consumed by
/// [`build_prepared`]; linking does not repeat Core encoding or source checking.
#[derive(Debug)]
pub struct PreparedProgramBuild {
    configuration: BuildConfiguration,
    generated_rust: String,
    native_payloads: Option<emit::NativePayloads>,
    producer_receipt: Option<super::checked_receipt::ReceiptSeed>,
    preparation_work: usize,
    compilation_work: CompilationWork,
    checked_preparation: bool,
}

impl PreparedProgramBuild {
    /// Borrows preparation observations when explicitly requested. FinalElf is
    /// absent until linking; no approval or executable authority is returned.
    #[must_use]
    pub fn producer_receipt(&self) -> Option<&super::checked_receipt::ProducerReceipt> {
        self.producer_receipt
            .as_ref()
            .map(super::checked_receipt::ReceiptSeed::receipt)
    }

    /// Borrows the exact generated host source that will be compiled.
    #[must_use]
    pub fn generated_rust(&self) -> &str {
        &self.generated_rust
    }

    /// Returns cumulative preparation charges, including encoding and emission.
    #[must_use]
    pub const fn preparation_work(&self) -> usize {
        self.preparation_work
    }
}

/// A linked executable with retained generated source and native-tool evidence.
#[derive(Debug)]
pub struct BuiltProgram {
    executable: PathBuf,
    generated_source: PathBuf,
    build_log: PathBuf,
    producer_receipt: Option<PathBuf>,
    preparation_work: usize,
    compilation_work: CompilationWork,
}

impl BuiltProgram {
    /// Returns bounded producer observations when explicitly requested. A matching
    /// receipt does not authorize startup or certify complete native closure.
    #[must_use]
    pub fn producer_receipt(&self) -> Option<&Path> {
        self.producer_receipt.as_deref()
    }

    /// Returns the executable copied after successful native linking.
    #[must_use]
    pub fn executable(&self) -> &Path {
        &self.executable
    }

    /// Returns the retained generated Rust host source.
    #[must_use]
    pub fn generated_source(&self) -> &Path {
        &self.generated_source
    }

    /// Returns the retained native build log.
    #[must_use]
    pub fn build_log(&self) -> &Path {
        &self.build_log
    }

    /// Returns cumulative encoding/emission charges without changing the compiler ledger.
    #[must_use]
    pub const fn preparation_work(&self) -> usize {
        self.preparation_work
    }

    /// Returns the original source compilation measurements.
    #[must_use]
    pub const fn compilation_work(&self) -> CompilationWork {
        self.compilation_work
    }
}

/// A source, private-Core preparation or native-link failure.
#[derive(Debug)]
pub struct BuildFailure(Failure);

#[derive(Debug)]
enum Failure {
    Source(FileFailure),
    UnsupportedTarget,
    UnsupportedCompilerConfiguration,
    UnsupportedProgram,
    InvalidOutput,
    InvalidNativeInput(usize),
    PreparationResource,
    Receipt(super::checked_receipt::ReceiptFailure),
    Bridge(super::bridge::ForeignBridgeFailure),
    Image(image::ImageFailure),
    Emission(emit::EmissionFailure),
    Io(io::Error),
    NativeTool(PathBuf),
}

impl BuildFailure {
    /// Returns the stable build-stage diagnostic reason.
    /// Source failures retain their own diagnostics through [`Self::source_failure`].
    #[must_use]
    pub const fn reason(&self) -> &'static str {
        match &self.0 {
            Failure::Source(_) => "build.source",
            Failure::UnsupportedTarget => "build.unsupported-target",
            Failure::UnsupportedCompilerConfiguration => "build.unsupported-compiler-configuration",
            Failure::UnsupportedProgram => "build.unsupported-program",
            Failure::InvalidOutput => "build.invalid-output",
            Failure::InvalidNativeInput(_) => "build.native-input",
            Failure::PreparationResource => "build.preparation-resource",
            Failure::Receipt(_) => "build.producer-receipt",
            Failure::Bridge(_) => "build.bridge-preparation",
            Failure::Image(_) => "build.core-preparation",
            Failure::Emission(_) => "build.host-emission",
            Failure::Io(_) => "build.input-output",
            Failure::NativeTool(_) => "build.native-tool",
        }
    }

    /// Identifies invocation, input or internal build responsibility.
    #[must_use]
    pub const fn responsibility(&self) -> &'static str {
        match &self.0 {
            Failure::UnsupportedTarget
            | Failure::UnsupportedCompilerConfiguration
            | Failure::UnsupportedProgram
            | Failure::InvalidOutput => "invocation",
            Failure::InvalidNativeInput(_) => "input",
            Failure::PreparationResource | Failure::Bridge(_) => "compiler",
            Failure::Receipt(_) => "input",
            Failure::Io(_) | Failure::NativeTool(_) => "input",
            Failure::Source(_) => "source",
            Failure::Image(_) | Failure::Emission(_) => "compiler",
        }
    }

    /// Borrows an original source-pipeline failure for structured diagnostics.
    #[must_use]
    pub fn source_failure(&self) -> Option<&FileFailure> {
        match &self.0 {
            Failure::Source(failure) => Some(failure),
            _ => None,
        }
    }

    /// Returns the retained log when a native build command failed.
    #[must_use]
    pub fn build_log(&self) -> Option<&Path> {
        match &self.0 {
            Failure::NativeTool(log) => Some(log),
            _ => None,
        }
    }
}

impl fmt::Display for BuildFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Failure::Source(error) => error.fmt(formatter),
            Failure::UnsupportedTarget => write!(
                formatter,
                "native program build requires {NATIVE_TARGET} on its matching host"
            ),
            Failure::UnsupportedCompilerConfiguration => formatter.write_str(
                "native program build requires a matching Cargo dev or release compiler profile",
            ),
            Failure::UnsupportedProgram => formatter.write_str(
                "native program build requires retained supported Pure or scalar/void Effect Core",
            ),
            Failure::InvalidOutput => {
                formatter.write_str("native program output must name an executable file")
            }
            Failure::InvalidNativeInput(index) => write!(
                formatter,
                "native input {index} is not a supported regular archive/shared object"
            ),
            Failure::PreparationResource => {
                formatter.write_str("native program preparation work or storage admission refused")
            }
            Failure::Receipt(error) => write!(formatter, "producer receipt refused: {error:?}"),
            Failure::Bridge(error) => {
                write!(formatter, "native bridge preparation refused: {error}")
            }
            Failure::Image(error) => error.fmt(formatter),
            Failure::Emission(error) => error.fmt(formatter),
            Failure::Io(error) => write!(
                formatter,
                "native program build input/output failed: {error}"
            ),
            Failure::NativeTool(log) => write!(
                formatter,
                "native program linking failed; see {}",
                log.display()
            ),
        }
    }
}

impl Error for BuildFailure {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.0 {
            Failure::Source(error) => Some(error),
            Failure::Io(error) => Some(error),
            _ => None,
        }
    }
}

impl From<io::Error> for BuildFailure {
    fn from(error: io::Error) -> Self {
        Self(Failure::Io(error))
    }
}

/// Prepares one checked program for the supported native host.
///
/// Accepts the established monomorphic Pure subset and the admitted closed
/// native Effect profile, including declared source owners, initialized bytes,
/// dependent lifecycles and sealed copying windows. Unsupported metadata
/// remains an explicit refusal.
/// Source provenance comes from the admitted program;
/// preparation never reopens its Ash source paths.
///
/// # Errors
/// Refuses unsupported targets/Core, exhausted work or storage admission.
pub fn prepare_program(
    program: &CompiledProgram,
    configuration: BuildConfiguration,
) -> Result<PreparedProgramBuild, BuildFailure> {
    if configuration.target != NATIVE_TARGET
        || !cfg!(all(
            target_os = "linux",
            target_arch = "x86_64",
            target_env = "gnu"
        ))
    {
        return Err(BuildFailure(Failure::UnsupportedTarget));
    }
    if configuration.output.file_name().is_none() {
        return Err(BuildFailure(Failure::InvalidOutput));
    }
    compiler_profile()?;
    let mut configuration = configuration;
    let mut work = if let Some((core, provenance)) = program.effect_build_input() {
        super::gas::preparation(provenance, core.node_count())
            .map_err(|()| BuildFailure(Failure::PreparationResource))?
    } else {
        // The established non-native Pure path keeps its existing policy.
        TypeWorkBudget::default()
    };
    // Native filesystem inputs are checked before emission/tool execution. This
    // check grants no source contract authority and performs no Ash checking.
    for (index, input) in configuration.native_inputs.iter_mut().enumerate() {
        work.charge(
            input
                .path()
                .as_os_str()
                .as_encoded_bytes()
                .len()
                .checked_add(64)
                .ok_or(BuildFailure(Failure::PreparationResource))?,
        )
        .map_err(|()| BuildFailure(Failure::PreparationResource))?;
        let path = fs::canonicalize(input.path())?;
        work.charge(path.as_os_str().as_encoded_bytes().len())
            .map_err(|()| BuildFailure(Failure::PreparationResource))?;
        input.replace_path(path);
        validate_native_input(input, index)?;
    }
    let (generated_rust, native_payloads, producer_receipt) =
        if let Some((core, provenance)) = program.pure_build_input() {
            // Receipt observations currently require the existing native image facts.
            if configuration.producer_receipt.is_some() {
                return Err(BuildFailure(Failure::UnsupportedProgram));
            }
            // Keep the established Pure path unchanged, including its unsafe policy.
            if !configuration.native_inputs.is_empty() {
                return Err(BuildFailure(Failure::UnsupportedProgram));
            }
            let image = image::encode(core, provenance, &mut work)
                .map_err(|error| BuildFailure(Failure::Image(error)))?;
            (
                emit::pure_host(&image, &super::runtime_fingerprint(), &mut work)
                    .map_err(|error| BuildFailure(Failure::Emission(error)))?,
                None,
                None,
            )
        } else if let Some((core, provenance)) = program.effect_build_input() {
            let image =
                image::encode_effect_for_build(core, provenance, &configuration.target, &mut work)
                    .map_err(|error| {
                        BuildFailure(match error {
                            image::NativeImageFailure::Image(error) => Failure::Image(error),
                            image::NativeImageFailure::Bridge(error) => Failure::Bridge(error),
                        })
                    })?;
            let emission = emit::native_host(&image, &super::runtime_fingerprint(), &mut work)
                .map_err(|error| BuildFailure(Failure::Emission(error)))?;
            let receipt = configuration
                .producer_receipt
                .map(|limits| {
                    let mut seed = super::checked_receipt::ReceiptSeed::from_emission(
                        &image,
                        core,
                        provenance,
                        &emission,
                        configuration.target.as_bytes(),
                        limits,
                    )?;
                    seed.observe_native_inputs(&configuration.native_inputs)?;
                    Ok(seed)
                })
                .transpose()
                .map_err(|error| BuildFailure(Failure::Receipt(error)))?;
            (emission.rust_source, Some(emission.payloads), receipt)
        } else {
            return Err(BuildFailure(Failure::UnsupportedProgram));
        };
    Ok(PreparedProgramBuild {
        configuration,
        generated_rust,
        native_payloads,
        producer_receipt,
        preparation_work: work.used(),
        compilation_work: *program.compilation_work(),
        checked_preparation: false,
    })
}

// Fixed-size binary-kind check only. It does not parse archive members or
// supply ABI/contract facts; ordinary linker failures remain native-tool errors.
/// Private producer-only checked Core entry. No public checked compilation or
/// startup permission is introduced. Source phase measurements are unavailable
/// through this low-level validated-Core API and remain explicitly absent.
#[allow(
    dead_code,
    reason = "TASK0053 producer is private until applicable protected launch exists"
)]
pub(super) fn prepare_checked_program(
    program: &crate::core::ValidatedEffectProgram,
    provenance: &[(
        crate::module::ModuleId,
        std::sync::Arc<crate::source::SourceFile>,
    )],
    mut configuration: BuildConfiguration,
    policy: crate::foreign::source_runtime::CheckedOwnerLimits,
) -> Result<PreparedProgramBuild, BuildFailure> {
    if configuration.target != NATIVE_TARGET
        || !cfg!(all(
            target_os = "linux",
            target_arch = "x86_64",
            target_env = "gnu"
        ))
    {
        return Err(BuildFailure(Failure::UnsupportedTarget));
    }
    if configuration.output.file_name().is_none() {
        return Err(BuildFailure(Failure::InvalidOutput));
    }
    compiler_profile()?;
    let limits = configuration
        .producer_receipt
        .ok_or(BuildFailure(Failure::UnsupportedProgram))?;
    let mut work = super::gas::preparation(provenance, program.node_count())
        .map_err(|()| BuildFailure(Failure::PreparationResource))?;
    for (index, input) in configuration.native_inputs.iter_mut().enumerate() {
        if !matches!(input, NativeLinkInput::StaticArchive(_)) {
            return Err(BuildFailure(Failure::UnsupportedProgram));
        }
        work.charge(1)
            .map_err(|()| BuildFailure(Failure::PreparationResource))?;
        let absolute = std::path::absolute(input.path())?;
        input.replace_path(absolute);
        validate_native_input(input, index)?;
    }
    let build =
        image::encode_checked_preparation(program, provenance, &configuration.target, &mut work)
            .map_err(|error| {
                BuildFailure(match error {
                    image::NativeImageFailure::Image(error) => Failure::Image(error),
                    image::NativeImageFailure::Bridge(error) => Failure::Bridge(error),
                })
            })?;
    let emission = emit::checked_native_host(
        &build,
        program,
        policy,
        &super::runtime_fingerprint(),
        &mut work,
    )
    .map_err(|error| BuildFailure(Failure::Emission(error)))?;
    let mut seed = super::checked_receipt::ReceiptSeed::from_checked_emission(
        &build,
        program,
        provenance,
        &emission,
        configuration.target.as_bytes(),
        limits,
        policy,
    )
    .map_err(|error| BuildFailure(Failure::Receipt(error)))?;
    seed.observe_native_inputs(&configuration.native_inputs)
        .map_err(|error| BuildFailure(Failure::Receipt(error)))?;
    Ok(PreparedProgramBuild {
        configuration,
        generated_rust: emission.rust_source,
        native_payloads: Some(emission.payloads),
        producer_receipt: Some(seed),
        preparation_work: work.used(),
        compilation_work: CompilationWork::default(),
        checked_preparation: true,
    })
}

fn validate_native_input(input: &NativeLinkInput, index: usize) -> Result<(), BuildFailure> {
    let invalid = || BuildFailure(Failure::InvalidNativeInput(index));
    let mut file = fs::File::open(input.path())?;
    if !file.metadata()?.is_file() {
        return Err(invalid());
    }
    match input {
        NativeLinkInput::StaticArchive(_) => {
            let mut header = [0; 8];
            file.read_exact(&mut header).map_err(|_| invalid())?;
            if &header != b"!<arch>\n" {
                return Err(invalid());
            }
        }
        NativeLinkInput::SharedLibrary(_) => {
            let mut header = [0; 64];
            file.read_exact(&mut header).map_err(|_| invalid())?;
            if &header[..4] != b"\x7fELF"
                || header[4] != 2
                || header[5] != 1
                || header[6] != 1
                || u16::from_le_bytes([header[16], header[17]]) != 3
                || u16::from_le_bytes([header[18], header[19]]) != 62
            {
                return Err(invalid());
            }
        }
    }
    Ok(())
}

static PROJECT_IDS: AtomicU64 = AtomicU64::new(0);

fn compiler_profile() -> Result<(&'static str, &'static str), BuildFailure> {
    match env!("ASH_RUNTIME_CARGO_PROFILE") {
        "debug" => Ok(("dev", "debug")),
        "release" => Ok(("release", "release")),
        _ => Err(BuildFailure(Failure::UnsupportedCompilerConfiguration)),
    }
}

fn fresh_project(parent: &Path) -> Result<PathBuf, BuildFailure> {
    fs::create_dir_all(parent)?;
    loop {
        let id = PROJECT_IDS.fetch_add(1, Ordering::Relaxed);
        let project = parent.join(format!("ash-host-{}-{id}", std::process::id()));
        match fs::create_dir(&project) {
            Ok(()) => return Ok(project),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error.into()),
        }
    }
}

/// Compiles and links a prepared host with one Cargo job.
///
/// Generated source, private compile-time payloads and native logs remain beside
/// the requested output in a fresh `.ash-build` project. Linking uses the matching
/// Ash source/toolchain;
/// the resulting executable reconstructs and validates private Core at startup
/// without invoking the Ash compiler or reading original source files.
/// Generated Cargo root artifacts are removed after copying. Shared dependency
/// caches remain; a private cache inside the generated project is temporary.
///
/// # Errors
/// Returns native-tool or filesystem failures. Failed linking preserves an
/// existing destination executable and retains generated inputs and diagnostics,
/// while retiring partial Cargo root artifacts. Cleanup failure prevents publication.
pub fn build_prepared(mut prepared: PreparedProgramBuild) -> Result<BuiltProgram, BuildFailure> {
    let native_host = prepared.native_payloads.is_some();
    let output = std::path::absolute(&prepared.configuration.output)?;
    let parent = output
        .parent()
        .ok_or(BuildFailure(Failure::InvalidOutput))?;
    let project = fresh_project(&parent.join(".ash-build"))?;
    fs::create_dir(project.join("src"))?;
    let generated_source = project.join("src/main.rs");
    let package_name = project
        .file_name()
        .and_then(|name| name.to_str())
        .expect("a generated project has an ASCII identity");
    fs::write(&generated_source, prepared.generated_rust)?;
    if let Some(payloads) = prepared.native_payloads {
        // Consume preparation's exact owned bytes once. include_bytes! embeds
        // them at Rust compile time; the resulting host opens no payload files.
        for (role, bytes) in payloads.into_files() {
            fs::write(project.join("src").join(role.file_name()), bytes)?;
        }
    }
    let ash_path = serde_json::to_string(env!("CARGO_MANIFEST_DIR"))
        .expect("a UTF-8 compiler manifest path is representable");
    let features = if cfg!(feature = "resource-calibration") {
        "[\"resource-calibration\"]"
    } else {
        "[]"
    };
    let (cargo_profile, profile) = compiler_profile()?;
    let optimization = env!("ASH_RUNTIME_OPT_LEVEL");
    let optimization = match optimization {
        "0" | "1" | "2" | "3" => optimization.to_owned(),
        "s" | "z" => format!("\"{optimization}\""),
        _ => return Err(BuildFailure(Failure::UnsupportedCompilerConfiguration)),
    };
    let panic = if cfg!(panic = "abort") {
        "abort"
    } else {
        "unwind"
    };
    let assertions = cfg!(debug_assertions);
    fs::write(
        project.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{package_name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n[dependencies]\nash = {{ path = {ash_path}, features = {features} }}\n\n[workspace]\n\n[profile.{cargo_profile}]\nopt-level = {optimization}\npanic = \"{panic}\"\ndebug-assertions = {assertions}\n"
        ),
    )?;
    fs::write(
        project.join("rust-toolchain.toml"),
        include_bytes!("../../rust-toolchain.toml"),
    )?;
    // Start from the exact resolved dependencies used by this compiler build.
    // Cargo may add the generated root package without selecting newer versions.
    fs::write(
        project.join("Cargo.lock"),
        include_bytes!("../../Cargo.lock"),
    )?;
    let emission_paths = [
        generated_source.clone(),
        project.join("src/program-image.bin"),
        project.join("src/expected-facts.bin"),
    ];
    let configuration_paths = [
        project.join("Cargo.toml"),
        project.join("rust-toolchain.toml"),
        project.join("Cargo.lock"),
    ];
    if let Some(seed) = &mut prepared.producer_receipt {
        seed.verify_emitted_files(&emission_paths)
            .map_err(|error| BuildFailure(Failure::Receipt(error)))?;
        seed.observe_configuration(&configuration_paths)
            .map_err(|error| BuildFailure(Failure::Receipt(error)))?;
    }
    let (target_directory, private_target) = match prepared.configuration.cargo_target_directory {
        Some(directory) => (std::path::absolute(directory)?, false),
        None => match std::env::var_os("CARGO_TARGET_DIR") {
            Some(directory) => (std::path::absolute(directory)?, false),
            None => (project.join("target"), true),
        },
    };
    let build_log = project.join("native-build.log");
    let log = fs::File::create(&build_log)?;
    let error_log = log.try_clone()?;
    let mut command = Command::new("cargo");
    // cargo rustc scopes native file arguments to this generated binary; no
    // RUSTFLAGS, shell, loader or implicit library-name resolver participates.
    command.current_dir(&project).args([
        if native_host { "rustc" } else { "build" },
        "--offline",
        "--jobs",
        "1",
        "--target",
        NATIVE_TARGET,
    ]);
    if profile == "release" {
        command.arg("--release");
    }
    command.arg("--target-dir").arg(&target_directory);
    if native_host {
        command.arg("--bin").arg(package_name);
        // Repeat only the fixed native-file-kind check immediately before tool
        // invocation; no image/source preparation or bridge planning is repeated.
        for (index, input) in prepared.configuration.native_inputs.iter().enumerate() {
            validate_native_input(input, index)?;
        }
        command.arg("--");
        if prepared.checked_preparation {
            // Exact root-only GNU whole-image selection, never global flags or
            // a default-profile fallback. This still grants no launch authority.
            command.args([
                "-C",
                "linker=/usr/bin/cc",
                "-C",
                "link-arg=-fuse-ld=bfd",
                "-C",
                "target-feature=+crt-static",
                "-C",
                "relocation-model=static",
                "-C",
                "link-arg=-no-pie",
                "-C",
                "strip=debuginfo",
            ]);
        }
        for input in &prepared.configuration.native_inputs {
            let mut argument = std::ffi::OsString::from("link-arg=");
            argument.push(input.path().as_os_str());
            command.arg("-C").arg(argument);
        }
    }
    let status = command
        .env("CARGO_BUILD_JOBS", "1")
        .env_remove("CARGO_BUILD_TARGET")
        .stdout(Stdio::from(log))
        .stderr(Stdio::from(error_log))
        .status();
    let receipt_path = project.join("producer-receipt.bin");
    let mut receipt_failure = None;
    let mut receipt_written = false;
    let finished = GeneratedArtifacts {
        project: &project,
        target_directory: &target_directory,
        package_name,
        target: NATIVE_TARGET,
        profile: cargo_profile,
        private_target,
    }
    .finish_with_observation(
        status.as_ref().is_ok_and(|status| status.success()),
        &output,
        &build_log,
        |linked| {
            if let Some(mut seed) = prepared.producer_receipt.take() {
                let observed = seed
                    .verify_emitted_files(&emission_paths)
                    .and_then(|()| seed.verify_native_inputs(&prepared.configuration.native_inputs))
                    .and_then(|()| seed.verify_configuration(&configuration_paths))
                    .and_then(|()| seed.finalize(linked));
                match observed {
                    Ok(bytes) => {
                        fs::write(&receipt_path, bytes)?;
                        receipt_written = true;
                    }
                    Err(error) => {
                        receipt_failure = Some(error);
                        return Err(io::Error::other("producer receipt refused"));
                    }
                }
            }
            Ok(())
        },
    );
    let status = status?;
    if !status.success() {
        return Err(BuildFailure(Failure::NativeTool(build_log)));
    }
    if let Some(error) = receipt_failure {
        return Err(BuildFailure(Failure::Receipt(error)));
    }
    finished.map_err(|failure| match failure {
        ArtifactFailure::Io(error) => BuildFailure::from(error),
        ArtifactFailure::Cleanup => BuildFailure(Failure::NativeTool(build_log.clone())),
    })?;
    Ok(BuiltProgram {
        executable: output,
        generated_source,
        build_log,
        producer_receipt: receipt_written.then_some(receipt_path),
        preparation_work: prepared.preparation_work,
        compilation_work: prepared.compilation_work,
    })
}

/// Compiles Ash once, prepares its checked Core, and links a native executable.
///
/// # Errors
/// Retains source pipeline failures and returns preparation/link failures.
pub fn build_path(
    source: RunConfiguration,
    configuration: BuildConfiguration,
) -> Result<BuiltProgram, BuildFailure> {
    let program = compile_path(source).map_err(|error| BuildFailure(Failure::Source(error)))?;
    build_prepared(prepare_program(&program, configuration)?)
}
