//! Native tool invocation for the initial matching-compiler Pure host.

use std::{
    error::Error,
    fmt, fs, io,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
};

use crate::{
    compiler_work::CompilationWork,
    driver::{CompiledProgram, FileFailure, RunConfiguration, compile_path},
    types::TypeWorkBudget,
};

use super::{emit, image};

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
}

impl BuildConfiguration {
    /// Selects the supported host profile and an output executable.
    #[must_use]
    pub fn new(output: PathBuf) -> Self {
        Self {
            output,
            target: NATIVE_TARGET.to_owned(),
            cargo_target_directory: None,
        }
    }
}

/// Completed private Core preparation and generated Rust, ready for native linking.
///
/// Preparation performs no Ash evaluation. This phase is consumed by
/// [`build_prepared`]; linking does not repeat Core encoding or source checking.
#[derive(Debug)]
pub struct PreparedProgramBuild {
    configuration: BuildConfiguration,
    generated_rust: String,
    preparation_work: usize,
    compilation_work: CompilationWork,
}

impl PreparedProgramBuild {
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
    preparation_work: usize,
    compilation_work: CompilationWork,
}

impl BuiltProgram {
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
                "native program build currently requires retained monomorphic Pure Core",
            ),
            Failure::InvalidOutput => {
                formatter.write_str("native program output must name an executable file")
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
/// The initial slice accepts monomorphic Pure Core and refuses unsupported
/// metadata explicitly. Effect programs and foreign linking are subsequent
/// milestone deliveries. Source provenance comes from the admitted program;
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
    let (core, provenance) = program
        .pure_build_input()
        .ok_or(BuildFailure(Failure::UnsupportedProgram))?;
    let mut work = TypeWorkBudget::default();
    let image = image::encode(core, provenance, &mut work)
        .map_err(|error| BuildFailure(Failure::Image(error)))?;
    let generated_rust = emit::pure_host(&image, &super::runtime_fingerprint(), &mut work)
        .map_err(|error| BuildFailure(Failure::Emission(error)))?;
    Ok(PreparedProgramBuild {
        configuration,
        generated_rust,
        preparation_work: work.used(),
        compilation_work: *program.compilation_work(),
    })
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
/// Generated source and native logs remain beside the requested output in a
/// fresh `.ash-build` project. Linking uses the matching Ash source/toolchain;
/// the resulting executable reconstructs and validates private Core at startup
/// without invoking the Ash compiler or reading original source files.
///
/// # Errors
/// Returns native-tool or filesystem failures. Failed linking preserves an
/// existing destination executable and retains the generated project/log.
pub fn build_prepared(prepared: PreparedProgramBuild) -> Result<BuiltProgram, BuildFailure> {
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
    let target_directory = match prepared.configuration.cargo_target_directory {
        Some(directory) => std::path::absolute(directory)?,
        None => match std::env::var_os("CARGO_TARGET_DIR") {
            Some(directory) => std::path::absolute(directory)?,
            None => project.join("target"),
        },
    };
    let build_log = project.join("native-build.log");
    let log = fs::File::create(&build_log)?;
    let error_log = log.try_clone()?;
    let mut command = Command::new("cargo");
    command.current_dir(&project).args([
        "build",
        "--offline",
        "--jobs",
        "1",
        "--target",
        NATIVE_TARGET,
    ]);
    if profile == "release" {
        command.arg("--release");
    }
    let status = command
        .arg("--target-dir")
        .arg(&target_directory)
        .env("CARGO_BUILD_JOBS", "1")
        .env_remove("CARGO_BUILD_TARGET")
        .stdout(Stdio::from(log))
        .stderr(Stdio::from(error_log))
        .status()?;
    if !status.success() {
        return Err(BuildFailure(Failure::NativeTool(build_log)));
    }
    let linked = project.join("linked-program");
    fs::copy(
        target_directory
            .join(NATIVE_TARGET)
            .join(profile)
            .join(package_name),
        &linked,
    )?;
    fs::rename(linked, &output)?;
    Ok(BuiltProgram {
        executable: output,
        generated_source,
        build_log,
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
