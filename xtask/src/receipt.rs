//! Conservative input pins for trusted local verification receipts.

use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub(super) const SCHEMA: u32 = 1;

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(super) struct Inputs {
    root: PathBuf,
    files: BTreeMap<PathBuf, Option<FilePin>>,
    configuration_files: BTreeMap<PathBuf, Option<FilePin>>,
    environment_sha256: String,
    tools: BTreeMap<String, String>,
    runner_sha256: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
struct FilePin {
    sha256: String,
    mode: u32,
    symlink: Option<PathBuf>,
}

pub(super) fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn output(command: &mut Command) -> Result<Vec<u8>, String> {
    let result = command
        .output()
        .map_err(|error| format!("{command:?}: {error}"))?;
    if !result.status.success() {
        return Err(format!(
            "{command:?} failed: {}",
            String::from_utf8_lossy(&result.stderr)
        ));
    }
    Ok(result.stdout)
}

fn file_pin(path: &Path) -> Result<String, String> {
    fs::read(path)
        .map(|bytes| digest(&bytes))
        .map_err(|error| format!("{}: {error}", path.display()))
}

fn input_file_pin(path: &Path) -> Result<FilePin, std::io::Error> {
    let bytes = fs::read(path)?;
    let metadata = fs::metadata(path)?;
    #[cfg(unix)]
    let mode = {
        use std::os::unix::fs::PermissionsExt;
        metadata.permissions().mode()
    };
    #[cfg(not(unix))]
    let mode = u32::from(metadata.permissions().readonly());
    let symlink = if fs::symlink_metadata(path)?.file_type().is_symlink() {
        Some(fs::read_link(path)?)
    } else {
        None
    };
    Ok(FilePin {
        sha256: digest(&bytes),
        mode,
        symlink,
    })
}

fn executable_pin(path: &Path, cache: &mut BTreeMap<PathBuf, String>) -> Result<String, String> {
    if let Some(pin) = cache.get(path) {
        return Ok(pin.clone());
    }
    let file = input_file_pin(path).map_err(|error| format!("{}: {error}", path.display()))?;
    let pin = digest(&serde_json::to_vec(&file).map_err(|error| error.to_string())?);
    cache.insert(path.to_owned(), pin.clone());
    Ok(pin)
}

fn pin_tool(
    root: &Path,
    name: &str,
    label: &str,
    executable: &std::ffi::OsStr,
    tools: &mut BTreeMap<String, String>,
    cache: &mut BTreeMap<PathBuf, String>,
) -> Result<(), String> {
    let path = executable_path(root, executable)?;
    tools.insert(format!("{label}-executable"), executable_pin(&path, cache)?);
    let canonical = path.canonicalize().map_err(|error| error.to_string())?;
    if canonical.file_name() == Some(std::ffi::OsStr::new("rustup")) {
        let bytes = output(
            Command::new(&canonical)
                .current_dir(root)
                .args(["which", name]),
        )?;
        let delegated = String::from_utf8(bytes).map_err(|error| error.to_string())?;
        let delegated = Path::new(delegated.trim());
        tools.insert(
            format!("{label}-delegated-executable"),
            executable_pin(delegated, cache)?,
        );
    }
    Ok(())
}

fn executable_path(root: &Path, executable: &std::ffi::OsStr) -> Result<PathBuf, String> {
    let path = Path::new(executable);
    if path.components().count() > 1 || path.is_absolute() {
        let path = root.join(path);
        return if path.is_file() {
            Ok(path)
        } else {
            Err(format!("executable not found: {}", path.display()))
        };
    }
    for directory in env::split_paths(&env::var_os("PATH").unwrap_or_default()) {
        let candidate = root.join(directory).join(path);
        if candidate.is_file() {
            return Ok(candidate);
        }
    }
    Err(format!("executable not found: {}", path.display()))
}

pub(super) fn require_ignored_output(root: &Path, directory: &Path) -> Result<(), String> {
    let directory = directory
        .canonicalize()
        .map_err(|error| error.to_string())?;
    if let Ok(relative) = directory.strip_prefix(root) {
        let result = Command::new("git")
            .current_dir(root)
            .args(["check-ignore", "--quiet", "--no-index", "--"])
            .arg(relative)
            .status()
            .map_err(|error| error.to_string())?;
        if !result.success() {
            return Err("receipt directory inside the checkout must be Git-ignored".into());
        }
    }
    Ok(())
}

pub(super) fn require_repository_root(root: &Path) -> Result<(), String> {
    let bytes = output(
        Command::new("git")
            .current_dir(root)
            .args(["rev-parse", "--show-toplevel"]),
    )?;
    let path = String::from_utf8(bytes).map_err(|error| error.to_string())?;
    let git_root = Path::new(path.trim())
        .canonicalize()
        .map_err(|error| error.to_string())?;
    if root.canonicalize().map_err(|error| error.to_string())? != git_root {
        return Err("run verification from the Git repository root".into());
    }
    Ok(())
}

pub(super) fn snapshot(root: &Path, external: &[PathBuf]) -> Result<Inputs, String> {
    let root = root.canonicalize().map_err(|error| error.to_string())?;
    let mut paths = BTreeSet::new();
    for arguments in [
        ["ls-files", "--cached", "-z"].as_slice(),
        ["ls-files", "--others", "--exclude-standard", "-z"].as_slice(),
    ] {
        let list = output(Command::new("git").current_dir(&root).args(arguments))?;
        for raw in list.split(|byte| *byte == 0).filter(|raw| !raw.is_empty()) {
            let path = String::from_utf8(raw.to_vec()).map_err(|error| error.to_string())?;
            paths.insert(root.join(path));
        }
    }
    let mut files = BTreeMap::new();
    for path in paths {
        let pin = match input_file_pin(&path) {
            Ok(pin) => Some(pin),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => return Err(format!("{}: {error}", path.display())),
        };
        files.insert(path, pin);
    }
    for path in external {
        let path = std::path::absolute(path).map_err(|error| error.to_string())?;
        files.insert(
            path.clone(),
            Some(input_file_pin(&path).map_err(|error| error.to_string())?),
        );
    }

    let mut configuration_paths = BTreeSet::new();
    for parent in root.ancestors() {
        for name in ["config", "config.toml"] {
            configuration_paths.insert(parent.join(".cargo").join(name));
        }
    }
    let cargo_home = env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo")));
    if let Some(home) = cargo_home {
        for name in ["config", "config.toml"] {
            configuration_paths.insert(home.join(name));
        }
    }
    let mut configuration_files = BTreeMap::new();
    for path in configuration_paths {
        let pin = match input_file_pin(&path) {
            Ok(pin) => Some(pin),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => return Err(format!("{}: {error}", path.display())),
        };
        configuration_files.insert(path, pin);
    }

    // Hash values rather than exposing credentials in receipts. Jobserver and
    // shell bookkeeping vary between equivalent launches; root is pinned above.
    let mut environment = BTreeMap::new();
    for (key, value) in env::vars_os() {
        let key = key
            .into_string()
            .map_err(|_| "non-UTF-8 environment name")?;
        if matches!(
            key.as_str(),
            "CARGO_MAKEFLAGS" | "_" | "SHLVL" | "PWD" | "OLDPWD"
        ) {
            continue;
        }
        let value = value
            .into_string()
            .map_err(|_| "non-UTF-8 environment value")?;
        environment.insert(key, value);
    }
    environment.insert("CARGO_BUILD_JOBS".into(), "1".into());
    let environment_sha256 =
        digest(&serde_json::to_vec(&environment).map_err(|error| error.to_string())?);
    let mut tools = BTreeMap::new();
    let mut executable_pins: BTreeMap<PathBuf, String> = BTreeMap::new();
    for (name, variable, arguments) in [
        ("cargo", "CARGO", ["--version"].as_slice()),
        ("rustc", "RUSTC", ["-vV"].as_slice()),
        ("rustdoc", "RUSTDOC", ["--version"].as_slice()),
        ("rustfmt", "RUSTFMT", ["--version"].as_slice()),
        (
            "clippy-driver",
            "CLIPPY_DRIVER_PATH",
            ["--version"].as_slice(),
        ),
        ("cc", "CC", ["--version"].as_slice()),
        ("ar", "AR", ["--version"].as_slice()),
    ] {
        let executable = env::var_os(variable).unwrap_or_else(|| name.into());
        let bytes = output(Command::new(&executable).current_dir(&root).args(arguments))?;
        tools.insert(name.to_owned(), digest(&bytes));
        pin_tool(
            &root,
            name,
            name,
            &executable,
            &mut tools,
            &mut executable_pins,
        )?;
        // Native build scripts invoke literal cc/ar; Cargo can delegate to PATH
        // tools as well. Overrides do not replace those actual selections.
        pin_tool(
            &root,
            name,
            &format!("path-{name}"),
            std::ffi::OsStr::new(name),
            &mut tools,
            &mut executable_pins,
        )?;
    }
    for name in ["cargo-fmt", "cargo-clippy"] {
        pin_tool(
            &root,
            name,
            name,
            std::ffi::OsStr::new(name),
            &mut tools,
            &mut executable_pins,
        )?;
    }
    for variable in ["RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"] {
        if let Some(path) = env::var_os(variable).filter(|path| !path.is_empty()) {
            tools.insert(
                variable.into(),
                executable_pin(&executable_path(&root, &path)?, &mut executable_pins)?,
            );
        }
    }
    let runner_sha256 = file_pin(&env::current_exe().map_err(|error| error.to_string())?)?;
    Ok(Inputs {
        root,
        files,
        configuration_files,
        environment_sha256,
        tools,
        runner_sha256,
    })
}

#[derive(Debug, Serialize, Deserialize)]
pub(super) struct StageReceipt {
    pub schema: u32,
    pub key: String,
    pub arguments: Vec<String>,
    pub rustdoc_flags: Option<String>,
    pub inputs: Inputs,
    pub exit_code: i32,
    pub seconds: f64,
    pub log: PathBuf,
    pub log_sha256: String,
}

impl StageReceipt {
    pub(super) fn load_matching(
        path: &Path,
        key: &str,
        inputs: &Inputs,
        arguments: &[&str],
        rustdoc_flags: Option<&str>,
    ) -> Option<Self> {
        let record: Self = serde_json::from_slice(&fs::read(path).ok()?).ok()?;
        if record.schema != SCHEMA
            || record.key != key
            || &record.inputs != inputs
            || record.arguments != arguments
            || record.rustdoc_flags.as_deref() != rustdoc_flags
            || record.exit_code != 0
            || !record.seconds.is_finite()
            || record.seconds < 0.0
            || file_pin(&record.log).ok().as_deref() != Some(record.log_sha256.as_str())
        {
            return None;
        }
        Some(record)
    }
}
