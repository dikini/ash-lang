//! Bakes a matching-compiler identity for private embedded program data.

use std::{env, error::Error, fs, path::PathBuf, process::Command};

use sha2::{Digest, Sha256};

fn main() -> Result<(), Box<dyn Error>> {
    println!("cargo:rustc-check-cfg=cfg(ash_checked_owner_root, values(\"v1\"))");
    let root = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").ok_or("missing manifest root")?);
    let canonical_root = root.to_str().filter(|path| !path.chars().any(char::is_control))
        .ok_or("unsupported canonical source path")?;
    println!("cargo:rustc-env=ASH_RUNTIME_CANONICAL_SOURCE_ROOT={canonical_root}");
    let cache_root = |variable: &str, fallback: &str| -> Result<PathBuf, &'static str> {
        match env::var_os(variable) {
            Some(path) => Ok(PathBuf::from(path)),
            None => Ok(PathBuf::from(env::var_os("HOME").ok_or("missing build cache home")?).join(fallback)),
        }
    };
    for (key,path) in [
        ("ASH_BUILD_CARGO_HOME", cache_root("CARGO_HOME", ".cargo")?),
        ("ASH_BUILD_RUSTUP_HOME", cache_root("RUSTUP_HOME", ".rustup")?),
    ] {
        let text=path.to_str().filter(|p| path.is_absolute() && !p.chars().any(char::is_control)).ok_or("unsupported build cache path")?;
        println!("cargo:rustc-env={key}={text}");
    }
    let mut paths = vec![
        root.join("build.rs"),
        root.join("Cargo.toml"),
        root.join("Cargo.lock"),
        root.join("rust-toolchain.toml"),
        root.join("trusted-preparation/Cargo.toml"),
        root.join("locales/en-US.ftl"),
        root.join("locales/bg.ftl"),
    ];
    let mut pending = vec![root.join("src"), root.join("trusted-preparation/src")];
    while let Some(directory) = pending.pop() {
        // Directory receipts also invalidate the identity when a file is added.
        println!("cargo:rerun-if-changed={}", directory.display());
        for entry in fs::read_dir(directory)? {
            let entry = entry?;
            if entry.file_type()?.is_dir() {
                pending.push(entry.path());
            } else if entry.file_type()?.is_file() {
                paths.push(entry.path());
            }
        }
    }
    paths.sort();
    let mut hash = Sha256::new();
    hash.update(b"Ash private program runtime v1\0");
    // Independent of the package/profile/configuration that compiles these
    // bytes. Artifact roots recompute this canonical component, then bind their
    // own exact manifest/lock/leaf/shim/configuration separately.
    let mut source_component = Sha256::new();
    source_component.update(b"Ash canonical runtime source component v1\0");
    for path in paths {
        println!("cargo:rerun-if-changed={}", path.display());
        let relative = path
            .strip_prefix(&root)?
            .to_str()
            .ok_or("non-UTF-8 runtime source path")?;
        let bytes = fs::read(&path)?;
        hash.update((relative.len() as u64).to_le_bytes());
        hash.update(relative.as_bytes());
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(&bytes);
        source_component.update((relative.len() as u64).to_le_bytes());
        source_component.update(relative.as_bytes());
        source_component.update((bytes.len() as u64).to_le_bytes());
        source_component.update(bytes);
    }
    let mut configuration = env::vars()
        .filter(|(key, _)| {
            matches!(
                key.as_str(),
                "TARGET" | "PROFILE" | "OPT_LEVEL" | "CARGO_ENCODED_RUSTFLAGS"
            ) || key.starts_with("CARGO_FEATURE_")
                || key.starts_with("CARGO_CFG_")
        })
        .collect::<Vec<_>>();
    configuration.sort();
    for (key, value) in configuration {
        hash.update((key.len() as u64).to_le_bytes());
        hash.update(key.as_bytes());
        hash.update((value.len() as u64).to_le_bytes());
        hash.update(value.as_bytes());
    }
    for (input, output) in [
        ("PROFILE", "ASH_RUNTIME_CARGO_PROFILE"),
        ("OPT_LEVEL", "ASH_RUNTIME_OPT_LEVEL"),
    ] {
        println!("cargo:rustc-env={output}={}", env::var(input)?);
    }
    let rustc = env::var_os("RUSTC").ok_or("missing Rust compiler")?;
    let rustc_text = rustc.to_str().filter(|path| !path.chars().any(char::is_control)).ok_or("unsupported Rust compiler path")?;
    println!("cargo:rustc-env=ASH_RUNTIME_RUSTC_PATH={rustc_text}");
    let compiler = Command::new(rustc)
        .args(["--version", "--verbose"])
        .output()?;
    if !compiler.status.success() {
        return Err("Rust compiler version discovery failed".into());
    }
    source_component.update(&compiler.stdout);
    println!("cargo:rustc-env=ASH_RUNTIME_SOURCE_COMPONENT={:x}", source_component.finalize());
    println!("cargo:rustc-env=ASH_RUNTIME_COMPILER_ID={:x}", Sha256::digest(&compiler.stdout));
    hash.update(compiler.stdout);
    println!(
        "cargo:rustc-env=ASH_RUNTIME_FINGERPRINT={:x}",
        hash.finalize()
    );
    Ok(())
}
