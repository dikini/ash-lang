//! Bakes a matching-compiler identity for private embedded program data.

use std::{env, error::Error, fs, path::PathBuf, process::Command};

use sha2::{Digest, Sha256};

fn main() -> Result<(), Box<dyn Error>> {
    let root = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").ok_or("missing manifest root")?);
    let mut paths = vec![
        root.join("build.rs"),
        root.join("Cargo.toml"),
        root.join("Cargo.lock"),
        root.join("rust-toolchain.toml"),
        root.join("native-buffer/Cargo.toml"),
    ];
    let mut pending = vec![root.join("src"), root.join("native-buffer/src")];
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
        hash.update(bytes);
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
    let compiler = Command::new(env::var_os("RUSTC").ok_or("missing Rust compiler")?)
        .args(["--version", "--verbose"])
        .output()?;
    if !compiler.status.success() {
        return Err("Rust compiler version discovery failed".into());
    }
    hash.update(compiler.stdout);
    println!(
        "cargo:rustc-env=ASH_RUNTIME_FINGERPRINT={:x}",
        hash.finalize()
    );
    Ok(())
}
