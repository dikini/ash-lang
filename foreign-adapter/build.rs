//! Checks the pinned SQLite C ABI and links the Linux experiment runtime.
use std::{env, path::PathBuf, process::Command};

fn main() {
    let target = env::var("TARGET").expect("Cargo supplies TARGET");
    assert_eq!(
        target, "x86_64-unknown-linux-gnu",
        "native experiment is audited only on Linux x86-64 GNU"
    );
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo supplies OUT_DIR"));
    let object = out.join("sqlite_bridge.o");
    let archive = out.join("libash_sqlite_bridge.a");
    let status = Command::new("cc")
        .args([
            "-std=c11",
            "-Werror=incompatible-pointer-types",
            "-fPIC",
            "-Ivendor",
            "-c",
            "sqlite_bridge.c",
            "-o",
        ])
        .arg(&object)
        .status()
        .expect("C compiler must be available");
    assert!(status.success(), "SQLite header/ABI check failed");
    let status = Command::new("ar")
        .arg("crs")
        .arg(&archive)
        .arg(&object)
        .status()
        .expect("archiver must be available");
    assert!(status.success(), "SQLite shim archive failed");
    println!("cargo:rerun-if-changed=sqlite_bridge.c");
    println!("cargo:rerun-if-changed=vendor/sqlite3.h");
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-lib=static=ash_sqlite_bridge");
    println!("cargo:rustc-link-lib=dylib:+verbatim=libsqlite3.so.0");
}
