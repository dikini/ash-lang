use super::{ArtifactFailure, GeneratedArtifacts};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    os::unix::fs::MetadataExt,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

const TARGET: &str = "x86_64-unknown-linux-gnu";
static IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let id = IDS.fetch_add(1, Ordering::Relaxed);
        let root =
            std::env::temp_dir().join(format!("ash-host-cleanup-test-{}-{id}", std::process::id()));
        fs::create_dir(&root).unwrap();
        fs::write(
            root.join("rust-toolchain.toml"),
            include_str!("../../rust-toolchain.toml"),
        )
        .unwrap();
        let dependency = root.join("shared");
        fs::create_dir_all(dependency.join("src")).unwrap();
        fs::write(dependency.join("Cargo.toml"),
            "[package]\nname = \"ash-artifact-shared\"\nversion = \"0.0.0\"\nedition = \"2024\"\n[workspace]\n[profile.dev]\ndebug = 0\n[profile.test]\ndebug = 0\n").unwrap();
        fs::write(dependency.join("src/lib.rs"),
            "pub fn answer() -> i32 { 42 }\n#[test] fn current_test() { assert_eq!(answer(), 42); }\n").unwrap();
        Self(root)
    }

    fn project(&self, source: &str) -> (PathBuf, String) {
        let id = IDS.fetch_add(1, Ordering::Relaxed);
        let name = format!("ash-host-{}-{id}", std::process::id());
        let project = self.0.join(&name);
        fs::create_dir_all(project.join("src")).unwrap();
        fs::write(project.join("Cargo.toml"), format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\n[workspace]\n[dependencies]\nash-artifact-shared = {{ path = \"../shared\" }}\n[profile.dev]\ndebug = 0\n")).unwrap();
        fs::write(project.join("src/main.rs"), source).unwrap();
        (project, name)
    }

    fn cargo(&self, project: &Path, cache: &Path, tests: bool) -> Output {
        let mut command = Command::new("cargo");
        command
            .current_dir(project)
            .arg(if tests { "test" } else { "build" });
        if tests {
            command.arg("--no-run");
        }
        let output = command
            .args(["--offline", "--jobs", "1", "--target", TARGET])
            .arg("--target-dir")
            .arg(cache)
            .env("CARGO_BUILD_JOBS", "1")
            .env_remove("CARGO_BUILD_TARGET")
            .output()
            .unwrap();
        let mut log = output.stdout.clone();
        log.extend_from_slice(&output.stderr);
        fs::write(project.join("native-build.log"), &log).unwrap();
        output
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn files(root: &Path) -> Vec<PathBuf> {
    if !root.exists() {
        return Vec::new();
    }
    let mut result = Vec::new();
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            result.extend(files(&path));
        } else {
            result.push(path);
        }
    }
    result
}

fn owned(cache: &Path, package: &str) -> Vec<PathBuf> {
    let crate_name = package.replace('-', "_");
    files(cache)
        .into_iter()
        .filter(|path| {
            path.components().any(|part| {
                let name = part.as_os_str().to_string_lossy();
                name == package
                    || name == format!("{package}.d")
                    || name.starts_with(&format!("{package}-"))
                    || name.starts_with(&format!("{crate_name}-"))
            })
        })
        .collect()
}

fn unique_bytes(paths: &[PathBuf]) -> u64 {
    let mut inodes = BTreeSet::new();
    paths
        .iter()
        .map(|path| fs::metadata(path).unwrap())
        .filter(|meta| inodes.insert((meta.dev(), meta.ino())))
        .map(|meta| meta.blocks() * 512)
        .sum()
}

fn shared_snapshot(cache: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
    files(cache)
        .into_iter()
        .filter(|path| {
            path.components().any(|part| {
                let name = part.as_os_str().to_string_lossy();
                name.starts_with("ash-artifact-shared-")
                    || name.starts_with("ash_artifact_shared-")
                    || name.starts_with("libash_artifact_shared-")
            })
        })
        .map(|path| {
            let contents = fs::read(&path).unwrap();
            (path, contents)
        })
        .collect()
}

#[test]
fn repeated_successes_remove_leaf_aliases_and_metadata_but_keep_shared_tests() {
    let fixture = Fixture::new();
    let cache = fixture.0.join("cache");
    let shared = fixture.cargo(&fixture.0.join("shared"), &cache, true);
    assert!(
        shared.status.success(),
        "{}",
        String::from_utf8_lossy(&shared.stderr)
    );
    let protected: BTreeMap<_, _> = shared_snapshot(&cache)
        .into_iter()
        .filter(|(path, _)| {
            !path
                .components()
                .any(|part| part.as_os_str() == "incremental")
        })
        .collect();
    assert!(!protected.is_empty());
    let mut packages = Vec::new();
    let mut linked_bytes = 0;
    for _ in 0..3 {
        let (project, package) =
            fixture.project("fn main() { println!(\"{}\", ash_artifact_shared::answer()); }\n");
        let build = fixture.cargo(&project, &cache, false);
        assert!(
            build.status.success(),
            "{}",
            String::from_utf8_lossy(&build.stderr)
        );
        let original = owned(&cache, &package);
        assert!(
            original
                .iter()
                .any(|path| path.components().any(|p| p.as_os_str() == ".fingerprint"))
        );
        assert!(
            original
                .iter()
                .any(|path| path.parent().unwrap().ends_with("deps"))
        );
        linked_bytes += unique_bytes(&original);
        let dependencies_before_cleanup = shared_snapshot(&cache);
        let output = project.join("published");
        GeneratedArtifacts {
            project: &project,
            target_directory: &cache,
            package_name: &package,
            target: TARGET,
            profile: "dev",
            private_target: false,
        }
        .finish(true, &output, &project.join("native-build.log"))
        .unwrap();
        for (path, bytes) in dependencies_before_cleanup {
            assert!(
                fs::read(&path).is_ok_and(|current| current == bytes),
                "cleanup changed shared artifact: {}",
                path.display()
            );
        }
        packages.push((package, output));
    }
    let leftovers: Vec<_> = packages
        .iter()
        .flat_map(|(name, _)| owned(&cache, name))
        .collect();
    eprintln!(
        "three generated roots: linked_unique_bytes={linked_bytes}, retained_leaf_files={}, retained_leaf_bytes={}",
        leftovers.len(),
        unique_bytes(&leftovers)
    );
    assert!(
        leftovers.is_empty(),
        "completed generated root artifacts remain: {leftovers:?}"
    );
    for (path, bytes) in protected {
        assert!(
            fs::read(&path).is_ok_and(|current| current == bytes),
            "cleanup changed current shared test artifact: {}",
            path.display()
        );
    }
    for (_, output) in packages {
        let run = Command::new(output).output().unwrap();
        assert!(run.status.success());
        assert_eq!(run.stdout, b"42\n");
    }
}

#[test]
fn failed_link_cleans_partial_leaf_and_keeps_destination_source_and_diagnostic() {
    let fixture = Fixture::new();
    let cache = fixture.0.join("cache");
    let (project, package) = fixture.project("unsafe extern \"C\" { fn ash_missing_cleanup_symbol(); }\nfn main() { unsafe { ash_missing_cleanup_symbol(); } }\n");
    let output = project.join("published");
    fs::write(&output, b"previous destination").unwrap();
    let build = fixture.cargo(&project, &cache, false);
    assert!(!build.status.success());
    assert!(!owned(&cache, &package).is_empty());
    let log = project.join("native-build.log");
    GeneratedArtifacts {
        project: &project,
        target_directory: &cache,
        package_name: &package,
        target: TARGET,
        profile: "dev",
        private_target: false,
    }
    .finish(false, &output, &log)
    .unwrap();
    assert!(owned(&cache, &package).is_empty());
    assert_eq!(fs::read(output).unwrap(), b"previous destination");
    assert!(project.join("src/main.rs").is_file());
    assert!(
        fs::read_to_string(log)
            .unwrap()
            .contains("ash_missing_cleanup_symbol")
    );
}

#[test]
fn private_cache_is_removed_after_copy_without_removing_published_program() {
    let fixture = Fixture::new();
    let (project, package) =
        fixture.project("fn main() { println!(\"{}\", ash_artifact_shared::answer()); }\n");
    let cache = project.join("target");
    let build = fixture.cargo(&project, &cache, false);
    assert!(build.status.success());
    let output = project.join("published");
    GeneratedArtifacts {
        project: &project,
        target_directory: &cache,
        package_name: &package,
        target: TARGET,
        profile: "dev",
        private_target: true,
    }
    .finish(true, &output, &project.join("native-build.log"))
    .unwrap();
    assert!(!cache.exists());
    assert_eq!(Command::new(output).output().unwrap().stdout, b"42\n");
    assert!(project.join("src/main.rs").is_file());
    assert!(project.join("native-build.log").is_file());
}

#[test]
fn cleanup_failure_prevents_publication_and_removes_the_staging_copy() {
    let fixture = Fixture::new();
    let cache = fixture.0.join("cache");
    let (project, package) = fixture.project("fn main() {}\n");
    assert!(fixture.cargo(&project, &cache, false).status.success());
    let output = project.join("published");
    fs::write(&output, b"previous destination").unwrap();
    // Force Cargo's package cleanup to refuse, after successful compilation.
    fs::write(project.join("Cargo.toml"), "invalid manifest =\n").unwrap();
    let log = project.join("native-build.log");
    let result = GeneratedArtifacts {
        project: &project,
        target_directory: &cache,
        package_name: &package,
        target: TARGET,
        profile: "dev",
        private_target: false,
    }
    .finish(true, &output, &log);
    match result {
        Err(ArtifactFailure::Cleanup) => (),
        other => panic!("expected cleanup refusal: {other:?}"),
    }
    assert_eq!(fs::read(output).unwrap(), b"previous destination");
    assert!(!project.join("linked-program").exists());
    assert!(fs::read_to_string(log).unwrap().contains("cleanup"));
}

#[test]
fn failed_copy_still_cleans_leaf_and_preserves_destination() {
    let fixture = Fixture::new();
    let cache = fixture.0.join("cache");
    let (project, package) = fixture.project("fn main() {}\n");
    assert!(fixture.cargo(&project, &cache, false).status.success());
    fs::remove_file(cache.join(TARGET).join("debug").join(&package)).unwrap();
    let output = project.join("published");
    fs::write(&output, b"previous destination").unwrap();
    let result = GeneratedArtifacts {
        project: &project,
        target_directory: &cache,
        package_name: &package,
        target: TARGET,
        profile: "dev",
        private_target: false,
    }
    .finish(true, &output, &project.join("native-build.log"));
    match result {
        Err(ArtifactFailure::Io(error)) => assert!(!error.to_string().is_empty()),
        other => panic!("expected copy refusal: {other:?}"),
    }
    assert!(owned(&cache, &package).is_empty());
    assert_eq!(fs::read(output).unwrap(), b"previous destination");
    assert!(!project.join("linked-program").exists());
}
