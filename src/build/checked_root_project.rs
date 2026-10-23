//! Fixed generated-package construction for the artifact-local binary root.
//! Files/commands here are build DATA, never installed-context authority.
use crate::types::TypeWorkBudget;
use std::{path::{Path, PathBuf}, process::Command};
use super::checked_root_identity::Failure;

const PACKAGE: &str = "ash-checked-owner-root";
const LEAF_PACKAGE: &str = "ash-checked-owner-leaf";
const MANIFEST: &str = include_str!("../../Cargo.toml");
const TOOLCHAIN: &[u8] = include_bytes!("../../rust-toolchain.toml");
const BUILD_SCRIPT: &str = include_str!("checked_owner_root_build.rs.in");
const LOCK_POLICY: &[u8] = include_bytes!("checked_root_lock_policy.rs");
const ORIGINAL_LOCK: &[u8] = include_bytes!("../../Cargo.lock");

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct RootConfiguration {
    version: u32,
    canonical_source_root: PathBuf,
    project_root: PathBuf,
    source_component: String,
    compiler: String,
    environment: super::checked_root_environment::Environment,
}
/// Complete code/configuration DATA for independent request reconstruction.
/// No field is an approval, installed context or caller-selected runtime pin.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct BuildData {
    pub version: u32,
    pub project_root: PathBuf,
    pub manifest: Vec<u8>,
    pub build_configuration: Vec<u8>,
    pub settled_lock: Vec<u8>,
    pub leaf_manifest: Vec<u8>,
    pub leaf: Vec<u8>,
    pub shim: Vec<u8>,
}
fn leaf_manifest(work: &mut TypeWorkBudget) -> Result<String, Failure> {
    pay(work,1024)?;
    Ok(format!("[package]\nname = {LEAF_PACKAGE:?}\nversion = \"0.0.0\"\nedition = \"2024\"\n\n[workspace]\n\n[lints.rust]\nunsafe_op_in_unsafe_fn = \"deny\"\n\n[lints.clippy]\nundocumented_unsafe_blocks = \"deny\"\n"))
}
fn validate_lock(settled: &[u8], work: &mut TypeWorkBudget) -> Result<(), Failure> {
    if settled.len() > 1024 * 1024 { return Err(Failure::Resource); }
    // Closed parser has at most256 packages and256 edges/package. Reserve
    // parsing, duplicate/edge scans, sorted copies and graph traversal before
    // allocation; this is work on actual bytes, not a larger product limit.
    let bytes = ORIGINAL_LOCK.len().checked_add(settled.len()).ok_or(Failure::Resource)?;
    pay(work, bytes)?;
    let mut packages = 0usize;
    let mut max_edges = 0usize;
    for raw in [ORIGINAL_LOCK, settled] {
        let text = std::str::from_utf8(raw).map_err(|_| Failure::Association)?;
        let mut edges = None;
        for line in text.lines().map(str::trim) {
            if line == "[[package]]" { packages = packages.checked_add(1).ok_or(Failure::Resource)?; }
            if line == "dependencies = [" { edges = Some(0usize); }
            else if line == "]" { if let Some(n) = edges.take() { max_edges = max_edges.max(n); } }
            else if let Some(n) = edges.as_mut() { *n = n.checked_add(1).ok_or(Failure::Resource)?; }
        }
    }
    if packages > 512 || max_edges > 256 { return Err(Failure::Resource); }
    let factor = packages.checked_add(max_edges).and_then(|n| n.checked_add(16)).and_then(|n| n.checked_mul(8)).ok_or(Failure::Resource)?;
    pay(work, bytes.checked_mul(factor).ok_or(Failure::Resource)?)?;
    super::checked_root_lock_policy::validate(ORIGINAL_LOCK, settled).map_err(|()| Failure::Association)
}
impl BuildData {
    pub(super) fn reconstruct(&self, expected_leaf: &str, expected_shim: &str, work: &mut TypeWorkBudget) -> Result<super::checked_root_identity::RootCodeIdentity, Failure> {
        if self.version != 1 { return Err(Failure::Unsupported); }
        if self.build_configuration.len() > 16 * 1024 || self.manifest.len() > 65536 || self.leaf_manifest.len() > 65536
            || self.leaf.len() > 32 * 1024 * 1024 || self.shim.len() > 32 * 1024 * 1024 { return Err(Failure::Resource); }
        pay(work, self.build_configuration.len().checked_mul(8).ok_or(Failure::Resource)?)?;
        let config: RootConfiguration = serde_json::from_slice(&self.build_configuration).map_err(|_| Failure::Association)?;
        if config.version != 1 || config.project_root != self.project_root
            || config.canonical_source_root != Path::new(env!("ASH_RUNTIME_CANONICAL_SOURCE_ROOT"))
            || config.source_component != env!("ASH_RUNTIME_SOURCE_COMPONENT") || config.compiler != env!("ASH_RUNTIME_COMPILER_ID") { return Err(Failure::Association); }
        config.environment.admit_data(&self.project_root, work)?;
        // Require the one canonical serialization; no unknown config fields,
        // alternate paths, arbitrary code or caller fingerprint is admitted.
        let canonical_config = serde_json::to_vec(&config).map_err(|_| Failure::Resource)?;
        let expected_manifest = manifest_for(&config.canonical_source_root, work)?;
        let expected_leaf_manifest = leaf_manifest(work)?;
        pay(work, canonical_config.len().checked_add(self.manifest.len()).and_then(|n| n.checked_add(self.leaf_manifest.len())).and_then(|n| n.checked_add(self.leaf.len())).and_then(|n| n.checked_add(self.shim.len())).ok_or(Failure::Resource)?)?;
        if canonical_config != self.build_configuration || expected_manifest.as_bytes() != self.manifest
            || expected_leaf_manifest.as_bytes() != self.leaf_manifest || expected_leaf.as_bytes() != self.leaf || expected_shim.as_bytes() != self.shim { return Err(Failure::Association); }
        validate_lock(&self.settled_lock, work)?;
        let root = self.project_root.to_str().ok_or(Failure::Unsupported)?;
        super::checked_root_identity::derive(&super::checked_root_identity::Configuration {
            target: super::host::NATIVE_TARGET, canonical_source_root: env!("ASH_RUNTIME_CANONICAL_SOURCE_ROOT"), project_root: root,
            profile: "debug", optimization: "0", panic: "unwind", debug_assertions: true,
            manifest: &self.manifest, build_configuration: &self.build_configuration, settled_lock: &self.settled_lock,
            leaf_manifest: &self.leaf_manifest, leaf: &self.leaf, shim: &self.shim,
        }, work)
    }
}


pub(super) struct Project {
    root: PathBuf,
    canonical: PathBuf,
    manifest: String,
    environment: super::checked_root_environment::Environment,
}
fn pay(work: &mut TypeWorkBudget, n: usize) -> Result<(), Failure> {
    work.charge(n).map_err(|()| Failure::Resource)
}
fn quoted(path: &Path, work: &mut TypeWorkBudget) -> Result<String, Failure> {
    let text = path.to_str().ok_or(Failure::Unsupported)?;
    if text.len() > 4096 || !path.is_absolute() { return Err(Failure::Unsupported); }
    pay(work, text.len().checked_mul(8).ok_or(Failure::Resource)?)?;
    serde_json::to_string(text).map_err(|_| Failure::Association)
}
pub(super) fn manifest_for(canonical: &Path, work: &mut TypeWorkBudget) -> Result<String, Failure> {
    pay(work, canonical.as_os_str().len().checked_mul(2).and_then(|n|n.checked_add(64)).ok_or(Failure::Resource)?)?;
    let source = quoted(&canonical.join("src/lib.rs"), work)?;
    let trusted = quoted(&canonical.join("trusted-preparation"), work)?;
    pay(work, MANIFEST.len())?;
    let (_, rest) = MANIFEST.split_once("\n[dependencies]\n").ok_or(Failure::Association)?;
    let (dependencies, _) = rest.split_once("\n[build-dependencies]\n").ok_or(Failure::Association)?;
    // This exact original block contains production dependencies only.
    // Original Ash dev-dependencies and selected provider adapters never
    // become dependencies of the generated root or opaque leaf.
    let size = dependencies.len().checked_add(source.len()).and_then(|n| n.checked_add(trusted.len())).and_then(|n| n.checked_add(2048)).ok_or(Failure::Resource)?;
    pay(work, size)?;
    let manifest = format!("[package]\nname = {PACKAGE:?}\nversion = \"0.0.0\"\nedition = \"2024\"\nbuild = \"build.rs\"\n\n[[bin]]\nname = {PACKAGE:?}\npath = {source}\n\n[dependencies]\n{dependencies}\nchecked_owner_leaf = {{ package = {LEAF_PACKAGE:?}, path = \"leaf\" }}\nash-trusted-preparation = {{ path = {trusted} }}\n\n[build-dependencies]\nsha2 = \"=0.10.9\"\nserde = {{ version = \"1\", features = [\"derive\"] }}\nserde_json = \"=1.0.151\"\n\n[features]\nresource-calibration = []\n\n[workspace]\n\n[profile.dev]\nopt-level = 0\npanic = \"unwind\"\ndebug-assertions = true\noverflow-checks = true\n\n[lints.rust]\nunsafe_code = \"forbid\"\n");
    Ok(manifest)
}

impl Project {
    /// The caller supplies a freshly owned transaction directory. No directory
    /// supplied here selects a protected configuration, store or runtime image.
    pub(super) fn create(root: PathBuf, leaf: &str, shim: &str, work: &mut TypeWorkBudget) -> Result<Self, Failure> {
        if !root.is_absolute() { return Err(Failure::Unsupported); }
        if cfg!(feature = "resource-calibration") || env!("ASH_RUNTIME_CARGO_PROFILE") != "debug"
            || env!("ASH_RUNTIME_OPT_LEVEL") != "0" || !cfg!(debug_assertions) || cfg!(panic = "abort") {
            return Err(Failure::Unsupported);
        }
        if leaf.is_empty() || shim.is_empty() || leaf.len() > 32 * 1024 * 1024 || shim.len() > 32 * 1024 * 1024 {
            return Err(Failure::Resource);
        }
        let environment = super::checked_root_environment::Environment::discover(&root, work)?;
        let canonical = PathBuf::from(env!("ASH_RUNTIME_CANONICAL_SOURCE_ROOT"));
        let manifest = manifest_for(&canonical, work)?;
        let leaf_manifest = leaf_manifest(work)?;
        let config_bound = environment.configurations.iter().try_fold(1024usize, |n, c| n.checked_add(c.path.as_os_str().len())?.checked_add(c.bytes.len()))
            .and_then(|n| n.checked_add(canonical.as_os_str().len()))
            .and_then(|n| n.checked_add(root.as_os_str().len()))
            .and_then(|n| n.checked_add(environment.cargo.as_os_str().len()))
            .and_then(|n| n.checked_add(environment.rustc.as_os_str().len()))
            .and_then(|n| n.checked_add(environment.cargo_home.as_os_str().len()))
            .and_then(|n| n.checked_add(environment.rustup_home.as_os_str().len()))
            .and_then(|n| n.checked_mul(8)).ok_or(Failure::Resource)?;
        pay(work, config_bound)?;
        let config = serde_json::to_vec(&RootConfiguration {
            version: 1, canonical_source_root: canonical.clone(), project_root: root.clone(),
            source_component: env!("ASH_RUNTIME_SOURCE_COMPONENT").into(), compiler: env!("ASH_RUNTIME_COMPILER_ID").into(), environment: environment.clone(),
        }).map_err(|_| Failure::Association)?;
        if config.len() > config_bound || config.len() > 16 * 1024 { return Err(Failure::Resource); }
        let total = manifest.len().checked_add(leaf_manifest.len()).and_then(|n| n.checked_add(leaf.len())).and_then(|n| n.checked_add(shim.len())).and_then(|n| n.checked_add(TOOLCHAIN.len())).and_then(|n| n.checked_add(ORIGINAL_LOCK.len())).and_then(|n| n.checked_add(BUILD_SCRIPT.len())).and_then(|n| n.checked_add(config.len())).and_then(|n| n.checked_add(LOCK_POLICY.len())).ok_or(Failure::Resource)?;
        pay(work, total)?;
        std::fs::create_dir(&root).map_err(|_| Failure::Resource)?;
        std::fs::create_dir(root.join("leaf")).map_err(|_| Failure::Resource)?;
        std::fs::create_dir(root.join("leaf/src")).map_err(|_| Failure::Resource)?;
        for (path, bytes) in [
            ("Cargo.toml", manifest.as_bytes()), ("Cargo.lock", ORIGINAL_LOCK),
            ("rust-toolchain.toml", TOOLCHAIN), ("leaf/Cargo.toml", leaf_manifest.as_bytes()),
            ("leaf/src/lib.rs", leaf.as_bytes()), ("root-shim.rs", shim.as_bytes()),
            ("build.rs", BUILD_SCRIPT.as_bytes()), ("lock_policy.rs", LOCK_POLICY), ("root-config.json", config.as_slice()),
        ] { std::fs::write(root.join(path), bytes).map_err(|_| Failure::Resource)?; }
        Ok(Self { root, canonical, manifest, environment })
    }
    /// Capture only already-created transaction files after Cargo has settled
    /// the lock. Same-open bounded reads and exact reconstruction precede use.
    pub(super) fn snapshot(&self, expected_leaf: &str, expected_shim: &str, work: &mut TypeWorkBudget) -> Result<BuildData, Failure> {
        use std::{io::Read, os::unix::fs::{MetadataExt, OpenOptionsExt}};
        self.verify_environment(work)?;
        pay(work,self.root.as_os_str().len())?;
        let mut read = |name: &str, limit: usize| -> Result<Vec<u8>, Failure> {
            pay(work, name.len()+32)?;
            let mut file = std::fs::OpenOptions::new().read(true).custom_flags(0x20000|0x80000|0x800).open(self.root.join(name)).map_err(|_| Failure::Resource)?;
            let before = file.metadata().map_err(|_| Failure::Resource)?;
            let size = usize::try_from(before.len()).map_err(|_| Failure::Resource)?;
            if !before.is_file() || size > limit { return Err(Failure::Resource); }
            pay(work, size.checked_add(1).and_then(|n| n.checked_mul(4)).ok_or(Failure::Resource)?)?;
            let mut bytes = Vec::new();
            bytes.try_reserve_exact(size+1).map_err(|_| Failure::Resource)?;
            std::io::Read::by_ref(&mut file).take((size+1) as u64).read_to_end(&mut bytes).map_err(|_| Failure::Resource)?;
            let after = file.metadata().map_err(|_| Failure::Resource)?;
            if bytes.len()!=size || (before.dev(),before.ino(),before.len(),before.mtime(),before.mtime_nsec(),before.ctime(),before.ctime_nsec()) != (after.dev(),after.ino(),after.len(),after.mtime(),after.mtime_nsec(),after.ctime(),after.ctime_nsec()) { return Err(Failure::Association); }
            Ok(bytes)
        };
        let data = BuildData { version: 1, project_root: self.root.clone(),
            manifest: read("Cargo.toml",65536)?, build_configuration: read("root-config.json",16384)?,
            settled_lock: read("Cargo.lock",1024*1024)?, leaf_manifest: read("leaf/Cargo.toml",65536)?,
            leaf: read("leaf/src/lib.rs",32*1024*1024)?, shim: read("root-shim.rs",32*1024*1024)?,
        };
        data.reconstruct(expected_leaf,expected_shim,work)?;
        Ok(data)
    }
    pub(super) fn verify_environment(&self, work: &mut TypeWorkBudget) -> Result<(), Failure> {
        self.environment.verify(&self.root, work)
    }
    pub(super) fn manifest(&self) -> &[u8] { self.manifest.as_bytes() }
    pub(super) fn canonical_root(&self) -> &Path { &self.canonical }
    fn cargo(&self, verb: &str, work: &mut TypeWorkBudget) -> Result<Command, Failure> {
        self.environment.command(&self.root, verb, work)
    }
    /// Run only through the existing bounded owned Cargo transaction. Lock
    /// settling must finish before deriving identity or encoding payloads.
    pub(super) fn settle_lock_command(&self, work: &mut TypeWorkBudget) -> Result<Command, Failure> { self.cargo("generate-lockfile", work) }
    /// Fixed actual command policy corresponding to the identity recipe. This
    /// accepts only the product's owned linker observer, not arbitrary flags.
    pub(super) fn compile_command(&self, target: &Path, linker: &Path, work: &mut TypeWorkBudget) -> Result<Command, Failure> {
        let mut command = self.cargo("rustc", work)?;
        command.args(["--locked", "--jobs", "1", "--target", super::host::NATIVE_TARGET, "--bin", PACKAGE]);
        command.arg("--target-dir").arg(target).arg("--");
        command.arg("--cfg").arg("ash_checked_owner_root=\"v1\"");
        command.arg("-C").arg(format!("linker={}", linker.display()));
        command.args(["-C", "link-arg=-fuse-ld=bfd", "-C", "target-feature=+crt-static", "-C", "relocation-model=static", "-C", "link-arg=-no-pie", "-C", "strip=debuginfo"]);
        Ok(command)
    }
}

#[cfg(test)]
pub(super) fn fixture_data(leaf: &str, shim: &str, work: &mut TypeWorkBudget) -> BuildData {
    let canonical=PathBuf::from(env!("ASH_RUNTIME_CANONICAL_SOURCE_ROOT"));
    let project=PathBuf::from("/tmp/ash-root-request-data-only/root");
    let environment=super::checked_root_environment::Environment::discover(&project,work).unwrap();
    let config=RootConfiguration {version:1,canonical_source_root:canonical.clone(),project_root:project.clone(),source_component:env!("ASH_RUNTIME_SOURCE_COMPONENT").into(),compiler:env!("ASH_RUNTIME_COMPILER_ID").into(),environment};
    // Test construction is separate from the request's actual shared meter.
    BuildData {version:1,project_root:project,manifest:manifest_for(&canonical,work).unwrap().into_bytes(),
        build_configuration:serde_json::to_vec(&config).unwrap(),settled_lock:super::checked_root_lock_policy::fixture(ORIGINAL_LOCK),
        leaf_manifest:leaf_manifest(work).unwrap().into_bytes(),leaf:leaf.as_bytes().to_vec(),shim:shim.as_bytes().to_vec()}
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn closed_root_reconstruction_binds_code_config_graph_and_shared_work() {
        // Clearly untrusted code DATA here; the actual request test supplies
        // independently rendered leaf/shim from genuine original declarations.
        let mut setup=TypeWorkBudget::with_limit(super::super::checked_request::RequestLimits::default().work);
        let data=fixture_data("leaf DATA","shim DATA",&mut setup);
        let mut work=TypeWorkBudget::with_limit(super::super::checked_request::RequestLimits::default().work);
        let canonical=data.reconstruct("leaf DATA","shim DATA",&mut work).unwrap();
        let cost=work.used();
        assert_eq!(data.reconstruct("leaf DATA","shim DATA",&mut TypeWorkBudget::with_limit(cost-1)),Err(Failure::Resource));
        for _ in 0..2 {
            let mut exact=TypeWorkBudget::with_limit(cost);
            assert_eq!(data.reconstruct("leaf DATA","shim DATA",&mut exact),Ok(canonical));
            assert_eq!(exact.used(),cost);
            assert_eq!(data.reconstruct("leaf DATA","shim DATA",&mut exact),Err(Failure::Resource));
        }
        for index in 0..7 {
            let mut donor=data.clone();
            match index {0=>donor.version=2,1=>donor.project_root=PathBuf::from("/tmp/donor"),2=>donor.manifest.push(b' '),3=>donor.leaf.push(b' '),4=>donor.shim.push(b' '),5=>donor.leaf_manifest.push(b' '),_=>donor.settled_lock=b"version = 3".to_vec()}
            assert!(donor.reconstruct("leaf DATA","shim DATA",&mut TypeWorkBudget::with_limit(super::super::checked_request::RequestLimits::default().work)).is_err());
        }
    }
}
