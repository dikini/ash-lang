//! Acyclic artifact-root code/configuration identity. This is data correspondence,
//! never applicability approval or a runtime admission capability.
use crate::types::TypeWorkBudget;
use sha2::{Digest, Sha256};

const TAG: &[u8] = b"Ash checked artifact root code/configuration v1\0";
const MAX_CODE_BYTES: usize = 32 * 1024 * 1024;
const MAX_MANIFEST_BYTES: usize = 64 * 1024;
const MAX_LOCK_BYTES: usize = 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Failure { Resource, Unsupported, Association }

/// Code/configuration DATA identity, with no approval/context constructor.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct RootCodeIdentity([u8; 32]);
impl RootCodeIdentity {
    pub(super) fn bytes(&self) -> &[u8; 32] { &self.0 }
}

/// Exact supported compiler/root configuration. Dynamic native file and owned
/// linker paths remain separately bound by the actual build/link receipt.
pub(super) struct Configuration<'a> {
    pub target: &'a str,
    pub canonical_source_root: &'a str,
    pub project_root: &'a str,
    pub profile: &'a str,
    pub optimization: &'a str,
    pub panic: &'a str,
    pub debug_assertions: bool,
    pub manifest: &'a [u8],
    pub build_configuration: &'a [u8],
    pub settled_lock: &'a [u8],
    pub leaf_manifest: &'a [u8],
    pub leaf: &'a [u8],
    pub shim: &'a [u8],
}
fn pay(work: &mut TypeWorkBudget, count: usize) -> Result<(), Failure> {
    work.charge(count).map_err(|()| Failure::Resource)
}
fn hex_pin(text: &str) -> Result<[u8; 32], Failure> {
    if text.len() != 64 { return Err(Failure::Association); }
    let mut bytes = [0; 32];
    for (pair, out) in text.as_bytes().chunks_exact(2).zip(&mut bytes) {
        let nibble = |byte| match byte {
            b'0'..=b'9' => Ok(byte - b'0'), b'a'..=b'f' => Ok(byte - b'a' + 10),
            _ => Err(Failure::Association),
        };
        *out = nibble(pair[0])? * 16 + nibble(pair[1])?;
    }
    Ok(bytes)
}
fn field(hash: &mut Sha256, tag: &[u8], bytes: &[u8], work: &mut TypeWorkBudget) -> Result<(), Failure> {
    let charge = tag.len().checked_add(bytes.len()).and_then(|n| n.checked_add(16)).ok_or(Failure::Resource)?;
    pay(work, charge)?;
    hash.update((tag.len() as u64).to_le_bytes()); hash.update(tag);
    hash.update((bytes.len() as u64).to_le_bytes()); hash.update(bytes);
    Ok(())
}
/// Derive from the compiler's independently hashed *source component*, never its
/// old configured runtime fingerprint. All variable Rust code is a named field;
/// non-Rust program payloads are bound separately by the final receipt/ELF.
pub(super) fn derive(config: &Configuration<'_>, work: &mut TypeWorkBudget) -> Result<RootCodeIdentity, Failure> {
    pay(work, 128)?;
    let component = hex_pin(env!("ASH_RUNTIME_SOURCE_COMPONENT"))?;
    let compiler = hex_pin(env!("ASH_RUNTIME_COMPILER_ID"))?;
    if cfg!(feature = "resource-calibration") || config.target != super::host::NATIVE_TARGET
        || config.profile != "debug" || config.optimization != "0"
        || config.panic != "unwind" || !config.debug_assertions {
        return Err(Failure::Unsupported);
    }
    for path in [config.canonical_source_root, config.project_root] {
        if path.len() > 4096 { return Err(Failure::Resource); }
        pay(work, path.len())?;
        if !std::path::Path::new(path).is_absolute() || path.chars().any(char::is_control)
            || std::path::Path::new(path).components().any(|p| matches!(p, std::path::Component::ParentDir | std::path::Component::CurDir)) {
            return Err(Failure::Unsupported);
        }
    }
    if config.build_configuration.is_empty() || config.build_configuration.len() > 16 * 1024 { return Err(Failure::Resource); }
    if config.manifest.is_empty() || config.manifest.len() > MAX_MANIFEST_BYTES
        || config.settled_lock.is_empty() || config.settled_lock.len() > MAX_LOCK_BYTES
        || config.leaf_manifest.is_empty() || config.leaf_manifest.len() > MAX_MANIFEST_BYTES
        || config.leaf.is_empty() || config.leaf.len() > MAX_CODE_BYTES
        || config.shim.is_empty() || config.shim.len() > MAX_CODE_BYTES {
        return Err(Failure::Resource);
    }
    let mut hash = Sha256::new();
    field(&mut hash, b"schema", TAG, work)?;
    field(&mut hash, b"canonical-source-component", &component, work)?;
    field(&mut hash, b"compiler-transcript", &compiler, work)?;
    field(&mut hash, b"canonical-source-path", config.canonical_source_root.as_bytes(), work)?;
    field(&mut hash, b"project-root", config.project_root.as_bytes(), work)?;
    field(&mut hash, b"target", config.target.as_bytes(), work)?;
    field(&mut hash, b"profile", config.profile.as_bytes(), work)?;
    field(&mut hash, b"optimization", config.optimization.as_bytes(), work)?;
    field(&mut hash, b"panic", config.panic.as_bytes(), work)?;
    field(&mut hash, b"debug-assertions", &[u8::from(config.debug_assertions)], work)?;
    field(&mut hash, b"root-cfg", b"ash_checked_owner_root=\"v1\"", work)?;
    field(&mut hash, b"features", b"", work)?;
    field(&mut hash, b"root-policy", b"unsafe_code=forbid;overflow-checks=true", work)?;
    field(&mut hash, b"root-rustc", b"linker=owned-observer;fuse-ld=bfd;crt-static;relocation=static;no-pie;strip=debuginfo", work)?;
    field(&mut hash, b"build-configuration", config.build_configuration, work)?;
    field(&mut hash, b"manifest", config.manifest, work)?;
    field(&mut hash, b"settled-lock", config.settled_lock, work)?;
    field(&mut hash, b"leaf-manifest", config.leaf_manifest, work)?;
    field(&mut hash, b"leaf-code", config.leaf, work)?;
    field(&mut hash, b"private-shim-code", config.shim, work)?;
    Ok(RootCodeIdentity(hash.finalize().into()))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn acyclic_root_code_identity_binds_every_code_field_and_paid_work() {
        let shim = crate::build::checked_leaf::render_root_shim(&mut TypeWorkBudget::default()).unwrap();
        let mut config = Configuration {
            target: super::super::host::NATIVE_TARGET, canonical_source_root: env!("ASH_RUNTIME_CANONICAL_SOURCE_ROOT"), project_root: "/owned/root-data",
            profile: "debug", optimization: "0", panic: "unwind", debug_assertions: true,
            manifest: b"fixed manifest DATA", build_configuration: b"closed build configuration DATA", settled_lock: b"settled lock DATA", leaf_manifest: b"fixed leaf manifest DATA",
            leaf: b"exact leaf code DATA", shim: shim.as_bytes(),
        };
        let mut work = TypeWorkBudget::default();
        let canonical = derive(&config, &mut work).unwrap();
        let cost = work.used();
        assert!(derive(&config, &mut TypeWorkBudget::with_limit(cost - 1)).is_err());
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(cost);
            assert_eq!(derive(&config, &mut exact).unwrap(), canonical);
            assert_eq!(exact.used(), cost);
            assert!(derive(&config, &mut exact).is_err());
        }
        for part in 0..5 {
            let original = match part { 0 => config.manifest, 1 => config.settled_lock, 2 => config.leaf, 3 => config.shim, _ => config.leaf_manifest };
            match part { 0 => config.manifest=b"donor", 1=>config.settled_lock=b"donor", 2=>config.leaf=b"donor", 3=>config.shim=b"donor", _=>config.leaf_manifest=b"donor" }
            assert_ne!(derive(&config, &mut TypeWorkBudget::default()).unwrap(), canonical);
            match part { 0=>config.manifest=original, 1=>config.settled_lock=original, 2=>config.leaf=original, 3=>config.shim=original, _=>config.leaf_manifest=original }
        }
        config.target = "unknown-target";
        assert_eq!(derive(&config, &mut TypeWorkBudget::default()), Err(Failure::Unsupported));
    }
}
