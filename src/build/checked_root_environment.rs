//! Closed Cargo build environment DATA. Cache/tool roots are explicit; ambient
//! executable, package, source, patch, env and profile overrides are not admitted.
use super::checked_root_identity::Failure;
use crate::types::TypeWorkBudget;
use serde::{Deserialize, Serialize};
use std::{path::{Path, PathBuf}, process::Command};
const MAX_CONFIGS: usize = 130;
const MAX_CONFIG_BYTES: usize = 64 * 1024;
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CargoConfiguration {
    pub path: PathBuf,
    pub bytes: Vec<u8>,
}
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Environment {
    pub version: u32,
    pub cargo: PathBuf,
    pub rustc: PathBuf,
    pub cargo_home: PathBuf,
    pub rustup_home: PathBuf,
    pub configurations: Vec<CargoConfiguration>,
}
fn pay(work: &mut TypeWorkBudget, n: usize) -> Result<(), Failure> { work.charge(n).map_err(|()| Failure::Resource) }
fn path(path: &Path, work: &mut TypeWorkBudget) -> Result<(), Failure> {
    let text = path.to_str().ok_or(Failure::Unsupported)?;
    if text.len() > 4096 { return Err(Failure::Resource); }
    pay(work, text.len())?;
    if !path.is_absolute() || text.chars().any(char::is_control)
        || path.components().any(|p| matches!(p, std::path::Component::ParentDir | std::path::Component::CurDir)) {
        return Err(Failure::Unsupported);
    }
    Ok(())
}
/// Supported inert aliases and build jobs/wrapper settings only. Wrappers are
/// explicitly disabled by the controlled command; no [env] or executable/source
/// remapping is accepted, including unknown future configuration sections.
pub(super) fn admit_configuration(bytes: &[u8], work: &mut TypeWorkBudget) -> Result<(), Failure> {
    if bytes.len() > MAX_CONFIG_BYTES { return Err(Failure::Resource); }
    pay(work, bytes.len().checked_mul(4).ok_or(Failure::Resource)?)?;
    let text = std::str::from_utf8(bytes).map_err(|_| Failure::Unsupported)?;
    let mut section = "";
    let mut seen = 0u8;
    for line in text.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') { continue; }
        if line.starts_with('[') {
            section = match line { "[alias]" => "alias", "[build]" => "build", _ => return Err(Failure::Unsupported) };
            continue;
        }
        let (key, value) = line.split_once('=').ok_or(Failure::Unsupported)?;
        let (key, value) = (key.trim(), value.trim());
        let bit = match (section, key) {
            ("alias", "xtask") if matches!(value, "\"run --package xtask --\"" | "\"run --package xtask --profile verification --\"") => 1,
            ("build", "jobs") if value == "1" => 2,
            ("build", "rustc-wrapper") => {
                // Retain its bytes as observed DATA but never execute it.
                let value: String = serde_json::from_str(value).map_err(|_| Failure::Unsupported)?;
                if value.len() > 4096 || value.chars().any(char::is_control) { return Err(Failure::Unsupported); }
                4
            }
            _ => return Err(Failure::Unsupported),
        };
        if seen & bit != 0 { return Err(Failure::Unsupported); }
        seen |= bit;
    }
    Ok(())
}
fn configuration_paths(project: &Path, cargo_home: &Path, work: &mut TypeWorkBudget) -> Result<Vec<PathBuf>, Failure> {
    let mut bytes = cargo_home.as_os_str().len().checked_mul(2).and_then(|n| n.checked_add(64)).ok_or(Failure::Resource)?;
    let mut count = 2usize;
    for (index, ancestor) in project.ancestors().enumerate() {
        if index >= 64 { return Err(Failure::Resource); }
        bytes = bytes.checked_add(ancestor.as_os_str().len().checked_mul(2).and_then(|n| n.checked_add(96)).ok_or(Failure::Resource)?).ok_or(Failure::Resource)?;
        count += 2;
    }
    pay(work, bytes.checked_add(count * std::mem::size_of::<PathBuf>()).ok_or(Failure::Resource)?)?;
    let mut result = Vec::new();
    result.try_reserve_exact(count).map_err(|_| Failure::Resource)?;
    for ancestor in project.ancestors() {
        result.push(ancestor.join(".cargo/config")); result.push(ancestor.join(".cargo/config.toml"));
    }
    result.push(cargo_home.join("config")); result.push(cargo_home.join("config.toml"));
    // At most130 entries; charge each actual full comparison and move before
    // work, rather than reserve a million units for absent configuration files.
    for index in 1..result.len() {
        let mut index = index;
        while index > 0 {
            let cost = result[index].as_os_str().len().checked_add(result[index-1].as_os_str().len()).and_then(|n| n.checked_mul(2)).and_then(|n| n.checked_add(3)).ok_or(Failure::Resource)?;
            pay(work, cost)?;
            if result[index-1] <= result[index] { break; }
            result.swap(index-1,index); index-=1;
        }
    }
    let mut index=1;
    while index<result.len() {
        pay(work, (result[index].as_os_str().len()+result[index-1].as_os_str().len())*2+1)?;
        if result[index]==result[index-1] { pay(work,result.len()-index)?; result.remove(index); }
        else { index+=1; }
    }
    Ok(result)
}
fn read_configurations(project: &Path, home: &Path, work: &mut TypeWorkBudget) -> Result<Vec<CargoConfiguration>, Failure> {
    use std::{io::Read, os::unix::fs::{MetadataExt, OpenOptionsExt}};
    let paths = configuration_paths(project, home, work)?;
    let mut configs = Vec::new();
    for path in paths {
        pay(work, 16)?;
        let mut file = match std::fs::OpenOptions::new().read(true).custom_flags(0x20000 | 0x80000 | 0x800).open(&path) {
            Ok(file) => file,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(_) => return Err(Failure::Unsupported),
        };
        let before = file.metadata().map_err(|_| Failure::Association)?;
        if !before.is_file() || before.len() > MAX_CONFIG_BYTES as u64 { return Err(Failure::Unsupported); }
        let bound=usize::try_from(before.len()).map_err(|_| Failure::Resource)?.checked_add(1).ok_or(Failure::Resource)?;
        pay(work, bound.checked_mul(8).ok_or(Failure::Resource)?)?;
        let mut bytes = Vec::new();
        (&mut file).take(bound as u64).read_to_end(&mut bytes).map_err(|_| Failure::Association)?;
        let after = file.metadata().map_err(|_| Failure::Association)?;
        if bytes.len() as u64 != before.len() || (before.dev(),before.ino(),before.len(),before.mtime(),before.mtime_nsec(),before.ctime(),before.ctime_nsec())
            != (after.dev(),after.ino(),after.len(),after.mtime(),after.mtime_nsec(),after.ctime(),after.ctime_nsec()) { return Err(Failure::Association); }
        admit_configuration(&bytes, work)?;
        configs.push(CargoConfiguration { path, bytes });
    }
    Ok(configs)
}
impl Environment {
    pub(super) fn discover(project: &Path, work: &mut TypeWorkBudget) -> Result<Self, Failure> {
        let cargo_home = PathBuf::from(env!("ASH_BUILD_CARGO_HOME"));
        let rustup_home = PathBuf::from(env!("ASH_BUILD_RUSTUP_HOME"));
        let mut result = Self { version: 1, cargo: PathBuf::from(env!("CARGO")), rustc: PathBuf::from(env!("ASH_RUNTIME_RUSTC_PATH")), cargo_home, rustup_home, configurations: Vec::new() };
        for p in [project, &result.cargo, &result.rustc, &result.cargo_home, &result.rustup_home] { path(p, work)?; }
        result.configurations = read_configurations(project, &result.cargo_home, work)?;
        Ok(result)
    }
    pub(super) fn admit_data(&self, project: &Path, work: &mut TypeWorkBudget) -> Result<(), Failure> {
        if self.version != 1 || self.configurations.len() > MAX_CONFIGS { return Err(Failure::Unsupported); }
        for p in [project,&self.cargo,&self.rustc,&self.cargo_home,&self.rustup_home] { path(p,work)?; }
        pay(work, self.cargo.as_os_str().len()+self.rustc.as_os_str().len()+self.cargo_home.as_os_str().len()+self.rustup_home.as_os_str().len())?;
        if self.cargo != Path::new(env!("CARGO")) || self.rustc != Path::new(env!("ASH_RUNTIME_RUSTC_PATH"))
            || self.cargo_home != Path::new(env!("ASH_BUILD_CARGO_HOME")) || self.rustup_home != Path::new(env!("ASH_BUILD_RUSTUP_HOME")) { return Err(Failure::Association); }
        let permitted=configuration_paths(project,&self.cargo_home,work)?;
        let mut previous: Option<&Path> = None;
        for config in &self.configurations {
            path(&config.path,work)?;
            for candidate in &permitted { pay(work, candidate.as_os_str().len()+config.path.as_os_str().len()+1)?; }
            if !permitted.contains(&config.path) { return Err(Failure::Association); }
            if let Some(previous)=previous {
                pay(work,previous.as_os_str().len()+config.path.as_os_str().len()+1)?;
                if previous >= config.path.as_path() { return Err(Failure::Association); }
            }
            previous=Some(&config.path);
            admit_configuration(&config.bytes,work)?;
        }
        Ok(())
    }
    pub(super) fn verify(&self, project: &Path, work: &mut TypeWorkBudget) -> Result<(), Failure> {
        self.admit_data(project,work)?;
        if read_configurations(project, &self.cargo_home, work)? != self.configurations { return Err(Failure::Association); }
        Ok(())
    }
    pub(super) fn command(&self, project: &Path, verb: &str, work: &mut TypeWorkBudget) -> Result<Command, Failure> {
        self.verify(project, work)?;
        let bytes = self.cargo.as_os_str().len().checked_add(self.rustc.as_os_str().len())
            .and_then(|n| n.checked_add(self.cargo_home.as_os_str().len()))
            .and_then(|n| n.checked_add(self.rustup_home.as_os_str().len()))
            .and_then(|n| n.checked_add(project.as_os_str().len()))
            .and_then(|n| n.checked_add(2048)).and_then(|n| n.checked_mul(8)).ok_or(Failure::Resource)?;
        pay(work, bytes)?;
        if !matches!(verb, "rustc" | "generate-lockfile") { return Err(Failure::Unsupported); }
        let bin = self.rustc.parent().ok_or(Failure::Unsupported)?;
        let search = std::env::join_paths([bin, Path::new("/usr/bin"), Path::new("/bin")]).map_err(|_| Failure::Unsupported)?;
        let mut command = Command::new(&self.cargo);
        command.current_dir(project).arg(verb).arg("--offline").env_clear()
            .env("PATH", search).env("CARGO_HOME", &self.cargo_home).env("RUSTUP_HOME", &self.rustup_home)
            .env("RUSTC", &self.rustc).env("LC_ALL", "C").env("LANG", "C").env("TZ", "UTC")
            .env("CARGO_BUILD_JOBS", "1").env("CARGO_INCREMENTAL", "0")
            .env("CARGO_ENCODED_RUSTFLAGS", "").env("RUSTC_WRAPPER", "").env("RUSTC_WORKSPACE_WRAPPER", "");
        for value in ["profile.dev.opt-level=0", "profile.dev.panic=\"unwind\"", "profile.dev.debug-assertions=true", "profile.dev.overflow-checks=true", "profile.dev.incremental=false", "build.rustc-wrapper=\"\"", "build.rustc-workspace-wrapper=\"\""] {
            command.arg("--config").arg(value);
        }
        Ok(command)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn closed_configuration_refuses_executable_profile_source_and_forced_env_inputs() {
        let canonical=b"[alias]\nxtask = \"run --package xtask --\"\n[build]\njobs = 1\nrustc-wrapper = \"/observed/disabled-wrapper\"\n";
        let mut measured=TypeWorkBudget::default();
        admit_configuration(canonical,&mut measured).unwrap();
        let cost=measured.used();
        assert_eq!(admit_configuration(canonical,&mut TypeWorkBudget::with_limit(cost-1)),Err(Failure::Resource));
        for _ in 0..2 { let mut exact=TypeWorkBudget::with_limit(cost);admit_configuration(canonical,&mut exact).unwrap();assert_eq!(exact.used(),cost);assert_eq!(admit_configuration(canonical,&mut exact),Err(Failure::Resource)); }
        for donor in ["[env]\nRUSTC = { value = \"donor\", force = true }\n","[profile.dev.package.ash]\nopt-level = 3\n","[profile.dev.build-override]\nopt-level = 3\n","[patch.crates-io]\nsha2 = { path = \"/donor\" }\n","[source.crates-io]\nreplace-with = \"donor\"\n","[build]\nrustflags = [\"--cfg\", \"donor\"]\n"] {
            assert_eq!(admit_configuration(donor.as_bytes(),&mut TypeWorkBudget::default()),Err(Failure::Unsupported));
        }
    }
    #[test]
    fn actual_config_discovery_is_funded_and_deserialized_selection_is_revalidated() {
        let project=Path::new("/tmp/ash-root-request-data-only/root");
        let mut measured=TypeWorkBudget::default();
        let canonical=Environment::discover(project,&mut measured).unwrap();
        let cost=measured.used();
        assert!(matches!(Environment::discover(project,&mut TypeWorkBudget::with_limit(cost-1)),Err(Failure::Resource)));
        for _ in 0..2 { let mut exact=TypeWorkBudget::with_limit(cost);assert_eq!(Environment::discover(project,&mut exact).unwrap(),canonical);assert_eq!(exact.used(),cost);assert!(Environment::discover(project,&mut exact).is_err()); }
        canonical.verify(project,&mut TypeWorkBudget::default()).unwrap();
        for index in 0..5 {
            let mut donor=canonical.clone();
            match index {0=>donor.cargo="/tmp/donor-cargo".into(),1=>donor.rustc="/tmp/donor-rustc".into(),2=>donor.cargo_home="/tmp/donor-home".into(),3=>donor.rustup_home="/tmp/donor-rustup".into(),_=>donor.configurations.push(CargoConfiguration{path:"/tmp/unsearched/config.toml".into(),bytes:Vec::new()})}
            assert_eq!(donor.admit_data(project,&mut TypeWorkBudget::default()),Err(Failure::Association));
        }
    }
}
