use crate::{Budget, PreparationLimits, Refusal, SealedData, io, linux};
use ash::build::{ApplicabilityRequest, ArtifactPin, RequestLimits};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::{
    ffi::CString,
    fs::File,
    io::Read,
    os::unix::fs::MetadataExt,
    path::{Component, Path},
};
const BOOT_BYTES: usize = 65536;
const BOOT_WORK: usize = 4 * 1024 * 1024;
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Identity {
    device: u64,
    inode: u64,
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    version: u32,
    uid: u32,
    gid: u32,
    groups: Vec<u32>,
    user_namespace: Identity,
    mount_namespace: Identity,
    uid_map_sha256: String,
    mountinfo_sha256: String,
    store: String,
    store_identity: Identity,
    stdio: String,
    context_version: u32,
    premise_version: u32,
    launch_version: u32,
    request_bytes: usize,
    request_work: usize,
    image_bytes: usize,
    image_work: usize,
    program_headers: usize,
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Pin {
    bytes: u64,
    sha256: String,
}
impl Pin {
    fn matches(&self, p: ArtifactPin) -> bool {
        self.bytes == p.bytes && self.sha256 == hex(&p.sha256)
    }
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Approval {
    version: u32,
    request: Pin,
    receipt: Pin,
    image: Pin,
    premises: Pin,
    context_sha256: String,
    target: String,
    mode: String,
    role: String,
    context_version: u32,
    premise_version: u32,
    launch_version: u32,
}
struct InstalledContext {
    config: Config,
    store: File,
    config_file: File,
    config_metadata: std::fs::Metadata,
    context_pin: [u8; 32],
}
/// Non-executing prepared image. Construction is private to the fixed protected
/// consumer; no caller path/context/token or deserialized bit can create it.
#[derive(Debug)]
pub struct PreparedImage {
    sealed: SealedData,
    _snapshot: Vec<u8>,
    _context_pin: [u8; 32],
}
impl PreparedImage {
    /// Immutable image data pin. This does not expose an execution operation.
    pub fn image_pin(&self) -> ArtifactPin {
        self.sealed.pin()
    }
}
/// Validate the installed fixed administrator association, independently read a
/// protected approval snapshot, then prepare sealed immutable bytes. Candidate
/// pathname and request bytes are DATA only; neither selects config/store.
/// Default uninstalled builds refuse MissingDeployment. No provisioning or exec.
pub fn prepare(request_bytes: &[u8], candidate: &Path) -> Result<PreparedImage, Refusal> {
    let mut budget = Budget::new(BOOT_WORK);
    let installed = bootstrap(&mut budget)?;
    let config = &installed.config;
    let request = ApplicabilityRequest::decode(
        request_bytes,
        RequestLimits {
            bytes: config.request_bytes,
            work: config.request_work,
        },
    )
    .map_err(|_| Refusal::Malformed)?;
    request.check_complete().map_err(|_| Refusal::Incomplete)?;
    let name = CString::new(hex(&request.request_pin().sha256)).map_err(|_| Refusal::Malformed)?;
    let mut approval = linux::open_child(&installed.store, &name, false)?;
    let before = protected_metadata(&approval, false)?;
    let bytes = bounded_read(&mut approval, BOOT_BYTES, &mut budget)?;
    budget.pay(bytes.len().checked_mul(4).ok_or(Refusal::Resource)?)?;
    let parsed: Approval = serde_json::from_slice(&bytes).map_err(|_| Refusal::Malformed)?;
    validate_approval(&parsed, &request, config, &installed.context_pin)?;
    if request.context_pin()
        != Some(ArtifactPin {
            bytes: installed.config_metadata.len(),
            sha256: installed.context_pin,
        })
    {
        return Err(Refusal::Association);
    }
    same_metadata(&before, &io(approval.metadata())?)?;
    same_metadata(
        &installed.config_metadata,
        &io(installed.config_file.metadata())?,
    )?;
    use std::os::unix::fs::OpenOptionsExt;
    let mut source = io(std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(0x80000 | 0x20000 | 0x800)
        .open(candidate))?;
    let sealed = SealedData::copy(
        &mut source,
        request.final_image_pin().ok_or(Refusal::Incomplete)?,
        PreparationLimits {
            image_bytes: config.image_bytes,
            work: config.image_work,
            program_headers: config.program_headers,
        },
    )?;
    check_context(config, &mut budget)?;
    // Store/config handles close here; only immutable bytes and snapshot data
    // survive. No runtime/provider receives store management handles.
    Ok(PreparedImage {
        sealed,
        _snapshot: bytes,
        _context_pin: installed.context_pin,
    })
}
fn validate_approval(
    a: &Approval,
    r: &ApplicabilityRequest,
    c: &Config,
    context: &[u8; 32],
) -> Result<(), Refusal> {
    if a.version != 1
        || a.context_version != c.context_version
        || a.premise_version != c.premise_version
        || a.launch_version != c.launch_version
    {
        return Err(Refusal::Malformed);
    }
    if a.target != "x86_64-unknown-linux-gnu"
        || a.mode != "checked-inprocess-static"
        || a.role != "checked-preparation"
        || a.context_sha256 != hex(context)
        || !a.request.matches(r.request_pin())
        || !a.receipt.matches(r.receipt_pin())
        || !a.premises.matches(r.premise_pin())
        || !a
            .image
            .matches(r.final_image_pin().ok_or(Refusal::Incomplete)?)
    {
        return Err(Refusal::Association);
    }
    Ok(())
}
fn bootstrap(budget: &mut Budget) -> Result<InstalledContext, Refusal> {
    let path = option_env!("ASH_PROTECTED_CONFIG_PATH").ok_or(Refusal::MissingDeployment)?;
    let expected = option_env!("ASH_PROTECTED_CONFIG_SHA256").ok_or(Refusal::MissingDeployment)?;
    if !valid_hash(expected) {
        return Err(Refusal::MissingDeployment);
    }
    // Bootstrap bounds and environment/descriptor policy precede config decode.
    if std::env::vars_os().next().is_some() {
        return Err(Refusal::Context);
    }
    budget.pay(256 * 8192 + 8192)?;
    linux::standard_fds()?;
    linux::inherited_fds()?;
    let mut file = walk(Path::new(path), false, budget)?;
    let metadata = protected_metadata(&file, false)?;
    let bytes = bounded_read(&mut file, BOOT_BYTES, budget)?;
    budget.pay(bytes.len())?;
    let context_pin: [u8; 32] = Sha256::digest(&bytes).into();
    if hex(&context_pin) != expected {
        return Err(Refusal::Association);
    }
    budget.pay(bytes.len().checked_mul(4).ok_or(Refusal::Resource)?)?;
    let config: Config = serde_json::from_slice(&bytes).map_err(|_| Refusal::Malformed)?;
    validate_config(&config)?;
    check_context(&config, budget)?;
    let store = walk(Path::new(&config.store), true, budget)?;
    let store_meta = protected_metadata(&store, true)?;
    if store_meta.dev() != config.store_identity.device
        || store_meta.ino() != config.store_identity.inode
    {
        return Err(Refusal::Context);
    }
    same_metadata(&metadata, &io(file.metadata())?)?;
    Ok(InstalledContext {
        config,
        store,
        config_file: file,
        config_metadata: metadata,
        context_pin,
    })
}
fn validate_config(c: &Config) -> Result<(), Refusal> {
    if c.version != 1 || c.context_version != 1 || c.premise_version != 1 || c.launch_version != 1 {
        return Err(Refusal::Malformed);
    }
    if c.stdio != "null-read-null-write-v1" {
        return Err(Refusal::Context);
    }
    if c.uid == 0
        || c.gid == 0
        || c.groups.len() > 128
        || c.groups.windows(2).any(|p| p[0] >= p[1])
        || !valid_hash(&c.uid_map_sha256)
        || !valid_hash(&c.mountinfo_sha256)
    {
        return Err(Refusal::Context);
    }
    if c.request_bytes == 0
        || c.request_bytes > 64 * 1024 * 1024
        || c.request_work == 0
        || c.request_work > 1024 * 1024 * 1024
        || c.image_bytes == 0
        || c.image_bytes > 2usize.pow(31)
        || c.image_work == 0
        || c.image_work > 16 * 1024 * 1024 * 1024
        || c.program_headers == 0
        || c.program_headers > 4096
    {
        return Err(Refusal::Resource);
    }
    Ok(())
}
fn check_context(c: &Config, budget: &mut Budget) -> Result<(), Refusal> {
    let (uids, gids) = linux::credentials()?;
    if uids != [c.uid; 3] || gids != [c.gid; 3] {
        return Err(Refusal::Context);
    }
    let proc = linux::calling_thread_proc()?;
    let namespace = linux::proc_child(&proc, c"ns", true)?;
    for (name, identity) in [(c"user", &c.user_namespace), (c"mnt", &c.mount_namespace)] {
        budget.pay(1)?;
        let file = linux::namespace(&namespace, name)?;
        let m = io(file.metadata())?;
        if m.dev() != identity.device || m.ino() != identity.inode {
            return Err(Refusal::Context);
        }
    }
    for (name, expected) in [
        (c"uid_map", &c.uid_map_sha256),
        (c"mountinfo", &c.mountinfo_sha256),
    ] {
        let mut file = linux::proc_child(&proc, name, false)?;
        let b = bounded_read(&mut file, BOOT_BYTES, budget)?;
        budget.pay(b.len())?;
        if hex(&Sha256::digest(&b)) != *expected {
            return Err(Refusal::Context);
        }
    }
    let mut status = linux::proc_child(&proc, c"status", false)?;
    let raw = bounded_read(&mut status, BOOT_BYTES, budget)?;
    let text = std::str::from_utf8(&raw).map_err(|_| Refusal::Malformed)?;
    check_status(text, c, budget)
}
fn check_status(text: &str, c: &Config, budget: &mut Budget) -> Result<(), Refusal> {
    let mut seen = [false; 9];
    for line in text.lines() {
        budget.pay(line.len() + 1)?;
        let Some((key, value)) = line.split_once(':') else {
            return Err(Refusal::Malformed);
        };
        let slot = match key {
            "Uid" => 0,
            "Gid" => 1,
            "Groups" => 2,
            "CapInh" => 3,
            "CapPrm" => 4,
            "CapEff" => 5,
            "CapAmb" => 6,
            "Threads" => 7,
            "TracerPid" => 8,
            _ => continue,
        };
        if std::mem::replace(&mut seen[slot], true) {
            return Err(Refusal::Malformed);
        }
        if slot < 2 {
            let values = value
                .split_whitespace()
                .map(str::parse::<u32>)
                .collect::<Result<Vec<_>, _>>()
                .map_err(|_| Refusal::Malformed)?;
            // Four kernel status IDs include FSUID/FSGID, unlike getres* alone.
            if values != vec![if slot == 0 { c.uid } else { c.gid }; 4] {
                return Err(Refusal::Context);
            }
        } else if slot == 2 {
            let groups = value
                .split_whitespace()
                .map(str::parse::<u32>)
                .collect::<Result<Vec<_>, _>>()
                .map_err(|_| Refusal::Malformed)?;
            if groups != c.groups {
                return Err(Refusal::Context);
            }
        } else if slot == 7 {
            if value.trim() != "1" {
                return Err(Refusal::Context);
            }
        } else if slot == 8 {
            if value.trim() != "0" {
                return Err(Refusal::Context);
            }
        } else if value.trim() != "0000000000000000" {
            return Err(Refusal::Context);
        }
    }
    if seen.iter().any(|v| !*v) {
        return Err(Refusal::Malformed);
    }
    Ok(())
}
fn walk(path: &Path, directory: bool, budget: &mut Budget) -> Result<File, Refusal> {
    if !path.is_absolute() || path.as_os_str().len() > 4096 {
        return Err(Refusal::Context);
    }
    let names = path
        .components()
        .skip(1)
        .map(|c| match c {
            Component::Normal(n) => Ok(n),
            _ => Err(Refusal::Context),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if names.is_empty() || names.len() > 64 {
        return Err(Refusal::Context);
    }
    let mut current = io(File::open("/"))?;
    protected_metadata(&current, true)?;
    for (i, name) in names.iter().enumerate() {
        budget.pay(name.len() + 1)?;
        let name = CString::new(name.as_encoded_bytes()).map_err(|_| Refusal::Context)?;
        let is_dir = i + 1 < names.len() || directory;
        let child = linux::open_child(&current, &name, is_dir)?;
        protected_metadata(&child, is_dir)?;
        current = child;
    }
    Ok(current)
}
fn protected_metadata(file: &File, directory: bool) -> Result<std::fs::Metadata, Refusal> {
    let m = io(file.metadata())?;
    if m.uid() != 0
        || m.mode() & 0o022 != 0
        || (if directory {
            !m.is_dir()
        } else {
            !m.is_file() || m.nlink() != 1
        })
    {
        return Err(Refusal::Context);
    }
    linux::no_acl(file)?;
    Ok(m)
}
fn bounded_read(file: &mut File, cap: usize, budget: &mut Budget) -> Result<Vec<u8>, Refusal> {
    let mut bytes = Vec::new();
    let mut buffer = [0u8; 8192];
    loop {
        let remaining = cap.checked_sub(bytes.len()).ok_or(Refusal::Resource)?;
        let count = buffer.len().min(remaining.saturating_add(1));
        budget.pay(count)?;
        let n = io(file.read(&mut buffer[..count]))?;
        if n == 0 {
            break;
        }
        if n > remaining {
            return Err(Refusal::Resource);
        }
        bytes.try_reserve(n).map_err(|_| Refusal::Resource)?;
        bytes.extend_from_slice(&buffer[..n]);
    }
    Ok(bytes)
}
fn same_metadata(a: &std::fs::Metadata, b: &std::fs::Metadata) -> Result<(), Refusal> {
    if (
        a.dev(),
        a.ino(),
        a.len(),
        a.mode(),
        a.uid(),
        a.gid(),
        a.mtime(),
        a.mtime_nsec(),
        a.ctime(),
        a.ctime_nsec(),
    ) != (
        b.dev(),
        b.ino(),
        b.len(),
        b.mode(),
        b.uid(),
        b.gid(),
        b.mtime(),
        b.mtime_nsec(),
        b.ctime(),
        b.ctime_nsec(),
    ) {
        Err(Refusal::Association)
    } else {
        Ok(())
    }
}
fn valid_hash(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}
fn hex(bytes: &[u8]) -> String {
    const H: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push(H[(b >> 4) as usize] as char);
        s.push(H[(b & 15) as usize] as char);
    }
    s
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn absent_fixed_deployment_and_same_uid_store_refuse_without_authority() {
        if option_env!("ASH_PROTECTED_CONFIG_PATH").is_none() {
            assert_eq!(
                prepare(b"untrusted", Path::new("/never-opened")).unwrap_err(),
                Refusal::MissingDeployment
            );
        }
        let directory = crate::test_directory("untrusted-store");
        let path = directory.join("claims");
        std::fs::write(&path, b"claims").unwrap();
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o666)).unwrap();
        let file = File::open(&path).unwrap();
        assert_eq!(
            protected_metadata(&file, false).unwrap_err(),
            Refusal::Context
        );
        let mut budget = Budget::new(BOOT_WORK);
        assert!(walk(&path, false, &mut budget).is_err());
        std::fs::remove_dir_all(directory).unwrap();
    }
    #[test]
    fn status_fsids_capabilities_and_versions_are_exact_data_checks() {
        let c:Config=serde_json::from_value(serde_json::json!({"version":1,"uid":1234,"gid":1234,"groups":[1234],"user_namespace":{"device":1,"inode":2},"mount_namespace":{"device":1,"inode":3},"uid_map_sha256":"00".repeat(32),"mountinfo_sha256":"00".repeat(32),"store":"/fixed/store","store_identity":{"device":1,"inode":4},"stdio":"null-read-null-write-v1","context_version":1,"premise_version":1,"launch_version":1,"request_bytes":4096,"request_work":4096,"image_bytes":4096,"image_work":16384,"program_headers":4})).unwrap();
        validate_config(&c).unwrap();
        let text = "Uid:\t1234 1234 1234 1234\nGid:\t1234 1234 1234 1234\nGroups:\t1234\nCapInh:\t0000000000000000\nCapPrm:\t0000000000000000\nCapEff:\t0000000000000000\nCapAmb:\t0000000000000000\nThreads:\t1\nTracerPid:\t0\n";
        check_status(text, &c, &mut Budget::new(4096)).unwrap();
        for donor in [
            text.replacen("1234 1234 1234 1234", "1234 1234 1234 0", 1),
            text.replace("CapEff:\t0000000000000000", "CapEff:\t0000000000000001"),
            text.replace("Groups:\t1234", "Groups:\t1234 0"),
        ] {
            assert_eq!(
                check_status(&donor, &c, &mut Budget::new(4096)),
                Err(Refusal::Context)
            );
        }
        assert_eq!(
            check_status(text, &c, &mut Budget::new(1)),
            Err(Refusal::Resource)
        );
        let mut unknown = serde_json::to_value(serde_json::json!({"version":2})).unwrap();
        // Unknown/incomplete config is refused by the real strict parser, not
        // hidden behind MissingDeployment in these data-level controls.
        assert!(serde_json::from_value::<Config>(unknown.take()).is_err());
        let directory = crate::test_directory("replacement");
        let path = directory.join("file");
        std::fs::write(&path, b"before").unwrap();
        let old = File::open(&path).unwrap();
        let before = old.metadata().unwrap();
        std::fs::remove_file(&path).unwrap();
        std::fs::write(&path, b"after").unwrap();
        assert_eq!(
            same_metadata(&before, &std::fs::metadata(&path).unwrap()),
            Err(Refusal::Association)
        );
        std::fs::remove_dir_all(directory).unwrap();
    }
}

#[cfg(test)]
mod artifact_data_tests {
    use super::*;
    #[test]
    #[ignore = "assigned actual current static artifact data only; no startup or protected positive"]
    fn actual_request_and_sealed_elf_are_data_not_protected_applicability() {
        let request_path = std::path::PathBuf::from(
            std::env::var_os("ASH_PREPARATION_REQUEST_PATH")
                .expect("explicit actual request DATA path"),
        );
        let image_path = std::path::PathBuf::from(
            std::env::var_os("ASH_PREPARATION_IMAGE_PATH").expect("explicit actual ELF DATA path"),
        );
        let mut request_file = File::open(&request_path).unwrap();
        let bytes = bounded_read(
            &mut request_file,
            RequestLimits::default().bytes,
            &mut Budget::new(RequestLimits::default().work),
        )
        .unwrap();
        let request = ApplicabilityRequest::decode(&bytes, RequestLimits::default()).unwrap();
        assert!(request.linked());
        assert_eq!(request.missing_fields().len(), 6);
        assert!(request.check_complete().is_err());
        let mut source = File::open(&image_path).unwrap();
        let expected = request.final_image_pin().unwrap();
        let sealed = SealedData::copy(
            &mut source,
            expected,
            PreparationLimits {
                image_bytes: 2usize.pow(31),
                work: 16 * 1024 * 1024 * 1024,
                program_headers: 64,
            },
        )
        .unwrap();
        assert_eq!(sealed.pin(), expected);
        assert_eq!(sealed.seals().unwrap(), 15);
        // This is the private pure association predicate with explicitly
        // untrusted Config/Approval DATA, not bootstrap, context installation,
        // approval truth, completeness or PreparedImage construction.
        let context = [7; 32];
        let config: Config = serde_json::from_value(serde_json::json!({
            "version": 1, "uid": 1000, "gid": 1000, "groups": [],
            "user_namespace": {"device": 1, "inode": 2},
            "mount_namespace": {"device": 1, "inode": 3},
            "uid_map_sha256": "0".repeat(64), "mountinfo_sha256": "0".repeat(64),
            "store": "/untrusted-approval-data/store", "store_identity": {"device": 1, "inode": 4},
            "stdio": "null-read-null-write-v1", "context_version": 1,
            "premise_version": 1, "launch_version": 1,
            "request_bytes": RequestLimits::default().bytes,
            "request_work": RequestLimits::default().work,
            "image_bytes": 2usize.pow(31), "image_work": 16 * 1024 * 1024 * 1024usize,
            "program_headers": 64
        }))
        .unwrap();
        validate_config(&config).unwrap();
        let claimed_pin = |p: ArtifactPin| Pin {
            bytes: p.bytes,
            sha256: hex(&p.sha256),
        };
        let approval_data = || Approval {
            version: 1,
            request: claimed_pin(request.request_pin()),
            receipt: claimed_pin(request.receipt_pin()),
            image: claimed_pin(expected),
            premises: claimed_pin(request.premise_pin()),
            context_sha256: hex(&context),
            target: "x86_64-unknown-linux-gnu".into(),
            mode: "checked-inprocess-static".into(),
            role: "checked-preparation".into(),
            context_version: 1,
            premise_version: 1,
            launch_version: 1,
        };
        assert_eq!(
            validate_approval(&approval_data(), &request, &config, &context),
            Ok(())
        );
        let change_digest = |pin: &mut Pin| {
            let changed = if pin.sha256.starts_with('0') {
                "1"
            } else {
                "0"
            };
            pin.sha256.replace_range(..1, changed);
        };
        for change in 0..16 {
            let mut donor = approval_data();
            match change {
                0 => donor.version = 2,
                1 => donor.context_version = 2,
                2 => donor.premise_version = 2,
                3 => donor.launch_version = 2,
                4 => change_digest(&mut donor.request),
                5 => change_digest(&mut donor.receipt),
                6 => change_digest(&mut donor.image),
                7 => change_digest(&mut donor.premises),
                8 => donor.context_sha256.push('0'),
                9 => donor.target.push('!'),
                10 => donor.mode.push('!'),
                11 => donor.role.push('!'),
                12 => donor.request.bytes += 1,
                13 => donor.receipt.bytes += 1,
                14 => donor.image.bytes += 1,
                _ => donor.premises.bytes += 1,
            }
            assert_eq!(
                validate_approval(&donor, &request, &config, &context),
                Err(if change < 4 {
                    Refusal::Malformed
                } else {
                    Refusal::Association
                }),
                "untrusted approval DATA mutation {change}"
            );
        }
        println!(
            "SEALED_PREPARATION_DATA {}",
            serde_json::json!({
                "request": request_path, "image": image_path,
                "image_bytes": expected.bytes, "image_sha256": hex(&expected.sha256),
                "seals": sealed.seals().unwrap(), "protected_positive": false,
            })
        );
        // This absent-install refusal is not a protected positive or deep
        // approval negative. The current request also has incomplete closure.
        if option_env!("ASH_PROTECTED_CONFIG_PATH").is_none() {
            assert_eq!(
                prepare(&bytes, &image_path).unwrap_err(),
                Refusal::MissingDeployment
            );
        }
    }
}
