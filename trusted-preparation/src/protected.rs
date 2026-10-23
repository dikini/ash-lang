use crate::{Budget, PreparationLimits, Refusal, SealedData, io, linux};
use ash::build::{ApplicabilityRequest, ArtifactPin, RequestLimits};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::{
    ffi::CString,
    fs::File,
    io::{Read, Seek, SeekFrom},
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
    launcher: Option<Pin>,
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
    let installed = bootstrap(&mut budget, Ingress::Preparation)?;
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
/// Privately verified actual running image and inherited report endpoint.
/// This non-Clone value carries no dependency-Ash Core/types into its consumer.
/// Its constructor is the fixed live verifier, never serialized request DATA.
pub struct VerifiedRunning {
    request: Vec<u8>,
    request_pin: ArtifactPin,
    image_pin: ArtifactPin,
    embedded: [(u64, [u8; 32]); 4],
    report: crate::outcome::ReportWriter,
}
impl VerifiedRunning {
    /// Exact bounded request framing for independent root-local restoration.
    pub fn request_bytes(&self) -> &[u8] { &self.request }
    /// Primitive data correspondence; not a caller-created applicability token.
    pub fn request_pin(&self) -> (u64, [u8; 32]) { (self.request_pin.bytes, self.request_pin.sha256) }
    /// Primitive image/facts/policy/runtime pins, in that fixed order. The root
    /// must independently hash its embedded bytes and restore its own originals.
    pub fn embedded_pins(&self) -> [(u64, [u8; 32]); 4] { self.embedded }
    /// Reserve fixed closing and terminal wire capacity before evaluator entry.
    /// This is output budgeting only; it grants no source/native permission.
    pub fn reserve_outcome_closings(&mut self, count: usize) -> Result<(), Refusal> {
        self.report.reserve_closings(count)
    }
    /// Finish the mandatory closing prefix and release unused closing capacity.
    /// Terminal capacity remains protected from optional result/Trace output.
    pub fn finish_outcome_closings(&mut self) -> Result<(), Refusal> { self.report.finish_closings() }
    /// Write one fixed, bounded v2 observation frame to the independently bound
    /// nonblocking parent endpoint. IO failure poisons the stream; this method
    /// never retries a native action or fabricates consumption from process state.
    pub fn write_outcome_frame(&mut self, kind: crate::OutcomeFrameKind, payload: &[u8]) -> Result<(), Refusal> {
        self.report.write(kind, payload)
    }
    /// Final running executable correspondence, with no nominal Ash type cast.
    pub fn image_pin(&self) -> (u64, [u8; 32]) { (self.image_pin.bytes, self.image_pin.sha256) }
}
/// Verify the current executable and fixed v2 ingress against real protected
/// approval. No argument selects a path, context, success bit or store. Ordinary
/// unconfigured builds refuse before touching incoming descriptors.
pub fn verify_running() -> Result<VerifiedRunning, Refusal> {
    let mut budget = Budget::new(BOOT_WORK);
    let installed = bootstrap(&mut budget, Ingress::Root)?;
    let c = &installed.config;
    let parent = crate::running::ParentPipe::inspect(&mut budget)?;
    check_proc_context(c, parent.parent(), &mut budget)?;
    let (request_flags, request_descriptor) = linux::role_flags(4)?;
    if request_flags & !0x8000 != 0 || request_descriptor != 0 { return Err(Refusal::Context); }
    let mut source = linux::duplicate_role(4)?;
    let mut request_work = Budget::new(c.request_work);
    let bytes = read_sealed_request(&mut source, c.request_bytes, &mut request_work)?;
    let request = ApplicabilityRequest::decode(&bytes, RequestLimits {
        bytes: c.request_bytes, work: request_work.remaining,
    }).map_err(|error| match error {
        ash::build::ReceiptFailure::Resource => Refusal::Resource,
        _ => Refusal::Malformed,
    })?;
    request.check_complete().map_err(|_| Refusal::Incomplete)?;
    if request.context_pin() != Some(ArtifactPin { bytes: installed.config_metadata.len(), sha256: installed.context_pin }) {
        return Err(Refusal::Association);
    }
    budget.pay(65)?;
    let name = CString::new(hex(&request.request_pin().sha256)).map_err(|_| Refusal::Malformed)?;
    let mut approval = linux::open_child(&installed.store, &name, false)?;
    let approval_before = protected_metadata(&approval, false)?;
    let raw = bounded_read(&mut approval, BOOT_BYTES, &mut budget)?;
    budget.pay(raw.len().checked_mul(4).ok_or(Refusal::Resource)?)?;
    let parsed: Approval = serde_json::from_slice(&raw).map_err(|_| Refusal::Malformed)?;
    validate_approval(&parsed, &request, c, &installed.context_pin)?;
    same_metadata(&approval_before, &io(approval.metadata())?)?;
    let current = linux::calling_thread_proc()?;
    require_command(&current, b"ash-checked-owner-root-v2\0", &mut budget)?;
    let image_pin = request.final_image_pin().ok_or(Refusal::Incomplete)?;
    let limits = PreparationLimits { image_bytes: c.image_bytes, work: c.image_work, program_headers: c.program_headers };
    let mut image_work = Budget::new(c.image_work);
    let running = SealedData::observe_existing(linux::proc_magic(&current, c"exe", false)?, image_pin, limits, &mut image_work)?;
    // Separate post-build protected record: including the launcher digest in
    // the baked config would create launcher->config->launcher self-reference.
    let mut descriptor = linux::open_child(&installed.store, c"checked-launcher-v2.json", false)?;
    let descriptor_before = protected_metadata(&descriptor, false)?;
    let descriptor_bytes = bounded_read(&mut descriptor, BOOT_BYTES, &mut budget)?;
    budget.pay(descriptor_bytes.len().checked_mul(4).ok_or(Refusal::Resource)?)?;
    let descriptor_data: LauncherDescriptor = serde_json::from_slice(&descriptor_bytes).map_err(|_| Refusal::Malformed)?;
    if descriptor_data.version != 2 || descriptor_data.context_sha256 != hex(&installed.context_pin)
        || descriptor_data.target != "x86_64-unknown-linux-gnu"
        || descriptor_data.image.bytes == 0 || descriptor_data.image.bytes > c.image_bytes as u64
        || !valid_hash(&descriptor_data.image.sha256) {
        return Err(Refusal::Association);
    }
    let launcher = &descriptor_data.image;
    if parsed.launcher.as_ref().is_none_or(|p| p.bytes != launcher.bytes || p.sha256 != launcher.sha256) {
        return Err(Refusal::Association);
    }
    budget.pay(64)?;
    let mut digest = [0; 32];
    for (pair, out) in launcher.sha256.as_bytes().chunks_exact(2).zip(&mut digest) {
        let digit = |b: u8| if b.is_ascii_digit() { b - b'0' } else { b - b'a' + 10 };
        *out = digit(pair[0]) * 16 + digit(pair[1]);
    }
    let launcher = SealedData::observe_existing(linux::proc_magic(parent.parent(), c"exe", false)?,
        ArtifactPin { bytes: launcher.bytes, sha256: digest }, limits, &mut image_work)?;
    // Reopen only the fixed kernel exe links, matching the already inspected
    // immutable objects. No proc textual target or pathname is accepted.
    running.same_object(&linux::proc_magic(&current, c"exe", false)?)?;
    launcher.same_object(&linux::proc_magic(parent.parent(), c"exe", false)?)?;
    check_context(c, &mut budget)?;
    check_proc_context(c, parent.parent(), &mut budget)?;
    parent.recheck(&mut budget)?;
    same_metadata(&installed.config_metadata, &io(installed.config_file.metadata())?)?;
    same_metadata(&descriptor_before, &io(descriptor.metadata())?)?;
    linux::close_role(4)?;
    linux::close_role(3)?;
    // All config/store/approval/proc/pidfd/executable handles close on return.
    // Only immutable DATA and the owned nonblocking report writer survive.
    Ok(VerifiedRunning { request: bytes, request_pin: request.request_pin(), image_pin,
        embedded: request.embedded_pins().map(|p| (p.bytes, p.sha256)), report: crate::outcome::ReportWriter::new(parent.into_writer()) })
}

fn read_sealed_request(source: &mut File, cap: usize, work: &mut Budget) -> Result<Vec<u8>, Refusal> {
    let before = io(source.metadata())?;
    if !before.is_file() || before.len() > cap as u64 || linux::seals(source)? != 15 {
        return Err(Refusal::Association);
    }
    // Fund owned request storage before allocation; bounded_read separately
    // charges actual bounded read requests. Never accept only an inherited
    // open-file-description suffix as the sealed request object's identity.
    work.pay(usize::try_from(before.len()).map_err(|_| Refusal::Resource)?)?;
    io(source.seek(SeekFrom::Start(0)))?;
    let bytes = bounded_read(source, cap, work)?;
    if bytes.len() as u64 != before.len() { return Err(Refusal::Association); }
    same_metadata(&before, &io(source.metadata())?)?;
    if linux::seals(source)? != 15 { return Err(Refusal::Association); }
    Ok(bytes)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LauncherDescriptor { version: u32, target: String, context_sha256: String, image: Pin }
fn validate_approval(
    a: &Approval,
    r: &ApplicabilityRequest,
    c: &Config,
    context: &[u8; 32],
) -> Result<(), Refusal> {
    if a.version != c.version
        || (c.version == 1 && a.launcher.is_some())
        || (c.version == 2 && a.launcher.as_ref().is_none_or(|p| p.bytes == 0 || !valid_hash(&p.sha256)))
        || a.context_version != c.context_version
        || a.premise_version != c.premise_version
        || a.launch_version != c.launch_version
    {
        return Err(Refusal::Malformed);
    }
    if a.target != "x86_64-unknown-linux-gnu"
        || a.mode != "checked-inprocess-static"
        || a.role != if c.version == 1 { "checked-preparation" } else { "checked-running" }
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
#[derive(Clone, Copy)]
enum Ingress { Preparation, Root, LauncherParent, LauncherChild }
fn bootstrap(budget: &mut Budget, ingress: Ingress) -> Result<InstalledContext, Refusal> {
    let association = crate::bootstrap_association::INSTALLED.as_ref().ok_or(Refusal::MissingDeployment)?;
    let path = association.path;
    let expected = association.sha256;
    if !valid_hash(expected) {
        return Err(Refusal::MissingDeployment);
    }
    // Bootstrap bounds and environment/descriptor policy precede config decode.
    if std::env::vars_os().next().is_some() {
        return Err(Refusal::Context);
    }
    budget.pay(256 * 8192 + 8192)?;
    linux::standard_fds()?;
    match ingress {
        Ingress::Preparation => linux::inherited_fds()?,
        Ingress::Root => linux::inherited_fds_for(&[0, 1, 2, 3, 4])?,
        Ingress::LauncherParent => { linux::inherited_fds_for(&[0, 1, 2, 4, 5])?;
            if !linux::role_absent(3)? { return Err(Refusal::Context); } },
        Ingress::LauncherChild => linux::inherited_fds_for(&[0, 1, 2, 3, 4, 5])?,
    }
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
    if !matches!(ingress, Ingress::Preparation) != (config.version == 2) { return Err(Refusal::Context); }
    check_context(&config, budget)?;
    let file = linux::high(file)?;
    let store = linux::high(walk(Path::new(&config.store), true, budget)?)?;
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
    let version = match (c.version, c.context_version, c.premise_version, c.launch_version) {
        (1, 1, 1, 1) => 1,
        (2, 2, 1, 2) => 2,
        _ => return Err(Refusal::Malformed),
    };
    if (version == 1 && c.stdio != "null-read-null-write-v1")
        || (version == 2 && c.stdio != "null-report-request-v2") {
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
    check_proc_context(c, &proc, budget)
}
fn check_proc_context(c: &Config, proc: &File, budget: &mut Budget) -> Result<(), Refusal> {
    let namespace = linux::proc_child(proc, c"ns", true)?;
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
        let mut file = linux::proc_child(proc, name, false)?;
        let b = bounded_read(&mut file, BOOT_BYTES, budget)?;
        budget.pay(b.len())?;
        if hex(&Sha256::digest(&b)) != *expected {
            return Err(Refusal::Context);
        }
    }
    let mut status = linux::proc_child(proc, c"status", false)?;
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
    fn sealed_request_reads_whole_object_not_an_inherited_suffix() {
        use std::io::Write;
        let raw = b"unbound prefix:{\"version\":2}";
        let mut source = linux::memfd().unwrap();
        source.write_all(raw).unwrap();
        linux::seal(&source).unwrap();
        source.seek(SeekFrom::Start(15)).unwrap();
        let mut meter = Budget::new(4096);
        assert_eq!(read_sealed_request(&mut source, 128, &mut meter).unwrap(), raw);
        let cost = 4096 - meter.remaining;
        for _ in 0..2 {
            let mut exact = Budget::new(cost);
            assert_eq!(read_sealed_request(&mut source, 128, &mut exact).unwrap(), raw);
            assert_eq!(exact.remaining, 0);
        }
        assert_eq!(read_sealed_request(&mut source, 128, &mut Budget::new(cost - 1)), Err(Refusal::Resource));
        assert_eq!(read_sealed_request(&mut source, raw.len() - 1, &mut Budget::new(4096)), Err(Refusal::Association));
    }
    #[test]
    fn absent_fixed_deployment_and_same_uid_store_refuse_without_authority() {
        if crate::bootstrap_association::INSTALLED.is_none() {
            assert_eq!(
                prepare(b"untrusted", Path::new("/never-opened")).unwrap_err(),
                Refusal::MissingDeployment
            );
            assert!(matches!(verify_running(), Err(Refusal::MissingDeployment)));
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
        let mut c:Config=serde_json::from_value(serde_json::json!({"version":1,"uid":1234,"gid":1234,"groups":[1234],"user_namespace":{"device":1,"inode":2},"mount_namespace":{"device":1,"inode":3},"uid_map_sha256":"00".repeat(32),"mountinfo_sha256":"00".repeat(32),"store":"/fixed/store","store_identity":{"device":1,"inode":4},"stdio":"null-read-null-write-v1","context_version":1,"premise_version":1,"launch_version":1,"request_bytes":4096,"request_work":4096,"image_bytes":4096,"image_work":16384,"program_headers":4})).unwrap();
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
        c.version = 2;
        c.context_version = 2;
        c.launch_version = 2;
        c.stdio = "null-report-request-v2".into();
        validate_config(&c).unwrap();
        c.stdio = "null-read-null-write-v1".into();
        assert_eq!(validate_config(&c), Err(Refusal::Context));
        c.stdio = "null-report-request-v2".into();
        c.launch_version = 1;
        assert_eq!(validate_config(&c), Err(Refusal::Malformed));
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
            launcher: None,
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
        if crate::bootstrap_association::INSTALLED.is_none() {
            assert_eq!(
                prepare(&bytes, &image_path).unwrap_err(),
                Refusal::MissingDeployment
            );
        }
    }
}

/// Bounded output from one freshly verified child. Frames are observations, not
/// provider authority. Inspect the result/Trace/closing channels independently.
pub struct LaunchOutcome {
    bytes: Vec<u8>,
    success: bool,
    complete: bool,
    reaped: bool,
    exit_code: Option<i32>,
    signal: Option<i32>,
    eof: bool,
    loss: u8,
    observed_bytes: usize,
}
impl LaunchOutcome {
    /// Complete raw frames retained even when EOF, framing or the child fails.
    pub fn frames(&self) -> &[u8] { &self.bytes }
    /// Actual child exit status; alone this proves no source/native outcome.
    pub fn child_succeeded(&self) -> bool { self.success }
    /// Sequence, exact consumed length, Terminal and actual EOF were observed.
    pub fn stream_complete(&self) -> bool { self.complete }
}

/// Fixed one-shot launcher entry. Ingress roles4/5 are sealed request DATA and
/// candidate image DATA, not caller-created applicability. Phase comes from the
/// actual executable seals and the actual pipe-role census, never argv/env.
pub fn launch_fixed() -> Result<LaunchOutcome, Refusal> {
    if crate::bootstrap_association::INSTALLED.is_none() { return Err(Refusal::MissingDeployment); }
    let child = !linux::role_absent(3)?;
    let mut budget = Budget::new(BOOT_WORK);
    let installed = bootstrap(&mut budget, if child { Ingress::LauncherChild } else { Ingress::LauncherParent })?;
    let c = &installed.config;
    let current = linux::high(linux::calling_thread_proc()?)?;
    let mut executable = linux::high(linux::proc_magic(&current, c"exe", false)?)?;
    let limits = PreparationLimits { image_bytes: c.image_bytes, work: c.image_work, program_headers: c.program_headers };
    let mut image_work = Budget::new(c.image_work);
    let bundle = launch_bundle(&installed, &mut budget)?;
    let launcher_pin = bundle.launcher;
    let state = linux::seals_or_regular(&executable)?;
    let sink = launcher_command(&current, state == Some(15), child, &mut budget)?;
    match state {
        None if !child => {
            // Normal installed-file invocation becomes the verified sealed
            // parent by replacing THIS process with the same opened bytes.
            protected_metadata(&executable, false)?;
            let sealed = SealedData::copy_metered(&mut executable, launcher_pin, limits, &mut image_work)?;
            check_context(c, &mut budget)?;
            same_metadata(&installed.config_metadata, &io(installed.config_file.metadata())?)?;
            drop(current); drop(executable); drop(installed);
            return match linux::exec_fixed(sealed.file(), false, sink.as_deref())? {};
        }
        Some(15) => {}
        _ => return Err(Refusal::Association),
    }
    let executable = SealedData::observe_existing(executable, launcher_pin, limits, &mut image_work)?;
    let (flags, descriptor) = linux::role_flags(5)?;
    if flags & !0x8000 != 0 || descriptor != 0 { return Err(Refusal::Context); }
    let image = {
        let mut candidate = linux::duplicate_role(5)?;
        if child { SealedData::observe_existing(candidate, bundle.image, limits, &mut image_work)? }
        else { SealedData::copy_metered(&mut candidate, bundle.image, limits, &mut image_work)? }
    }.high()?;
    if child {
        let parent = crate::running::ParentPipe::inspect(&mut budget)?;
        check_proc_context(c, parent.parent(), &mut budget)?;
        let parent_image = SealedData::observe_existing(linux::proc_magic(parent.parent(), c"exe", false)?,
            launcher_pin, limits, &mut image_work)?;
        parent_image.same_object(&linux::proc_magic(parent.parent(), c"exe", false)?)?;
        parent.recheck(&mut budget)?;
        check_context(c, &mut budget)?;
        executable.same_object(&linux::proc_magic(&current, c"exe", false)?)?;
        same_metadata(&installed.config_metadata, &io(installed.config_file.metadata())?)?;
        // FD5 must not survive into the root census; all managed handles are
        // CLOEXEC. Root independently checks role3/4 and its actual sealed exe.
        linux::close_role(5)?;
        drop(parent); drop(parent_image); drop(current); drop(executable); drop(installed);
        return match linux::exec_fixed(image.file(), true, None)? {};
    }
    // Reserve bounded output storage before starting any child. This separate
    // fixed wire-profile capacity is not source work or a request-meter reset.
    let mut output_work = Budget::new(crate::outcome::STREAM_BYTES);
    output_work.pay(crate::outcome::STREAM_BYTES)?;
    let mut output = Vec::new();
    output.try_reserve_exact(crate::outcome::STREAM_BYTES).map_err(|_|Refusal::Resource)?;
    let request = linux::duplicate_role(4)?;
    let application = linux::readonly(image.file())?;
    let (reader, writer) = linux::report_pipe()?;
    let reader = linux::occupy_reader(&reader)?;
    check_context(c, &mut budget)?;
    executable.same_object(&linux::proc_magic(&current, c"exe", false)?)?;
    same_metadata(&installed.config_metadata, &io(installed.config_file.metadata())?)?;
    let pins = [bundle.request, bundle.image, bundle.launcher];
    let mut process = linux::spawn_launcher(executable.file(), &writer, &request, &application)?;
    // Never retain a writer in the parent: EOF means all child writers closed.
    drop(writer); drop(request); drop(application); drop(image); drop(current); drop(executable); drop(installed);
    let observation = collect_child(&reader, &mut process, &mut output);
    // Reader's actual FD3 remains unchanged until process.wait has reaped child.
    drop(reader);
    let outcome = LaunchOutcome { bytes: output, success: observation.success, complete: observation.complete,
        reaped: observation.reaped, exit_code: observation.exit_code, signal: observation.signal,
        eof: observation.eof, loss: observation.loss, observed_bytes: observation.observed_bytes };
    if let Some(path) = sink { publish_observation(&path, &pins, &outcome)?; }
    Ok(outcome)
}

struct LaunchBundle { request: ArtifactPin, image: ArtifactPin, launcher: ArtifactPin }
fn launch_bundle(installed: &InstalledContext, budget: &mut Budget) -> Result<LaunchBundle, Refusal> {
    let c = &installed.config;
    let (flags, descriptor) = linux::role_flags(4)?;
    if flags & !0x8000 != 0 || descriptor != 0 { return Err(Refusal::Context); }
    let mut request_file = linux::duplicate_role(4)?;
    let mut request_work = Budget::new(c.request_work);
    let bytes = read_sealed_request(&mut request_file, c.request_bytes, &mut request_work)?;
    let request = ApplicabilityRequest::decode(&bytes, RequestLimits { bytes: c.request_bytes, work: request_work.remaining })
        .map_err(|error| match error { ash::build::ReceiptFailure::Resource => Refusal::Resource, _ => Refusal::Malformed })?;
    request.check_complete().map_err(|_|Refusal::Incomplete)?;
    if request.context_pin() != Some(ArtifactPin { bytes: installed.config_metadata.len(), sha256: installed.context_pin }) {
        return Err(Refusal::Association);
    }
    budget.pay(65)?;
    let name = CString::new(hex(&request.request_pin().sha256)).map_err(|_|Refusal::Malformed)?;
    let mut approval = linux::open_child(&installed.store, &name, false)?;
    let before = protected_metadata(&approval, false)?;
    let raw = bounded_read(&mut approval, BOOT_BYTES, budget)?;
    budget.pay(raw.len().checked_mul(4).ok_or(Refusal::Resource)?)?;
    let approval_data: Approval = serde_json::from_slice(&raw).map_err(|_|Refusal::Malformed)?;
    validate_approval(&approval_data, &request, c, &installed.context_pin)?;
    same_metadata(&before, &io(approval.metadata())?)?;
    let mut descriptor = linux::open_child(&installed.store, c"checked-launcher-v2.json", false)?;
    let before = protected_metadata(&descriptor, false)?;
    let raw = bounded_read(&mut descriptor, BOOT_BYTES, budget)?;
    budget.pay(raw.len().checked_mul(4).ok_or(Refusal::Resource)?)?;
    let data: LauncherDescriptor = serde_json::from_slice(&raw).map_err(|_|Refusal::Malformed)?;
    if data.version != 2 || data.target != "x86_64-unknown-linux-gnu" || data.context_sha256 != hex(&installed.context_pin)
        || data.image.bytes == 0 || data.image.bytes > c.image_bytes as u64 || !valid_hash(&data.image.sha256)
        || approval_data.launcher.as_ref().is_none_or(|pin| pin.bytes != data.image.bytes || pin.sha256 != data.image.sha256) {
        return Err(Refusal::Association);
    }
    same_metadata(&before, &io(descriptor.metadata())?)?;
    budget.pay(64)?;
    let mut digest = [0;32];
    for (pair, byte) in data.image.sha256.as_bytes().chunks_exact(2).zip(&mut digest) {
        let digit = |b:u8| if b.is_ascii_digit() { b-b'0' } else { b-b'a'+10 };
        *byte = digit(pair[0])*16 + digit(pair[1]);
    }
    Ok(LaunchBundle { request: request.request_pin(), image: request.final_image_pin().ok_or(Refusal::Incomplete)?,
        launcher: ArtifactPin { bytes:data.image.bytes, sha256:digest } })
}
fn require_command(proc: &File, expected: &[u8], budget: &mut Budget) -> Result<(), Refusal> {
    let mut command = linux::proc_child(proc, c"cmdline", false)?;
    let bytes = bounded_read(&mut command, 256, budget)?;
    if bytes != expected { return Err(Refusal::Context); }
    Ok(())
}
fn launcher_command(proc: &File, sealed: bool, child: bool, budget: &mut Budget) -> Result<Option<CString>, Refusal> {
    let mut file = linux::proc_child(proc, c"cmdline", false)?;
    let bytes = bounded_read(&mut file, 8194, budget)?;
    let mut args = bytes.split(|byte| *byte == 0);
    let first = args.next().ok_or(Refusal::Context)?;
    if first.is_empty() || first.len() > 4096 || (sealed && first != b"ash-checked-launcher-v2") { return Err(Refusal::Context); }
    let next = args.next().ok_or(Refusal::Context)?;
    if next.is_empty() && args.next().is_none() { return Ok(None); }
    if child || next.is_empty() || next.len() > 4096 || args.next() != Some(b"".as_slice()) || args.next().is_some() {
        return Err(Refusal::Context);
    }
    budget.pay(next.len().checked_add(1).ok_or(Refusal::Resource)?)?;
    Ok(Some(CString::new(next).map_err(|_|Refusal::Malformed)?))
}
fn publish_observation(path: &std::ffi::CStr, pins: &[ArtifactPin;3], outcome: &LaunchOutcome) -> Result<(), Refusal> {
    use std::{io::Write, os::unix::{ffi::OsStrExt, fs::OpenOptionsExt}};
    if !outcome.reaped || outcome.bytes.len() > crate::outcome::STREAM_BYTES { return Err(Refusal::Input); }
    // Fixed256-byte envelope, no additional heap allocation. All variable bytes
    // were reserved before the child; this write happens only after actual reap.
    let mut header = [0u8;256];
    header[..8].copy_from_slice(b"ASHOBS02");
    header[8..16].copy_from_slice(&(crate::outcome::STREAM_BYTES as u64).to_le_bytes());
    header[16..24].copy_from_slice(&(outcome.bytes.len() as u64).to_le_bytes());
    header[24..32].copy_from_slice(&(outcome.observed_bytes as u64).to_le_bytes());
    header[32] = u8::from(outcome.success); header[33] = u8::from(outcome.complete);
    header[34] = u8::from(outcome.eof); header[35] = outcome.loss;
    header[36] = u8::from(outcome.exit_code.is_some()); header[37..41].copy_from_slice(&outcome.exit_code.unwrap_or(0).to_le_bytes());
    header[41] = u8::from(outcome.signal.is_some()); header[42..46].copy_from_slice(&outcome.signal.unwrap_or(0).to_le_bytes());
    for (slot, pin) in header[48..168].chunks_exact_mut(40).zip(pins) {
        slot[..8].copy_from_slice(&pin.bytes.to_le_bytes()); slot[8..].copy_from_slice(&pin.sha256);
    }
    header[168..172].copy_from_slice(&4096u32.to_le_bytes());
    header[172..176].copy_from_slice(&1024u32.to_le_bytes());
    // A DATA path is never an approval/store selector. Exclusive final-component
    // nofollow creation prevents clobber/retry; a failed write never reruns work.
    let mut file = io(std::fs::OpenOptions::new().write(true).create_new(true).mode(0o600)
        .custom_flags(0x20000 | 0x80000).open(std::ffi::OsStr::from_bytes(path.to_bytes())))?;
    let mut calls = 0usize;
    for mut bytes in [header.as_slice(), outcome.bytes.as_slice()] {
        while !bytes.is_empty() {
            calls += 1;
            if calls > crate::outcome::STREAM_BYTES + header.len() { return Err(Refusal::Resource); }
            let n = io(file.write(bytes))?;
            if n == 0 { return Err(Refusal::Input); }
            bytes = &bytes[n..];
        }
    }
    Ok(())
}
struct ChildObservation { success: bool, complete: bool, reaped: bool, exit_code: Option<i32>, signal: Option<i32>,
    eof: bool, loss: u8, observed_bytes: usize }
fn validate_stream(bytes: &[u8]) -> (usize, bool) {
    let mut parser = crate::outcome::FrameReader::new();
    let mut consumed = 0;
    while consumed < bytes.len() {
        match parser.next(&bytes[consumed..]) {
            Ok((_,_,n)) => consumed += n,
            Err(_) => return (consumed, false),
        }
    }
    (consumed, parser.finish().is_ok())
}
fn collect_child(reader: &File, process: &mut std::process::Child, bytes: &mut Vec<u8>) -> ChildObservation {
    use std::{io::Read, os::unix::process::ExitStatusExt, time::{Duration, Instant}};
    let deadline = Instant::now() + Duration::from_secs(60);
    let mut source = reader;
    let mut scratch = [0;4096];
    let mut eof = false;
    let mut status = None;
    let mut loss = 0;
    while Instant::now() < deadline {
        match source.read(&mut scratch) {
            Ok(0) => eof = true,
            Ok(n) => {
                if n > crate::outcome::STREAM_BYTES.saturating_sub(bytes.len()) { loss = 1; break; }
                bytes.extend_from_slice(&scratch[..n]);
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {},
            Err(_) => { loss = 2; break; }
        }
        match process.try_wait() {
            Ok(Some(result)) => status = Some(result), Ok(None) => {}, Err(_) => { loss = 3; break; }
        }
        if eof && status.is_some() { break; }
        std::thread::sleep(Duration::from_millis(1));
    }
    if status.is_none() {
        if loss == 0 { loss = 4; }
        if process.kill().is_err() { loss = 5; }
    }
    let waited = process.wait();
    let reaped = waited.is_ok();
    if !reaped { loss = 6; }
    let exit_code = waited.as_ref().ok().and_then(|status| status.code());
    let signal = waited.as_ref().ok().and_then(|status| status.signal());
    let success = waited.is_ok_and(|status| status.success());
    let (consumed, framed) = validate_stream(bytes);
    if !framed && loss == 0 { loss = 7; }
    if !eof && loss == 0 { loss = 8; }
    let complete = loss == 0 && eof && reaped && consumed == bytes.len() && framed;
    let observed_bytes = bytes.len();
    // Only complete frames survive a torn/malformed suffix. No report is
    // reconstructed from process status, and a Terminal without EOF fails.
    bytes.truncate(consumed);
    ChildObservation { success, complete, reaped, exit_code, signal, eof, loss, observed_bytes }
}

#[cfg(test)]
mod launcher_tests {
    use super::*;
    fn frame(seq: u64, kind: u32, bytes: &[u8]) -> Vec<u8> {
        let mut raw = b"ASHOUT02".to_vec(); raw.extend_from_slice(&seq.to_le_bytes());
        raw.extend_from_slice(&kind.to_le_bytes()); raw.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
        raw.extend_from_slice(bytes); raw
    }
    #[test]
    fn parent_stream_requires_terminal_exact_length_and_retains_complete_prefix() {
        let first = frame(0, 3, b"facts"); let mut raw = first.clone();
        assert_eq!(validate_stream(&raw), (raw.len(),false));
        let terminal = frame(1,5,b""); raw.extend_from_slice(&terminal);
        assert_eq!(validate_stream(&raw), (raw.len(),true));
        for cut in first.len()..raw.len() { assert_eq!(validate_stream(&raw[..cut]), (first.len(),false)); }
        raw.push(0); assert_eq!(validate_stream(&raw), (raw.len()-1,false));
        let mut wrong = first.clone(); wrong.extend_from_slice(&frame(3,5,b""));
        assert_eq!(validate_stream(&wrong), (first.len(),false));
        for _ in 0..2 { assert_eq!(validate_stream(&first), (first.len(),false)); }
    }
    #[test]
    fn post_reap_observation_sink_is_exclusive_bounded_data() {
        use std::{os::unix::{ffi::OsStrExt, fs::PermissionsExt}, io::Read};
        let dir = crate::test_directory("post-reap-observation");
        let path = dir.join("result"); let cpath = CString::new(path.as_os_str().as_bytes()).unwrap();
        let pins = [ArtifactPin { bytes: 7, sha256: [9;32] };3];
        let mut outcome = LaunchOutcome { bytes: frame(0,5,b""), success: false, complete: true,
            reaped: false, exit_code: Some(1), signal: None, eof: true, loss: 0, observed_bytes: 24 };
        assert_eq!(publish_observation(&cpath, &pins, &outcome), Err(Refusal::Input));
        assert!(!path.exists()); outcome.reaped = true;
        publish_observation(&cpath, &pins, &outcome).unwrap();
        let before = std::fs::read(&path).unwrap();
        assert_eq!(&before[..8], b"ASHOBS02"); assert_eq!(before.len(),256+24);
        assert_eq!(&before[48..56], &7u64.to_le_bytes()); assert_eq!(&before[56..88], &[9;32]);
        assert_eq!(std::fs::metadata(&path).unwrap().permissions().mode() & 0o777,0o600);
        assert_eq!(publish_observation(&cpath, &pins, &outcome), Err(Refusal::Input));
        assert_eq!(std::fs::read(&path).unwrap(),before);
        let link = dir.join("link"); std::os::unix::fs::symlink(&path,&link).unwrap();
        let clink = CString::new(link.as_os_str().as_bytes()).unwrap();
        assert_eq!(publish_observation(&clink, &pins, &outcome), Err(Refusal::Input));
        let mut file=File::open(&path).unwrap(); let mut first=[0;8];file.read_exact(&mut first).unwrap();assert_eq!(&first,b"ASHOBS02");
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn unconfigured_launcher_refuses_without_consulting_inherited_roles() {
        assert!(crate::bootstrap_association::INSTALLED.is_none());
        assert!(matches!(launch_fixed(), Err(Refusal::MissingDeployment)));
    }
}
