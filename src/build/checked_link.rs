//! Actual root-link observations, not approval or complete runtime closure.
use super::checked_receipt::{ArtifactPin, ProducerReceipt, ReceiptFailure, ReceiptField};
use crate::types::TypeWorkBudget;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeSet,
    fs,
    io::Read,
    path::{Path, PathBuf},
};

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Limits {
    pub file_bytes: usize,
    pub total_bytes: usize,
    pub map_bytes: usize,
    pub output_bytes: usize,
    pub record_bytes: usize,
    pub paths: usize,
    pub arguments: usize,
    pub seconds: u32,
    pub cargo_bytes: usize,
    pub cargo_seconds: u32,
    pub work: usize,
}
impl Limits {
    pub(super) fn validate(self) -> Result<(), ReceiptFailure> {
        if self.file_bytes == 0
            || self.file_bytes > 2usize.pow(31)
            || self.total_bytes == 0
            || self.total_bytes > 8 * 1024 * 1024 * 1024
            || self.map_bytes == 0
            || self.map_bytes > 256 * 1024 * 1024
            || self.output_bytes == 0
            || self.output_bytes > 4 * 1024 * 1024
            || self.record_bytes == 0
            || self.record_bytes > 4 * 1024 * 1024
            || self.paths == 0
            || self.paths > 4096
            || self.arguments == 0
            || self.arguments > 65536
            || self.seconds == 0
            || self.seconds > 120
            || self.cargo_bytes == 0
            || self.cargo_bytes > 16 * 1024 * 1024
            || self.cargo_seconds == 0
            || self.cargo_seconds > 1800
            || self.work == 0
            || self.work > 64 * 1024 * 1024 * 1024
        {
            return Err(ReceiptFailure::Resource);
        }
        Ok(())
    }
}
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Pin {
    bytes: u64,
    sha256: String,
}
impl Pin {
    fn artifact(&self) -> Result<ArtifactPin, ReceiptFailure> {
        if self.sha256.len() != 64
            || !self
                .sha256
                .bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return Err(ReceiptFailure::Malformed);
        }
        let mut sha256 = [0; 32];
        for (n, byte) in sha256.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&self.sha256[n * 2..n * 2 + 2], 16)
                .map_err(|_| ReceiptFailure::Malformed)?;
        }
        Ok(ArtifactPin {
            bytes: self.bytes,
            sha256,
        })
    }
}
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Input {
    path: String,
    device: u64,
    inode: u64,
    bytes: u64,
    sha256: String,
}
impl Input {
    fn pin(&self) -> Pin {
        Pin {
            bytes: self.bytes,
            sha256: self.sha256.clone(),
        }
    }
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Script {
    path: String,
    text: String,
    members: Vec<String>,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ResponseText {
    path: String,
    text: String,
}
#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SearchEntry {
    name: String,
    input: Input,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SearchPrefix {
    path: String,
    entries: Vec<SearchEntry>,
}
#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct BfdInvocation {
    version: u32,
    arguments: Vec<String>,
    output: String,
    tool: Input,
    proxy: Input,
    configuration: Input,
    process_group: u32,
    attempted_fd_exec: bool,
    work_used: usize,
}
#[derive(Serialize)]
struct ToolConfiguration<'a> {
    version: u32,
    tool: &'a Input,
    observer: &'a Input,
    proxy: &'a Input,
    work_limit: usize,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Observation {
    version: u32,
    arguments: Vec<String>,
    expanded: Vec<String>,
    searches: Vec<String>,
    command: Vec<String>,
    prefixes: Vec<SearchPrefix>,
    bfd: BfdInvocation,
    bfd_marker: Input,
    bfd_marker_text: String,
    cc_exit_code: i32,
    responses: Vec<Input>,
    response_texts: Vec<ResponseText>,
    inputs: Vec<Input>,
    loads: Vec<String>,
    resolved_loads: Vec<String>,
    scripts: Vec<Script>,
    tools: Vec<Input>,
    output: Input,
    map: Pin,
    stderr: Pin,
    work_used: usize,
    child_reaped: bool,
    owned_group_empty: bool,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RequiredInput {
    declared_path: String,
    observed: Input,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Record {
    declared_limits: Limits,
    tools_before: Vec<Input>,
    required: Vec<RequiredInput>,
    version: u32,
    observation: Observation,
    observer: Input,
    configuration: Input,
    proxy: Input,
    tool_configuration: Input,
    associations: Vec<ArtifactPinData>,
    configuration_before_binding: ArtifactPinData,
}
#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ArtifactPinData {
    bytes: u64,
    sha256: [u8; 32],
}
impl From<ArtifactPin> for ArtifactPinData {
    fn from(p: ArtifactPin) -> Self {
        Self {
            bytes: p.bytes,
            sha256: p.sha256,
        }
    }
}
impl From<&ArtifactPinData> for ArtifactPin {
    fn from(p: &ArtifactPinData) -> Self {
        Self {
            bytes: p.bytes,
            sha256: p.sha256,
        }
    }
}
fn pay(work: &mut TypeWorkBudget, n: usize) -> Result<(), ReceiptFailure> {
    work.charge(n).map_err(|()| ReceiptFailure::Resource)
}
fn read(path: &Path, cap: usize, work: &mut TypeWorkBudget) -> Result<Vec<u8>, ReceiptFailure> {
    let mut f = fs::File::open(path).map_err(|_| ReceiptFailure::Input)?;
    let n = usize::try_from(f.metadata().map_err(|_| ReceiptFailure::Input)?.len())
        .map_err(|_| ReceiptFailure::Resource)?;
    if n > cap {
        return Err(ReceiptFailure::Resource);
    }
    pay(work, n.checked_add(1).ok_or(ReceiptFailure::Resource)?)?;
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(n + 1)
        .map_err(|_| ReceiptFailure::Resource)?;
    f.by_ref()
        .take((n + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|_| ReceiptFailure::Input)?;
    if bytes.len() != n {
        return Err(ReceiptFailure::Association);
    }
    Ok(bytes)
}
#[cfg(unix)]
fn observe(path: &Path, cap: usize, work: &mut TypeWorkBudget) -> Result<Input, ReceiptFailure> {
    use std::os::unix::fs::MetadataExt;
    let path = fs::canonicalize(path).map_err(|_| ReceiptFailure::Input)?;
    let name = path.to_str().ok_or(ReceiptFailure::Input)?;
    if name.chars().any(char::is_whitespace) {
        return Err(ReceiptFailure::Input);
    }
    pay(work, name.len() + 1)?;
    let mut f = fs::File::open(&path).map_err(|_| ReceiptFailure::Input)?;
    let a = f.metadata().map_err(|_| ReceiptFailure::Input)?;
    if !a.is_file() || a.len() > cap as u64 {
        return Err(ReceiptFailure::Resource);
    }
    let mut h = Sha256::new();
    let mut buffer = [0; 65536];
    let mut n = 0usize;
    loop {
        let got = f.read(&mut buffer).map_err(|_| ReceiptFailure::Input)?;
        if got == 0 {
            break;
        }
        n = n.checked_add(got).ok_or(ReceiptFailure::Resource)?;
        if n > cap {
            return Err(ReceiptFailure::Resource);
        }
        pay(work, got)?;
        h.update(&buffer[..got]);
    }
    let z = f.metadata().map_err(|_| ReceiptFailure::Input)?;
    if (
        a.dev(),
        a.ino(),
        a.len(),
        a.mtime(),
        a.mtime_nsec(),
        a.ctime(),
        a.ctime_nsec(),
    ) != (
        z.dev(),
        z.ino(),
        z.len(),
        z.mtime(),
        z.mtime_nsec(),
        z.ctime(),
        z.ctime_nsec(),
    ) || n as u64 != a.len()
    {
        return Err(ReceiptFailure::Association);
    }
    Ok(Input {
        path: name.into(),
        device: a.dev(),
        inode: a.ino(),
        bytes: n as u64,
        sha256: format!("{:x}", h.finalize()),
    })
}
const ASSOCIATIONS: [ReceiptField; 5] = [
    ReceiptField::ProgramImage,
    ReceiptField::ExpectedFacts,
    ReceiptField::OriginalMappings,
    ReceiptField::DeclaredNativeInputs,
    ReceiptField::Policy,
];
fn associations(receipt: &ProducerReceipt) -> Result<Vec<ArtifactPinData>, ReceiptFailure> {
    ASSOCIATIONS
        .iter()
        .map(|&f| {
            receipt
                .pin(f)
                .map(Into::into)
                .ok_or(ReceiptFailure::Association)
        })
        .collect()
}

fn proxy_work(
    tool: &Input,
    observer: &Input,
    proxy: &Input,
    limits: Limits,
) -> Result<usize, ReceiptFailure> {
    usize::try_from(tool.bytes)
        .ok()
        .and_then(|n| n.checked_add(observer.bytes.try_into().ok()?))
        .and_then(|n| n.checked_add(proxy.bytes.try_into().ok()?))
        .and_then(|n| n.checked_add(limits.record_bytes.checked_mul(8)?))
        .and_then(|n| n.checked_add(4096))
        .filter(|n| *n <= limits.work)
        .ok_or(ReceiptFailure::Resource)
}
pub(super) struct Capture {
    directory: PathBuf,
    limits: Limits,
    work: TypeWorkBudget,
    observer: Input,
    configuration: Input,
    proxy: Input,
    tool_configuration: Input,
    observation: Option<Observation>,
    required: Vec<RequiredInput>,
    tools_before: Vec<Input>,
    cargo_calls: u32,
}
impl Capture {
    pub(super) fn prepare(
        project: &Path,
        limits: Limits,
        required: &[super::host::NativeLinkInput],
    ) -> Result<Self, ReceiptFailure> {
        limits.validate()?;
        let mut work = TypeWorkBudget::with_limit(limits.work);
        let directory = project.join("checked-link");
        fs::create_dir(&directory).map_err(|_| ReceiptFailure::Input)?;
        let script = include_bytes!("checked_link_observer.py");
        pay(&mut work, script.len())?;
        fs::write(directory.join("observer.py"), script).map_err(|_| ReceiptFailure::Input)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(
                directory.join("observer.py"),
                fs::Permissions::from_mode(0o700),
            )
            .map_err(|_| ReceiptFailure::Input)?;
        }
        let config = serde_json::to_vec(&limits).map_err(|_| ReceiptFailure::Resource)?;
        pay(&mut work, config.len())?;
        fs::write(directory.join("limits.json"), &config).map_err(|_| ReceiptFailure::Input)?;
        let observer = observe(
            &directory.join("observer.py"),
            limits.record_bytes,
            &mut work,
        )?;
        let configuration = observe(
            &directory.join("limits.json"),
            limits.record_bytes,
            &mut work,
        )?;
        let mut tools_before = Vec::new();
        tools_before
            .try_reserve_exact(3)
            .map_err(|_| ReceiptFailure::Resource)?;
        for tool in ["/usr/bin/cc", "/usr/bin/ld.bfd", "/usr/bin/python3"] {
            tools_before.push(observe(Path::new(tool), limits.file_bytes, &mut work)?);
        }
        let prefix = directory.join("selected-bfd");
        fs::create_dir(&prefix).map_err(|_| ReceiptFailure::Input)?;
        let code = include_bytes!("checked_bfd_proxy.py");
        pay(&mut work, code.len())?;
        fs::write(prefix.join("ld.bfd"), code).map_err(|_| ReceiptFailure::Input)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(prefix.join("ld.bfd"), fs::Permissions::from_mode(0o700))
                .map_err(|_| ReceiptFailure::Input)?;
        }
        let proxy = observe(&prefix.join("ld.bfd"), limits.record_bytes, &mut work)?;
        pay(&mut work, 4096)?;
        let tool_bytes = serde_json::to_vec(&ToolConfiguration {
            version: 1,
            tool: &tools_before[1],
            observer: &observer,
            proxy: &proxy,
            work_limit: proxy_work(&tools_before[1], &observer, &proxy, limits)?,
        })
        .map_err(|_| ReceiptFailure::Resource)?;
        if tool_bytes.len() > 4096 {
            return Err(ReceiptFailure::Resource);
        }
        fs::write(prefix.join("tool.json"), &tool_bytes).map_err(|_| ReceiptFailure::Input)?;
        let tool_configuration = observe(&prefix.join("tool.json"), 4096, &mut work)?;
        let mut required_inputs = Vec::new();
        if required.is_empty() || required.len() > limits.paths {
            return Err(ReceiptFailure::Association);
        }
        for input in required {
            if !matches!(input, super::host::NativeLinkInput::StaticArchive(_)) {
                return Err(ReceiptFailure::Association);
            }
            let declared_path = input
                .path()
                .to_str()
                .ok_or(ReceiptFailure::Input)?
                .to_owned();
            pay(&mut work, declared_path.len() + 1)?;
            required_inputs
                .try_reserve(1)
                .map_err(|_| ReceiptFailure::Resource)?;
            required_inputs.push(RequiredInput {
                declared_path,
                observed: observe(input.path(), limits.file_bytes, &mut work)?,
            });
        }
        Ok(Self {
            directory,
            limits,
            work,
            observer,
            configuration,
            proxy,
            tool_configuration,
            observation: None,
            required: required_inputs,
            tools_before,
            cargo_calls: 0,
        })
    }
    pub(super) fn run_cargo(
        &mut self,
        command: &mut std::process::Command,
        log: &Path,
    ) -> std::io::Result<std::process::ExitStatus> {
        if self.cargo_calls >= 2 {
            return Err(std::io::Error::other("checked Cargo phase capacity"));
        }
        let directory = self.directory.join(format!("cargo-{}", self.cargo_calls));
        std::fs::create_dir(&directory)?;
        self.cargo_calls += 1;
        super::checked_native_build::run_root_cargo(
            command,
            &directory,
            log,
            self.limits,
            &mut self.work,
        )
        .map_err(|e| std::io::Error::other(format!("checked Cargo observation refused: {e:?}")))
    }
    pub(super) fn linker(&self) -> PathBuf {
        self.directory.join("observer.py")
    }
    // Invoked on copied staging bytes BEFORE root/private Cargo cleanup. The
    // wrapper has already pinned every transient LOAD input before returning.
    pub(super) fn capture(&mut self, linked: &Path) -> Result<(), ReceiptFailure> {
        if self.observation.is_some() {
            return Err(ReceiptFailure::Association);
        }
        if observe(&self.linker(), self.limits.record_bytes, &mut self.work)? != self.observer
            || observe(
                &self.directory.join("limits.json"),
                self.limits.record_bytes,
                &mut self.work,
            )? != self.configuration
        {
            return Err(ReceiptFailure::Association);
        }
        let bytes = read(
            &self.directory.join("record.json"),
            self.limits.record_bytes,
            &mut self.work,
        )?;
        let obs: Observation =
            serde_json::from_slice(&bytes).map_err(|_| ReceiptFailure::Malformed)?;
        validate(&obs, self.limits, &mut self.work)?;
        let prefix = self.directory.join("selected-bfd");
        if observe(
            &prefix.join("ld.bfd"),
            self.limits.record_bytes,
            &mut self.work,
        )? != self.proxy
            || observe(&prefix.join("tool.json"), 4096, &mut self.work)? != self.tool_configuration
            || observe(
                &prefix.join("invocation.json"),
                self.limits.record_bytes,
                &mut self.work,
            )? != obs.bfd_marker
        {
            return Err(ReceiptFailure::Association);
        }
        let marker: BfdInvocation = serde_json::from_slice(&read(
            &prefix.join("invocation.json"),
            self.limits.record_bytes,
            &mut self.work,
        )?)
        .map_err(|_| ReceiptFailure::Malformed)?;
        if marker != obs.bfd {
            return Err(ReceiptFailure::Association);
        }

        let map = read(
            &self.directory.join("link.map"),
            self.limits.map_bytes,
            &mut self.work,
        )?;
        if super::checked_receipt::pin(&map, &mut self.work)? != obs.map.artifact()? {
            return Err(ReceiptFailure::Association);
        }
        let loads = map_loads(&map, self.limits, &mut self.work)?;
        if loads != obs.loads {
            return Err(ReceiptFailure::Association);
        }
        if observe(linked, self.limits.file_bytes, &mut self.work)?.pin() != obs.output.pin() {
            return Err(ReceiptFailure::Association);
        }
        for p in &obs.tools {
            if observe(Path::new(&p.path), self.limits.file_bytes, &mut self.work)? != *p {
                return Err(ReceiptFailure::Association);
            }
        }
        // Existing paths are revalidated. A vanished transient path is recorded
        // as an earlier wrapper observation, never claimed independently present.
        for p in &obs.inputs {
            if Path::new(&p.path).exists()
                && observe(Path::new(&p.path), self.limits.file_bytes, &mut self.work)? != *p
            {
                return Err(ReceiptFailure::Association);
            }
        }
        for required in &self.required {
            pay(
                &mut self.work,
                (required.observed.path.len() + 128)
                    .checked_mul(obs.inputs.len())
                    .ok_or(ReceiptFailure::Resource)?,
            )?;
            if !obs.inputs.iter().any(|p| p == &required.observed)
                || observe(
                    Path::new(&required.observed.path),
                    self.limits.file_bytes,
                    &mut self.work,
                )? != required.observed
            {
                return Err(ReceiptFailure::Association);
            }
        }
        self.observation = Some(obs);
        Ok(())
    }
    pub(super) fn finish(
        &mut self,
        receipt: &ProducerReceipt,
        linked: &Path,
    ) -> Result<Vec<u8>, ReceiptFailure> {
        let obs = self.observation.take().ok_or(ReceiptFailure::Association)?;
        if observe(linked, self.limits.file_bytes, &mut self.work)?.pin() != obs.output.pin() {
            return Err(ReceiptFailure::Association);
        }
        let record = Record {
            declared_limits: self.limits,
            tools_before: std::mem::take(&mut self.tools_before),
            required: std::mem::take(&mut self.required),
            version: 1,
            observation: obs,
            observer: self.observer.clone(),
            configuration: self.configuration.clone(),
            proxy: self.proxy.clone(),
            tool_configuration: self.tool_configuration.clone(),
            associations: associations(receipt)?,
            configuration_before_binding: receipt
                .pin(ReceiptField::BuildConfiguration)
                .ok_or(ReceiptFailure::Association)?
                .into(),
        };
        pay(&mut self.work, self.limits.record_bytes)?;
        let bytes = serde_json::to_vec(&record).map_err(|_| ReceiptFailure::Resource)?;
        if bytes.len() > self.limits.record_bytes {
            return Err(ReceiptFailure::Resource);
        }
        Ok(bytes)
    }
    pub(super) fn limits(&self) -> Limits {
        self.limits
    }
}
fn map_loads(
    bytes: &[u8],
    limits: Limits,
    work: &mut TypeWorkBudget,
) -> Result<Vec<String>, ReceiptFailure> {
    if bytes.len() > limits.map_bytes {
        return Err(ReceiptFailure::Resource);
    }
    pay(work, bytes.len())?;
    let text = std::str::from_utf8(bytes).map_err(|_| ReceiptFailure::Malformed)?;
    if !text.contains("Linker script and memory map\n")
        || !text
            .lines()
            .any(|s| s.starts_with("OUTPUT(") && s.contains("elf64-x86-64"))
    {
        return Err(ReceiptFailure::Malformed);
    }
    let mut loads = Vec::new();
    for line in text.lines() {
        if let Some(path) = line.strip_prefix("LOAD ") {
            if path.is_empty()
                || path.chars().any(char::is_whitespace)
                || !Path::new(path).is_absolute()
            {
                return Err(ReceiptFailure::Malformed);
            }
            if loads.len() == limits.paths {
                return Err(ReceiptFailure::Resource);
            }
            loads.try_reserve(1).map_err(|_| ReceiptFailure::Resource)?;
            loads.push(path.to_owned());
        }
    }
    if loads.is_empty() {
        return Err(ReceiptFailure::Malformed);
    }
    Ok(loads)
}
fn script_members(text: &str, work: &mut TypeWorkBudget) -> Result<Vec<String>, ReceiptFailure> {
    if text.len() > 16384 {
        return Err(ReceiptFailure::Resource);
    }
    pay(
        work,
        text.len().checked_mul(4).ok_or(ReceiptFailure::Resource)?,
    )?;
    if !text.is_ascii() {
        return Err(ReceiptFailure::Malformed);
    }
    let mut clean = String::new();
    clean
        .try_reserve(text.len())
        .map_err(|_| ReceiptFailure::Resource)?;
    let mut rest = text;
    while let Some(at) = rest.find("/*") {
        clean.push_str(&rest[..at]);
        rest = &rest[at + 2..];
        let end = rest.find("*/").ok_or(ReceiptFailure::Malformed)?;
        rest = &rest[end + 2..];
        clean.push(' ');
    }
    clean.push_str(rest);
    if clean.contains("*/") {
        return Err(ReceiptFailure::Malformed);
    }
    let expanded = clean.replace('(', " ( ").replace(')', " ) ");
    let words = expanded.split_whitespace().collect::<Vec<_>>();
    if words.len() < 8
        || words[..4] != ["OUTPUT_FORMAT", "(", "elf64-x86-64", ")"]
        || !matches!(words[4], "GROUP" | "INPUT")
        || words[5] != "("
        || words.last() != Some(&")")
    {
        return Err(ReceiptFailure::Malformed);
    }
    let mut members = Vec::new();
    for path in &words[6..words.len() - 1] {
        pay(
            work,
            (path.len() + 1)
                .checked_mul(members.len() + 1)
                .ok_or(ReceiptFailure::Resource)?,
        )?;
        if !Path::new(path).is_absolute()
            || !(path.ends_with(".a") || path.ends_with(".o"))
            || members.contains(&path.to_string())
        {
            return Err(ReceiptFailure::Malformed);
        }
        members.push(path.to_string());
    }
    Ok(members)
}

fn response_tokens(text: &str, work: &mut TypeWorkBudget) -> Result<Vec<String>, ReceiptFailure> {
    pay(
        work,
        text.len().checked_mul(4).ok_or(ReceiptFailure::Resource)?,
    )?;
    let mut chars = text.chars().peekable();
    let mut result = Vec::new();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
            continue;
        }
        let quoted = matches!(c, '\"' | '\'');
        let quote = if quoted {
            chars.next();
            Some(c)
        } else {
            None
        };
        let mut word = String::new();
        let mut closed = !quoted;
        while let Some(&c) = chars.peek() {
            if Some(c) == quote {
                chars.next();
                closed = true;
                break;
            }
            if !quoted && c.is_whitespace() {
                break;
            }
            if c == '\\' || (!quoted && matches!(c, '\"' | '\'')) {
                return Err(ReceiptFailure::Malformed);
            }
            word.push(c);
            chars.next();
        }
        if !closed
            || word.is_empty()
            || word.chars().any(char::is_whitespace)
            || (quoted && chars.peek().is_some_and(|c| !c.is_whitespace()))
        {
            return Err(ReceiptFailure::Malformed);
        }
        result.push(word);
    }
    Ok(result)
}
fn expanded_arguments(
    args: &[String],
    obs: &Observation,
    limits: Limits,
    visited: &mut Vec<String>,
    depth: usize,
    work: &mut TypeWorkBudget,
) -> Result<Vec<String>, ReceiptFailure> {
    if depth > 4 {
        return Err(ReceiptFailure::Resource);
    }
    let mut result = Vec::new();
    for arg in args {
        pay(work, arg.len() + 1)?;
        if let Some(path) = arg.strip_prefix('@') {
            pay(
                work,
                (path.len() + 1)
                    .checked_mul(
                        visited
                            .len()
                            .checked_add(obs.response_texts.len())
                            .and_then(|n| n.checked_add(obs.responses.len() + 1))
                            .ok_or(ReceiptFailure::Resource)?,
                    )
                    .ok_or(ReceiptFailure::Resource)?,
            )?;
            if !Path::new(path).is_absolute() || visited.iter().any(|p| p == path) {
                return Err(ReceiptFailure::Malformed);
            }
            visited.push(path.into());
            let data = obs
                .response_texts
                .iter()
                .find(|p| p.path == path)
                .ok_or(ReceiptFailure::Association)?;
            let input = obs
                .responses
                .iter()
                .find(|p| p.path == path)
                .ok_or(ReceiptFailure::Association)?;
            if super::checked_receipt::pin(data.text.as_bytes(), work)? != input.pin().artifact()? {
                return Err(ReceiptFailure::Association);
            }
            let tokens = response_tokens(&data.text, work)?;
            result.extend(expanded_arguments(
                &tokens,
                obs,
                limits,
                visited,
                depth + 1,
                work,
            )?);
        } else {
            result.push(arg.clone());
        }
        if result.len() > limits.arguments {
            return Err(ReceiptFailure::Resource);
        }
    }
    Ok(result)
}
fn require_bfd(args: &[String], work: &mut TypeWorkBudget) -> Result<(), ReceiptFailure> {
    let mut selected = None;
    for arg in args {
        pay(
            work,
            arg.len().checked_add(1).ok_or(ReceiptFailure::Resource)?,
        )?;
        if arg.starts_with("-fuse-ld") {
            if !matches!(arg.as_str(), "-fuse-ld=lld" | "-fuse-ld=bfd") {
                return Err(ReceiptFailure::Input);
            }
            selected = Some(arg.as_str());
        }
    }
    if selected != Some("-fuse-ld=bfd") {
        return Err(ReceiptFailure::Input);
    }
    Ok(())
}
fn validate_bfd(
    obs: &Observation,
    limits: Limits,
    work: &mut TypeWorkBudget,
) -> Result<(), ReceiptFailure> {
    let bfd = &obs.bfd;
    if obs.bfd_marker_text.len() > limits.record_bytes {
        return Err(ReceiptFailure::Resource);
    }
    let marker_pin = super::checked_receipt::pin(obs.bfd_marker_text.as_bytes(), work)?;
    pay(work, obs.bfd_marker_text.len())?;
    let parsed: BfdInvocation =
        serde_json::from_str(&obs.bfd_marker_text).map_err(|_| ReceiptFailure::Malformed)?;
    if marker_pin != obs.bfd_marker.pin().artifact()? || parsed != *bfd {
        return Err(ReceiptFailure::Association);
    }
    if bfd.version != 1
        || !bfd.attempted_fd_exec
        || bfd.process_group == 0
        || obs.cc_exit_code != 0
        || bfd.tool != obs.tools[1]
        || bfd.output != obs.output.path
        || bfd.arguments.is_empty()
        || bfd.arguments.len() > limits.arguments
        || obs.command.len()
            != obs
                .expanded
                .len()
                .checked_add(4)
                .ok_or(ReceiptFailure::Resource)?
    {
        return Err(ReceiptFailure::Association);
    }
    let prefix = Path::new(&bfd.proxy.path)
        .parent()
        .ok_or(ReceiptFailure::Association)?;
    pay(
        work,
        bfd.proxy
            .path
            .len()
            .checked_add(
                obs.command
                    .iter()
                    .map(String::len)
                    .try_fold(0usize, usize::checked_add)
                    .ok_or(ReceiptFailure::Resource)?,
            )
            .ok_or(ReceiptFailure::Resource)?,
    )?;
    let search = format!("-B{}", prefix.to_str().ok_or(ReceiptFailure::Malformed)?);
    let n = obs.expanded.len();
    if obs.command[0] != "/usr/bin/cc"
        || obs.command[1] != search
        || obs.command[2..2 + n] != obs.expanded
        || obs.command[2 + n] != "-v"
        || obs.command[3 + n] != "-Wl,--no-print-map-discarded,-Map=-"
    {
        return Err(ReceiptFailure::Association);
    }
    let mut outputs = 0;
    for (i, arg) in bfd.arguments.iter().enumerate() {
        pay(
            work,
            arg.len().checked_add(1).ok_or(ReceiptFailure::Resource)?,
        )?;
        if arg.starts_with('@') {
            return Err(ReceiptFailure::Input);
        }
        if arg == "-o" {
            if bfd.arguments.get(i + 1) != Some(&bfd.output) {
                return Err(ReceiptFailure::Association);
            }
            outputs += 1;
        }
    }
    if outputs != 1 {
        return Err(ReceiptFailure::Association);
    }
    let mut prefixes = Vec::new();
    for (i, arg) in obs.expanded.iter().enumerate() {
        pay(
            work,
            arg.len().checked_add(1).ok_or(ReceiptFailure::Resource)?,
        )?;
        if arg == "-B" {
            prefixes.push(
                obs.expanded
                    .get(i + 1)
                    .ok_or(ReceiptFailure::Malformed)?
                    .as_str(),
            );
        } else if let Some(p) = arg.strip_prefix("-B") {
            prefixes.push(p);
        }
    }
    if prefixes.len() > 1 || prefixes.len() != obs.prefixes.len() {
        return Err(ReceiptFailure::Association);
    }
    for (path, observed) in prefixes.iter().zip(&obs.prefixes) {
        pay(
            work,
            path.len()
                .checked_add(observed.path.len())
                .ok_or(ReceiptFailure::Resource)?,
        )?;
        if *path != observed.path
            || !Path::new(path).is_absolute()
            || !path.ends_with("/lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld")
            || Path::new(path).components().any(|c| {
                matches!(
                    c,
                    std::path::Component::ParentDir | std::path::Component::CurDir
                )
            })
            || observed.entries.len() != 4
        {
            return Err(ReceiptFailure::Association);
        }
        for (entry, name) in observed
            .entries
            .iter()
            .zip(["ld.lld", "ld64.lld", "lld-link", "wasm-ld"])
        {
            pay(
                work,
                entry
                    .name
                    .len()
                    .checked_add(entry.input.path.len())
                    .and_then(|n| n.checked_add(128))
                    .ok_or(ReceiptFailure::Resource)?,
            )?;
            if entry.name != name
                || !Path::new(&entry.input.path).is_absolute()
                || entry.input.bytes > limits.file_bytes as u64
            {
                return Err(ReceiptFailure::Association);
            }
            entry.input.pin().artifact()?;
        }
    }
    Ok(())
}
fn validate(
    obs: &Observation,
    limits: Limits,
    work: &mut TypeWorkBudget,
) -> Result<(), ReceiptFailure> {
    limits.validate()?;
    pay(work, 1)?;
    if obs.version != 1 {
        return Err(ReceiptFailure::Version);
    }
    if !obs.child_reaped
        || !obs.owned_group_empty
        || obs.inputs.is_empty()
        || obs.tools.len() != 3
        || obs.loads.is_empty()
    {
        return Err(ReceiptFailure::Malformed);
    }
    if obs
        .inputs
        .len()
        .checked_add(obs.responses.len())
        .ok_or(ReceiptFailure::Resource)?
        > limits.paths
        || obs.loads.len() > limits.paths
        || obs.arguments.len() > limits.arguments
        || obs.expanded.len() > limits.arguments
        || obs.work_used > limits.work
        || obs.map.bytes > limits.map_bytes as u64
        || obs.stderr.bytes > limits.output_bytes as u64
    {
        return Err(ReceiptFailure::Resource);
    }
    if obs.response_texts.len() != obs.responses.len() {
        return Err(ReceiptFailure::Association);
    }
    let mut visited = Vec::new();
    if expanded_arguments(&obs.arguments, obs, limits, &mut visited, 0, work)? != obs.expanded
        || visited.len() != obs.responses.len()
    {
        return Err(ReceiptFailure::Association);
    }
    require_bfd(&obs.expanded, work)?;
    validate_bfd(obs, limits, work)?;
    let comparisons = obs
        .inputs
        .len()
        .checked_add(obs.resolved_loads.len())
        .ok_or(ReceiptFailure::Resource)?;
    for path in obs
        .inputs
        .iter()
        .map(|p| &p.path)
        .chain(&obs.resolved_loads)
    {
        pay(
            work,
            path.len()
                .checked_add(1)
                .and_then(|n| n.checked_mul(comparisons))
                .ok_or(ReceiptFailure::Resource)?,
        )?;
    }
    if obs.loads.len() != obs.resolved_loads.len()
        || obs.resolved_loads.iter().collect::<BTreeSet<_>>()
            != obs.inputs.iter().map(|p| &p.path).collect::<BTreeSet<_>>()
    {
        return Err(ReceiptFailure::Association);
    }
    for argument in obs
        .arguments
        .iter()
        .chain(&obs.expanded)
        .chain(&obs.searches)
    {
        pay(
            work,
            argument
                .len()
                .checked_add(1)
                .ok_or(ReceiptFailure::Resource)?,
        )?;
    }
    if obs.scripts.len() > limits.paths {
        return Err(ReceiptFailure::Resource);
    }
    for script in &obs.scripts {
        if script_members(&script.text, work)? != script.members {
            return Err(ReceiptFailure::Association);
        }
        let source_pin = super::checked_receipt::pin(script.text.as_bytes(), work)?;
        let input = obs
            .inputs
            .iter()
            .find(|p| p.path == script.path)
            .ok_or(ReceiptFailure::Association)?;
        if input.pin().artifact()? != source_pin {
            return Err(ReceiptFailure::Association);
        }
        for member in &script.members {
            pay(
                work,
                member
                    .len()
                    .checked_mul(obs.inputs.len() + obs.scripts.len() + 1)
                    .ok_or(ReceiptFailure::Resource)?,
            )?;
            if !obs.inputs.iter().any(|p| &p.path == member)
                || obs.scripts.iter().any(|s| &s.path == member)
            {
                return Err(ReceiptFailure::Association);
            }
        }
    }
    let mut total = 0u64;
    let mut paths = BTreeSet::new();
    for p in obs.inputs.iter().chain(&obs.responses) {
        pay(work, p.path.len() + 1)?;
        if !Path::new(&p.path).is_absolute()
            || p.path.chars().any(char::is_whitespace)
            || !paths.insert(&p.path)
        {
            return Err(ReceiptFailure::Malformed);
        }
        p.pin().artifact()?;
        if p.bytes > limits.file_bytes as u64 {
            return Err(ReceiptFailure::Resource);
        }
        total = total.checked_add(p.bytes).ok_or(ReceiptFailure::Resource)?;
    }
    if total > limits.total_bytes as u64 {
        return Err(ReceiptFailure::Resource);
    }
    Ok(())
}
fn required_association(
    record: &Record,
    receipt: &ProducerReceipt,
    work: &mut TypeWorkBudget,
) -> Result<(), ReceiptFailure> {
    if record.required.is_empty() {
        return Err(ReceiptFailure::Association);
    }
    let mut hash = Sha256::new();
    let mut bytes = 0u64;
    for required in &record.required {
        pay(
            work,
            required
                .declared_path
                .len()
                .checked_add(49)
                .ok_or(ReceiptFailure::Resource)?,
        )?;
        pay(
            work,
            required
                .observed
                .path
                .len()
                .checked_add(128)
                .and_then(|n| n.checked_mul(record.observation.inputs.len() + 1))
                .ok_or(ReceiptFailure::Resource)?,
        )?;
        if !record
            .observation
            .inputs
            .iter()
            .any(|p| p == &required.observed)
        {
            return Err(ReceiptFailure::Association);
        }
        bytes = bytes
            .checked_add(required.declared_path.len() as u64 + 49)
            .ok_or(ReceiptFailure::Resource)?;
        hash.update((required.declared_path.len() as u64).to_le_bytes());
        hash.update(required.declared_path.as_bytes());
        hash.update([0]);
        hash.update(required.observed.bytes.to_le_bytes());
        hash.update(required.observed.pin().artifact()?.sha256);
    }
    if receipt.pin(ReceiptField::DeclaredNativeInputs)
        != Some(ArtifactPin {
            bytes,
            sha256: hash.finalize().into(),
        })
    {
        return Err(ReceiptFailure::Association);
    }
    Ok(())
}
fn validate_record(
    r: &Record,
    limits: Limits,
    receipt: &ProducerReceipt,
    work: &mut TypeWorkBudget,
) -> Result<(), ReceiptFailure> {
    validate(&r.observation, limits, work)?;
    if r.required.len() > limits.paths || r.tools_before.len() != 3 {
        return Err(ReceiptFailure::Resource);
    }
    r.declared_limits.validate()?;
    required_association(r, receipt, work)?;
    pay(work, r.tools_before.len())?;
    for (before, after) in r.tools_before.iter().zip(&r.observation.tools) {
        pay(
            work,
            before
                .path
                .len()
                .checked_add(after.path.len())
                .and_then(|n| n.checked_add(128))
                .ok_or(ReceiptFailure::Resource)?,
        )?;
        before.pin().artifact()?;
        after.pin().artifact()?;
        if !Path::new(&before.path).is_absolute() || before.bytes > limits.file_bytes as u64 {
            return Err(ReceiptFailure::Malformed);
        }
    }
    if r.tools_before != r.observation.tools {
        return Err(ReceiptFailure::Association);
    }
    let observer = super::checked_receipt::pin(include_bytes!("checked_link_observer.py"), work)?;
    pay(work, 4096)?;
    let config = serde_json::to_vec(&r.declared_limits).map_err(|_| ReceiptFailure::Resource)?;
    if r.observer.pin().artifact()? != observer
        || r.configuration.pin().artifact()? != super::checked_receipt::pin(&config, work)?
    {
        return Err(ReceiptFailure::Association);
    }
    let proxy = super::checked_receipt::pin(include_bytes!("checked_bfd_proxy.py"), work)?;
    pay(work, 4096)?;
    let tool_config = serde_json::to_vec(&ToolConfiguration {
        version: 1,
        tool: &r.tools_before[1],
        observer: &r.observer,
        proxy: &r.proxy,
        work_limit: proxy_work(&r.tools_before[1], &r.observer, &r.proxy, r.declared_limits)?,
    })
    .map_err(|_| ReceiptFailure::Resource)?;
    if r.observation.bfd.work_used == 0
        || r.observation.bfd.work_used
            > proxy_work(&r.tools_before[1], &r.observer, &r.proxy, r.declared_limits)?
    {
        return Err(ReceiptFailure::Resource);
    }
    let prefix = Path::new(&r.proxy.path)
        .parent()
        .ok_or(ReceiptFailure::Association)?;
    if r.proxy.pin().artifact()? != proxy
        || r.proxy != r.observation.bfd.proxy
        || r.tool_configuration != r.observation.bfd.configuration
        || r.tool_configuration.pin().artifact()?
            != super::checked_receipt::pin(&tool_config, work)?
        || Path::new(&r.proxy.path)
            .file_name()
            .is_none_or(|n| n != "ld.bfd")
        || prefix.file_name().is_none_or(|n| n != "selected-bfd")
        || Path::new(&r.tool_configuration.path) != prefix.join("tool.json")
        || Path::new(&r.observation.bfd_marker.path) != prefix.join("invocation.json")
    {
        return Err(ReceiptFailure::Association);
    }
    Ok(())
}
pub(super) fn binding(
    bytes: &[u8],
    limits: Limits,
    receipt: &ProducerReceipt,
    work: &mut TypeWorkBudget,
) -> Result<(ArtifactPin, ArtifactPin), ReceiptFailure> {
    if bytes.len() > limits.record_bytes {
        return Err(ReceiptFailure::Resource);
    }
    pay(work, bytes.len())?;
    let r: Record = serde_json::from_slice(bytes).map_err(|_| ReceiptFailure::Malformed)?;
    if r.version != 1 {
        return Err(ReceiptFailure::Version);
    }
    validate_record(&r, limits, receipt, work)?;
    if r.associations != associations(receipt)?
        || Some(ArtifactPin::from(&r.configuration_before_binding))
            != receipt.pin(ReceiptField::BuildConfiguration)
    {
        return Err(ReceiptFailure::Association);
    }
    Ok((
        (&r.configuration_before_binding).into(),
        super::checked_receipt::pin(bytes, work)?,
    ))
}
pub(super) fn configuration_binding(
    before: ArtifactPin,
    record: ArtifactPin,
    work: &mut TypeWorkBudget,
) -> Result<ArtifactPin, ReceiptFailure> {
    pay(work, 88)?;
    let mut h = Sha256::new();
    h.update(b"ASHLNK01");
    for p in [before, record] {
        h.update(p.bytes.to_le_bytes());
        h.update(p.sha256)
    }
    Ok(ArtifactPin {
        bytes: 88,
        sha256: h.finalize().into(),
    })
}

pub(super) fn matches(
    bytes: &[u8],
    limits: Limits,
    receipt: &ProducerReceipt,
    work: &mut TypeWorkBudget,
) -> Result<ArtifactPin, ReceiptFailure> {
    if bytes.len() > limits.record_bytes {
        return Err(ReceiptFailure::Resource);
    }
    pay(work, bytes.len())?;
    let r: Record = serde_json::from_slice(bytes).map_err(|_| ReceiptFailure::Malformed)?;
    validate_record(&r, limits, receipt, work)?;
    let before = ArtifactPin::from(&r.configuration_before_binding);
    if r.version != 1
        || r.associations != associations(receipt)?
        || receipt.pin(ReceiptField::FinalElf) != Some(r.observation.output.pin().artifact()?)
        || receipt.pin(ReceiptField::BuildConfiguration)
            != Some(configuration_binding(
                before,
                super::checked_receipt::pin(bytes, work)?,
                work,
            )?)
    {
        return Err(ReceiptFailure::Association);
    }
    Ok(before)
}

#[cfg(test)]
pub(super) fn exercise_independent_controls(
    bytes: &[u8],
    receipt: &ProducerReceipt,
    limits: Limits,
) {
    let fresh = || TypeWorkBudget::with_limit(limits.work);
    // This is called only after the genuine same-build canonical link succeeds.
    matches(bytes, limits, receipt, &mut fresh()).unwrap();
    let decode = || serde_json::from_slice::<Record>(bytes).unwrap();
    let mut measured = fresh();
    matches(bytes, limits, receipt, &mut measured).unwrap();
    let cost = measured.used();
    for prefix in [0, 7] {
        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
        exact.charge(prefix).unwrap();
        matches(bytes, limits, receipt, &mut exact).unwrap();
        assert_eq!(exact.used(), prefix + cost);
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            matches(bytes, limits, receipt, &mut short),
            Err(ReceiptFailure::Resource)
        );
        assert!(matches(bytes, limits, receipt, &mut short).is_err());
        matches(
            bytes,
            limits,
            receipt,
            &mut TypeWorkBudget::with_limit(cost),
        )
        .unwrap();
    }
    let mut exact = limits;
    exact.record_bytes = bytes.len();
    matches(bytes, exact, receipt, &mut fresh()).unwrap();
    exact.record_bytes -= 1;
    assert_eq!(
        matches(bytes, exact, receipt, &mut fresh()),
        Err(ReceiptFailure::Resource)
    );
    let mut total = limits;
    let r = decode();
    total.total_bytes = r
        .observation
        .inputs
        .iter()
        .chain(&r.observation.responses)
        .map(|p| p.bytes as usize)
        .sum();
    matches(bytes, total, receipt, &mut fresh()).unwrap();
    total.total_bytes -= 1;
    assert_eq!(
        matches(bytes, total, receipt, &mut fresh()),
        Err(ReceiptFailure::Resource)
    );
    // Outer receipt substitutions deliberately keep the original immutable
    // association. The following inner tests instead rebind that data digest;
    // they must reach the independent observer/config/tool/membership checks.
    for which in 0..13 {
        let mut r = decode();
        match which {
            0 => r.observer.sha256 = "00".repeat(32),
            1 => r.configuration.sha256 = "00".repeat(32),
            2 => r.observation.tools[0].sha256 = r.observation.tools[1].sha256.clone(),
            3 => {
                r.observation.inputs.pop();
            }
            4 => r.observation.bfd.tool.sha256 = "00".repeat(32),
            5 => r.observation.command[1] = "-B/donor".into(),
            6 => r.observation.bfd.output = "/donor/output".into(),
            7 => r.observation.bfd.attempted_fd_exec = false,
            8 => r.observation.prefixes[0].entries[0].name = "collect2".into(),
            9 => r.proxy.sha256 = "00".repeat(32),
            10 => r.observation.bfd.arguments[0].push_str("-donor"),
            11 => r.observation.bfd.work_used -= 1,
            _ => r.observation.bfd_marker.path = "/donor/invocation.json".into(),
        }
        let before = ArtifactPin::from(&r.configuration_before_binding);
        let data = serde_json::to_vec(&r).unwrap();
        let new_pin = configuration_binding(
            before,
            super::checked_receipt::pin(&data, &mut fresh()).unwrap(),
            &mut fresh(),
        )
        .unwrap();
        let forged = receipt.substituted_configuration_data_for_test(new_pin);
        assert_eq!(
            matches(&data, limits, &forged, &mut fresh()),
            Err(ReceiptFailure::Association)
        );
        assert_eq!(
            forged.activate(),
            Err(ReceiptFailure::ProtectedAuthorityUnavailable)
        );
    }
    for which in 0..5 {
        let mut r = decode();
        match which {
            0 => r.associations[0].sha256[0] ^= 1,
            1 => r.observation.tools[0].sha256 = r.observation.tools[1].sha256.clone(),
            2 => r.configuration.sha256 = r.observer.sha256.clone(),
            3 => {
                r.observation.inputs.pop();
            }
            _ => r.observation.loads[0] = "/unsupported-donor.o".into(),
        }
        assert_eq!(
            matches(
                &serde_json::to_vec(&r).unwrap(),
                limits,
                receipt,
                &mut fresh()
            ),
            Err(ReceiptFailure::Association)
        );
    }
    let mut unknown = serde_json::to_value(decode()).unwrap();
    unknown
        .as_object_mut()
        .unwrap()
        .insert("unsupported".into(), true.into());
    assert_eq!(
        matches(
            &serde_json::to_vec(&unknown).unwrap(),
            limits,
            receipt,
            &mut fresh()
        ),
        Err(ReceiptFailure::Malformed)
    );
    let mut duplicate = decode();
    duplicate
        .observation
        .responses
        .push(duplicate.observation.inputs[0].clone());
    assert!(
        matches(
            &serde_json::to_vec(&duplicate).unwrap(),
            limits,
            receipt,
            &mut fresh()
        )
        .is_err()
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    fn limits() -> Limits {
        Limits {
            file_bytes: 1024 * 1024,
            total_bytes: 8 * 1024 * 1024,
            map_bytes: 1024 * 1024,
            output_bytes: 4096,
            record_bytes: 65536,
            paths: 64,
            arguments: 256,
            seconds: 2,
            cargo_bytes: 4096,
            cargo_seconds: 2,
            work: 16 * 1024 * 1024,
        }
    }
    #[test]
    fn root_link_map_boundaries_and_work_are_paid() {
        let canonical=b"Linker script and memory map\nLOAD /actual/input.o\nOUTPUT(/actual/result elf64-x86-64)\n";
        let mut measured = TypeWorkBudget::with_limit(4096);
        assert_eq!(
            map_loads(canonical, limits(), &mut measured).unwrap(),
            vec!["/actual/input.o"]
        );
        let cost = measured.used();
        for prefix in [0, 3] {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            map_loads(canonical, limits(), &mut exact).unwrap();
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                map_loads(canonical, limits(), &mut short),
                Err(ReceiptFailure::Resource)
            );
            assert!(map_loads(canonical, limits(), &mut short).is_err());
            map_loads(canonical, limits(), &mut TypeWorkBudget::with_limit(cost)).unwrap();
        }
        for hostile in [
            b"LOAD /actual/input.o\n".as_slice(),
            b"Linker script and memory map\nLOAD relative.o\nOUTPUT(result elf64-x86-64)\n",
            b"Linker script and memory map\nLOAD /two names.o\nOUTPUT(result elf64-x86-64)\n",
        ] {
            assert_eq!(
                map_loads(hostile, limits(), &mut TypeWorkBudget::with_limit(4096)),
                Err(ReceiptFailure::Malformed)
            );
        }
        let mut one = limits();
        one.paths = 1;
        assert_eq!(map_loads(b"Linker script and memory map\nLOAD /one.o\nLOAD /two.o\nOUTPUT(result elf64-x86-64)\n",one,&mut TypeWorkBudget::with_limit(4096)),Err(ReceiptFailure::Resource));
    }
    #[test]
    fn root_link_effective_selector_is_paid_and_requires_final_bfd() {
        let args = ["-fuse-ld=lld".to_owned(), "-fuse-ld=bfd".to_owned()];
        let paid = args.iter().map(|s| s.len() + 1).sum();
        require_bfd(&args, &mut TypeWorkBudget::with_limit(paid)).unwrap();
        assert_eq!(
            require_bfd(&args, &mut TypeWorkBudget::with_limit(paid - 1)),
            Err(ReceiptFailure::Resource)
        );
        for bad in [
            vec![],
            vec!["-fuse-ld=bfd", "-fuse-ld=lld"],
            vec!["-fuse-ld=gold", "-fuse-ld=bfd"],
            vec!["-fuse-ld=/usr/bin/ld.bfd", "-fuse-ld=bfd"],
            vec!["-fuse-ld", "bfd"],
        ] {
            let bad = bad.into_iter().map(str::to_owned).collect::<Vec<_>>();
            assert_eq!(
                require_bfd(&bad, &mut TypeWorkBudget::with_limit(4096)),
                Err(ReceiptFailure::Input)
            );
        }
        require_bfd(&args, &mut TypeWorkBudget::with_limit(paid)).unwrap();
    }
    #[test]
    fn root_link_script_subset_refuses_unknown_search_relative_and_duplicate() {
        let valid = "/* GNU ld script */ OUTPUT_FORMAT(elf64-x86-64) GROUP ( /actual/libone.a /actual/libtwo.a )";
        assert_eq!(
            script_members(valid, &mut TypeWorkBudget::with_limit(4096)).unwrap(),
            vec!["/actual/libone.a", "/actual/libtwo.a"]
        );
        for bad in [
            "OUTPUT_FORMAT(elf64-x86-64) GROUP ( relative.a )",
            "OUTPUT_FORMAT(elf64-x86-64) GROUP ( -lm )",
            "OUTPUT_FORMAT(elf64-x86-64) GROUP ( /one.a /one.a )",
            "OUTPUT_FORMAT(elf64-x86-64) INCLUDE /extra.ld",
            "OUTPUT_FORMAT(elf64-x86-64) GROUP ( AS_NEEDED ( /one.a ) )",
        ] {
            assert!(script_members(bad, &mut TypeWorkBudget::with_limit(4096)).is_err());
        }
    }
    #[test]
    fn root_link_checked_cargo_output_timeout_and_preentry_work_are_bounded() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir =
            std::env::temp_dir().join(format!("ash-checked-cargo-{}-{nonce}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        let log = dir.join("build.log");
        let mut success = std::process::Command::new("/usr/bin/printf");
        success.arg("abc");
        let status = super::super::checked_native_build::run_root_cargo(
            &mut success,
            &dir,
            &log,
            limits(),
            &mut TypeWorkBudget::with_limit(limits().work),
        )
        .unwrap();
        assert!(status.success());
        assert_eq!(fs::read(&log).unwrap(), b"abc");
        let mut small = limits();
        small.cargo_bytes = 2;
        let mut flood = std::process::Command::new("/usr/bin/yes");
        assert!(matches!(
            super::super::checked_native_build::run_root_cargo(
                &mut flood,
                &dir,
                &log,
                small,
                &mut TypeWorkBudget::with_limit(small.work)
            ),
            Err(ReceiptFailure::Resource)
        ));
        let mut short = limits();
        short.cargo_seconds = 1;
        let mut stall = std::process::Command::new("/usr/bin/sleep");
        stall.arg("30");
        assert!(matches!(
            super::super::checked_native_build::run_root_cargo(
                &mut stall,
                &dir,
                &log,
                short,
                &mut TypeWorkBudget::with_limit(short.work)
            ),
            Err(ReceiptFailure::Resource)
        ));
        let lifecycle: serde_json::Value =
            serde_json::from_slice(&fs::read(dir.join("cargo.lifecycle.json")).unwrap()).unwrap();
        assert_eq!(lifecycle["child_reaped"], true);
        assert_eq!(lifecycle["owned_group_empty"], true);
        let marker = dir.join("must-not-enter");
        let mut entry = std::process::Command::new("/usr/bin/touch");
        entry.arg(&marker);
        assert!(matches!(
            super::super::checked_native_build::run_root_cargo(
                &mut entry,
                &dir,
                &log,
                limits(),
                &mut TypeWorkBudget::with_limit(0)
            ),
            Err(ReceiptFailure::Resource)
        ));
        assert!(!marker.exists());
        fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn root_link_bfd_proxy_records_attempt_only_and_refuses_donors() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir =
            std::env::temp_dir().join(format!("ash-bfd-proxy-{}-{nonce}", std::process::id()));
        let prefix = dir.join("selected-bfd");
        fs::create_dir_all(&prefix).unwrap();
        fs::write(
            dir.join("observer.py"),
            include_bytes!("checked_link_observer.py"),
        )
        .unwrap();
        fs::write(
            prefix.join("ld.bfd"),
            include_bytes!("checked_bfd_proxy.py"),
        )
        .unwrap();
        let mut selected = limits();
        selected.file_bytes = 16 * 1024 * 1024;
        selected.work = 64 * 1024 * 1024;
        fs::write(
            dir.join("limits.json"),
            serde_json::to_vec(&selected).unwrap(),
        )
        .unwrap();
        let mut work = TypeWorkBudget::with_limit(selected.work);
        let tool = observe(Path::new("/usr/bin/ld.bfd"), selected.file_bytes, &mut work).unwrap();
        let observer = observe(&dir.join("observer.py"), selected.record_bytes, &mut work).unwrap();
        let proxy = observe(&prefix.join("ld.bfd"), selected.record_bytes, &mut work).unwrap();
        fs::write(
            prefix.join("tool.json"),
            serde_json::to_vec(&ToolConfiguration {
                version: 1,
                tool: &tool,
                observer: &observer,
                proxy: &proxy,
                work_limit: proxy_work(&tool, &observer, &proxy, selected).unwrap(),
            })
            .unwrap(),
        )
        .unwrap();
        fs::write(
            dir.join("output.json"),
            serde_json::to_vec(
                &serde_json::json!({"output":dir.join("never-linked").to_str().unwrap()}),
            )
            .unwrap(),
        )
        .unwrap();
        // Inject before FDexec: this verifies opened identity/attempt bookkeeping,
        // not native BFD execution, a successful link or any checked authority.
        let program = r#"import runpy,sys,os,json
from pathlib import Path
proxy=Path(sys.argv[1]);m=runpy.run_path(str(proxy));sys.argv=[str(proxy),'-o',str(proxy.parent.parent/'never-linked')]
seen=[]
def no_exec(fd,args,env):
 seen.append(fd);assert os.fstat(fd).st_size>0
 assert args[0]==str(Path('/usr/bin/ld.bfd').resolve())
 raise RuntimeError('injected before native tool execution')
os.execve=no_exec;os.supports_fd.add(no_exec)
try:m['main']()
except RuntimeError as e:assert 'injected before native' in str(e)
else:raise AssertionError('unexpected FDexec return')
assert len(seen)==1
try:os.fstat(seen[0])
except OSError:pass
else:raise AssertionError('verified FD leaked')
marker=proxy.parent/'invocation.json';record=json.loads(marker.read_text())
assert record['attempted_fd_exec'] is True and record['output']==sys.argv[-1]
assert not Path(sys.argv[-1]).exists()
m=runpy.run_path(str(proxy))
try:m['main']()
except FileExistsError:pass
else:raise AssertionError('duplicate BFD entry accepted')
assert len(seen)==1
marker.unlink();config=proxy.parent/'tool.json';original=config.read_bytes();bad=json.loads(original);bad['tool']['sha256']='00'*32;config.write_text(json.dumps(bad))
m=runpy.run_path(str(proxy))
try:m['main']()
except RuntimeError as e:assert 'opened identity' in str(e)
else:raise AssertionError('donor BFD pin accepted')
assert not marker.exists() and len(seen)==1
config.write_bytes(original);os.supports_fd.remove(no_exec)
m=runpy.run_path(str(proxy))
try:m['main']()
except RuntimeError as e:assert 'FD execution' in str(e)
else:raise AssertionError('unsupported FDexec accepted')
assert not marker.exists() and len(seen)==1
"#;
        assert!(
            std::process::Command::new("/usr/bin/python3")
                .args(["-c", program])
                .arg(prefix.join("ld.bfd"))
                .status()
                .unwrap()
                .success()
        );
        fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn root_link_observer_response_and_postspawn_cleanup_controls() {
        use std::process::Command;
        use std::sync::atomic::{AtomicU64, Ordering};
        static ID: AtomicU64 = AtomicU64::new(0);
        let dir = std::env::temp_dir().join(format!(
            "ash-root-link-observer-{}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
            ID.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&dir).unwrap();
        fs::write(
            dir.join("observer.py"),
            include_bytes!("checked_link_observer.py"),
        )
        .unwrap();
        fs::write(
            dir.join("limits.json"),
            serde_json::to_vec(&limits()).unwrap(),
        )
        .unwrap();
        // Inject only a trusted sleep utility and an error after actual spawn;
        // no linker/native/image authority or selected native function exists.
        let program = r#"import runpy,sys,subprocess,os
m=runpy.run_path(sys.argv[1]); parse=m['response_tokens']
assert parse(b'"/one.o" -m64')==['/one.o','-m64']
m['require_bfd'](['-fuse-ld=lld','-fuse-ld=bfd'])
for bad in [[],['-fuse-ld=bfd','-fuse-ld=lld'],['-fuse-ld=gold','-fuse-ld=bfd'],['-fuse-ld=/usr/bin/ld.bfd','-fuse-ld=bfd'],['-fuse-ld','bfd']]:
 try: m['require_bfd'](bad)
 except RuntimeError: pass
 else: raise AssertionError('accepted unsupported effective selector')
for b in [b'"unterminated',br'/escaped\ name.o',b'"/space name.o"']:
 try: parse(b)
 except RuntimeError: pass
 else: raise AssertionError('accepted unknown response')
real=subprocess.Popen; children=[]
def spawn(*args,**kw):
 assert args[0][-1]=='-Wl,--no-print-map-discarded,-Map=-'
 assert sum('Map=' in a for a in args[0])==1
 p=real(['/usr/bin/sleep','30'],**kw);children.append(p);return p
subprocess.Popen=spawn
class Broken:
 def __init__(self): raise RuntimeError('injected after spawn')
m['run'].__globals__['selectors'].DefaultSelector=Broken
try: m['run']([])
except RuntimeError: pass
else: raise AssertionError('missing postspawn refusal')
assert len(children)==1 and children[0].poll() is not None
try: os.killpg(children[0].pid,0)
except ProcessLookupError: pass
else: raise AssertionError('owned descendant survived')
subprocess.Popen=real
import signal,time
child_code = """import runpy,subprocess,sys,os
m=runpy.run_path(sys.argv[1]);real=subprocess.Popen
def spawn(*args,**kw):
 p=real(['/usr/bin/sleep','30'],**kw)
 with open(sys.argv[2],'w') as f: f.write(str(p.pid))
 return p
subprocess.Popen=spawn
try: m['run']([])
except RuntimeError as e:
 assert 'terminated' in str(e)
else: raise AssertionError('external termination did not refuse')
"""
for sig in [signal.SIGTERM,signal.SIGINT,signal.SIGHUP]:
 marker=sys.argv[1]+'.child-'+str(sig)
 outer=real(['/usr/bin/python3','-c',child_code,sys.argv[1],marker],start_new_session=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
 owned=None
 try:
  end=time.monotonic()+3
  while not os.path.exists(marker) and time.monotonic()<end: time.sleep(0.01)
  assert os.path.exists(marker)
  with open(marker) as f: owned=int(f.read())
  outer.send_signal(sig);assert outer.wait(timeout=5)==0
  try: os.killpg(owned,0)
  except ProcessLookupError: pass
  else: raise AssertionError('external signal left owned descendant')
 finally:
  if outer.poll() is None:
   os.killpg(outer.pid,signal.SIGKILL);outer.wait()
  if owned is not None:
   try: os.killpg(owned,signal.SIGKILL)
   except ProcessLookupError: pass
"#;
        let status = Command::new("/usr/bin/python3")
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("LC_ALL", "C")
            .args(["-c", program])
            .arg(dir.join("observer.py"))
            .status()
            .unwrap();
        assert!(status.success());
        fs::remove_dir_all(dir).unwrap();
    }
}
