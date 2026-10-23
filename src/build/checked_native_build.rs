//! Same-build C/header/ABI observations. These are not complete tool/native
//! closure, independent premises, approval, or an execution capability.
use super::{
    checked_receipt::{ArtifactPin, ProducerReceipt, ReceiptFailure, ReceiptField},
    image::NativeBuildImage,
};
use crate::types::TypeWorkBudget;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeSet,
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

#[derive(Clone, Copy, Debug)]
pub(super) struct Limits {
    pub file_bytes: usize,
    pub total_bytes: usize,
    pub output_bytes: usize,
    pub paths: usize,
    pub record_bytes: usize,
    pub command_seconds: u32,
    pub work: usize,
}

pub(super) struct Request<'a> {
    pub source: &'a Path,
    pub header: &'a Path,
    pub directory: &'a Path,
    pub limits: Limits,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Pin {
    bytes: u64,
    sha256: [u8; 32],
}
impl From<ArtifactPin> for Pin {
    fn from(p: ArtifactPin) -> Self {
        Self {
            bytes: p.bytes,
            sha256: p.sha256,
        }
    }
}
impl From<&Pin> for ArtifactPin {
    fn from(p: &Pin) -> Self {
        Self {
            bytes: p.bytes,
            sha256: p.sha256,
        }
    }
}
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Input {
    path: String,
    device: u64,
    inode: u64,
    pin: Pin,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Invocation {
    tool: String,
    arguments: Vec<String>,
    stdout: Pin,
    stderr: Pin,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Record {
    version: u32,
    target: String,
    environment: Vec<(String, String)>,
    inputs: Vec<Input>,
    tools: Vec<Input>,
    commands: Vec<Invocation>,
    helper_dependencies: Vec<String>,
    abi_dependencies: Vec<String>,
    archive: Input,
    // These are actual same-emission/configuration observations, not claims of
    // native behavior or whole tool/runtime closure.
    associations: Vec<Pin>,
    configuration_before_binding: Option<Pin>,
}

#[derive(Debug)]
pub(super) struct NativeBuild {
    record: Record,
    limits: Limits,
    work: TypeWorkBudget,
}

fn pay(work: &mut TypeWorkBudget, n: usize) -> Result<(), ReceiptFailure> {
    work.charge(n).map_err(|()| ReceiptFailure::Resource)
}
fn io<T>(r: std::io::Result<T>) -> Result<T, ReceiptFailure> {
    r.map_err(|_| ReceiptFailure::Input)
}
fn pin(bytes: &[u8], work: &mut TypeWorkBudget) -> Result<Pin, ReceiptFailure> {
    Ok(super::checked_receipt::pin(bytes, work)?.into())
}
fn path_string(path: &Path) -> Result<String, ReceiptFailure> {
    path.to_str()
        .map(str::to_owned)
        .ok_or(ReceiptFailure::Input)
}

#[cfg(unix)]
fn observe(
    path: &Path,
    limits: Limits,
    work: &mut TypeWorkBudget,
) -> Result<Input, ReceiptFailure> {
    use std::os::unix::fs::MetadataExt;
    let path = io(fs::canonicalize(path))?;
    pay(
        work,
        path.as_os_str()
            .len()
            .checked_add(1)
            .ok_or(ReceiptFailure::Resource)?,
    )?;
    let mut file = io(fs::File::open(&path))?;
    let before = io(file.metadata())?;
    if !before.is_file() || before.len() > limits.file_bytes as u64 {
        return Err(ReceiptFailure::Resource);
    }
    let mut sha = Sha256::new();
    let mut buffer = [0; 65536];
    let mut bytes = 0usize;
    loop {
        let n = io(file.read(&mut buffer))?;
        if n == 0 {
            break;
        }
        bytes = bytes.checked_add(n).ok_or(ReceiptFailure::Resource)?;
        if bytes > limits.file_bytes {
            return Err(ReceiptFailure::Resource);
        }
        pay(work, n)?;
        sha.update(&buffer[..n]);
    }
    let after = io(file.metadata())?;
    let named = io(fs::metadata(&path))?;
    let identity = |m: &fs::Metadata| {
        (
            m.dev(),
            m.ino(),
            m.len(),
            m.mtime(),
            m.mtime_nsec(),
            m.ctime(),
            m.ctime_nsec(),
        )
    };
    if identity(&before) != identity(&after)
        || identity(&after) != identity(&named)
        || bytes as u64 != before.len()
    {
        return Err(ReceiptFailure::Association);
    }
    Ok(Input {
        path: path_string(&path)?,
        device: before.dev(),
        inode: before.ino(),
        pin: Pin {
            bytes: bytes as u64,
            sha256: sha.finalize().into(),
        },
    })
}
#[cfg(not(unix))]
fn observe(_: &Path, _: Limits, _: &mut TypeWorkBudget) -> Result<Input, ReceiptFailure> {
    Err(ReceiptFailure::Input)
}

fn read(path: &Path, cap: usize, work: &mut TypeWorkBudget) -> Result<Vec<u8>, ReceiptFailure> {
    let mut file = io(fs::File::open(path))?;
    let n = io(file.metadata())?.len();
    if n > cap as u64 {
        return Err(ReceiptFailure::Resource);
    }
    let n = usize::try_from(n).map_err(|_| ReceiptFailure::Resource)?;
    pay(work, n.checked_mul(2).ok_or(ReceiptFailure::Resource)?)?;
    let mut b = Vec::new();
    b.try_reserve_exact(n)
        .map_err(|_| ReceiptFailure::Resource)?;
    io(file.by_ref().take(n as u64 + 1).read_to_end(&mut b))?;
    if b.len() != n {
        return Err(ReceiptFailure::Association);
    }
    Ok(b)
}

// Restricted make dependency grammar. Escaped spaces/backslashes, extra targets,
// relative paths, duplicates and nonregular/unknown paths explicitly refuse.
fn dependencies(
    bytes: &[u8],
    limits: Limits,
    work: &mut TypeWorkBudget,
) -> Result<Vec<String>, ReceiptFailure> {
    if bytes.len() > limits.output_bytes {
        return Err(ReceiptFailure::Resource);
    }
    pay(
        work,
        bytes.len().checked_mul(3).ok_or(ReceiptFailure::Resource)?,
    )?;
    let text = std::str::from_utf8(bytes)
        .map_err(|_| ReceiptFailure::Malformed)?
        .replace("\\\n", " ");
    let text = text
        .strip_prefix("ash-native:")
        .ok_or(ReceiptFailure::Malformed)?;
    let mut set = BTreeSet::new();
    for value in text.split_whitespace() {
        pay(
            work,
            value.len().checked_add(4).ok_or(ReceiptFailure::Resource)?,
        )?;
        if !value.starts_with('/')
            || value.contains(['\\', ':', '$', '#'])
            || !set.insert(value.to_owned())
        {
            return Err(ReceiptFailure::Malformed);
        }
        if set.len() > limits.paths {
            return Err(ReceiptFailure::Resource);
        }
    }
    if set.is_empty() {
        return Err(ReceiptFailure::Malformed);
    }
    Ok(set.into_iter().collect())
}

fn environment() -> Vec<(String, String)> {
    vec![
        ("PATH".into(), "/usr/bin:/bin".into()),
        ("LC_ALL".into(), "C".into()),
        ("TZ".into(), "UTC".into()),
    ]
}

// Each command owns a fresh process group. The fixed, observed kill utility
// signals only that group; timeout is an additional command deadline, not the
// cleanup authority. Every post-spawn Result path finishes this owner first.
struct OwnedCommand {
    child: std::process::Child,
    group: u32,
    settled: bool,
}
impl OwnedCommand {
    fn signal(&self, signal: &str) -> Result<bool, ReceiptFailure> {
        let status = io(Command::new("/usr/bin/kill")
            .args([signal, "--", &format!("-{}", self.group)])
            .env_clear()
            .env("LC_ALL", "C")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status())?;
        Ok(status.success())
    }
    fn probe(&mut self) -> Result<(bool, bool), ReceiptFailure> {
        let exited = io(self.child.try_wait())?.is_some();
        Ok((exited, !self.signal("-0")?))
    }
    fn finish(&mut self, stop: bool) -> Result<(), ReceiptFailure> {
        self.finish_with_probe(stop, Self::probe)
    }
    fn finish_with_probe(
        &mut self,
        stop: bool,
        mut probe: impl FnMut(&mut Self) -> Result<(bool, bool), ReceiptFailure>,
    ) -> Result<(), ReceiptFailure> {
        let mut failure = None;
        if stop && self.signal("-TERM").is_err() {
            failure = Some(ReceiptFailure::Input);
        }
        let deadline = Instant::now() + Duration::from_secs(1);
        while Instant::now() < deadline {
            match probe(self) {
                Ok((true, true)) => {
                    self.settled = true;
                    return failure.map_or(Ok(()), Err);
                }
                Ok(_) => {}
                Err(error) => {
                    failure = Some(error);
                    break;
                }
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        // Probe errors never bypass forced group signalling and direct reap.
        // Preserve the refusal even if a later independent probe can settle.
        if self.signal("-TERM").is_err() {
            failure = Some(ReceiptFailure::Input);
        }
        if self.signal("-KILL").is_err() {
            failure = Some(ReceiptFailure::Input);
        }
        let _ = self.child.kill();
        if self.child.wait().is_err() {
            failure = Some(ReceiptFailure::Input);
        }
        let deadline = Instant::now() + Duration::from_secs(1);
        while Instant::now() < deadline {
            match probe(self) {
                Ok((true, true)) => {
                    self.settled = true;
                    return failure.map_or(Ok(()), Err);
                }
                Ok(_) => {}
                Err(error) => {
                    failure = Some(error);
                    break;
                }
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        // An unavailable probe is not evidence of an empty group.
        Err(failure.unwrap_or(ReceiptFailure::Input))
    }
}
impl Drop for OwnedCommand {
    fn drop(&mut self) {
        if !self.settled {
            let _ = self.finish(true);
        }
    }
}

// A pipe reader writes at most cap bytes, reports the first excess byte, and
// closes the pipe. Backpressure prevents unbounded buffering or disk output.
fn capture(mut input: impl Read, mut file: fs::File, cap: usize) -> Result<(), ReceiptFailure> {
    use std::io::Write;
    let mut buffer = [0u8; 4096];
    let mut written = 0usize;
    loop {
        let want = buffer
            .len()
            .min(cap.saturating_sub(written).saturating_add(1));
        let n = io(input.read(&mut buffer[..want]))?;
        if n == 0 {
            return Ok(());
        }
        let admitted = n.min(cap.saturating_sub(written));
        io(file.write_all(&buffer[..admitted]))?;
        written = written
            .checked_add(admitted)
            .ok_or(ReceiptFailure::Resource)?;
        if admitted != n {
            return Err(ReceiptFailure::Resource);
        }
    }
}
fn run(
    directory: &Path,
    tool: &Path,
    args: &[String],
    limits: Limits,
    work: &mut TypeWorkBudget,
    index: usize,
) -> Result<(Invocation, Vec<u8>), ReceiptFailure> {
    let size = args
        .iter()
        .try_fold(0usize, |n, s| n.checked_add(s.len() + 1))
        .ok_or(ReceiptFailure::Resource)?;
    // Reserve both bounded stream-copy budgets and polling/cleanup work before
    // starting an irreversible tool. Failure retains these spent reservations.
    let reserved = limits
        .output_bytes
        .checked_mul(6)
        .and_then(|n| n.checked_add((limits.command_seconds as usize + 2) * 400 + 4096 + 8192 + 64))
        .and_then(|n| n.checked_add(size))
        .ok_or(ReceiptFailure::Resource)?;
    pay(work, reserved)?;
    let out = directory.join(format!("command-{index}.stdout"));
    let err = directory.join(format!("command-{index}.stderr"));
    let out_file = io(fs::File::create(&out))?;
    let err_file = io(fs::File::create(&err))?;
    let mut command = Command::new("/usr/bin/timeout");
    command
        .args(["--signal=TERM", "--kill-after=1s"])
        .arg(format!("{}s", limits.command_seconds))
        .arg(tool)
        .args(args)
        .current_dir(directory)
        .env_clear()
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for (k, v) in environment() {
        command.env(k, v);
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    let child = io(command.spawn())?;
    let mut owned = OwnedCommand {
        group: child.id(),
        child,
        settled: false,
    };
    let stdout = owned.child.stdout.take().ok_or(ReceiptFailure::Input)?;
    let stderr = owned.child.stderr.take().ok_or(ReceiptFailure::Input)?;
    let (sender, receiver) = std::sync::mpsc::channel();
    let mut workers = Vec::new();
    workers
        .try_reserve_exact(2)
        .map_err(|_| ReceiptFailure::Resource)?;
    let cap = limits.output_bytes;
    let first = sender.clone();
    workers.push(io(std::thread::Builder::new()
        .name("ash-cc-stdout".into())
        .spawn(move || {
            let result = capture(stdout, out_file, cap);
            let _ = first.send(result);
            result
        }))?);
    let second = std::thread::Builder::new()
        .name("ash-cc-stderr".into())
        .spawn(move || {
            let result = capture(stderr, err_file, cap);
            let _ = sender.send(result);
            result
        });
    match second {
        Ok(worker) => workers.push(worker),
        Err(_) => {
            let _ = owned.finish(true);
            for worker in workers {
                let _ = worker.join();
            }
            return Err(ReceiptFailure::Input);
        }
    }
    let started = Instant::now();
    let status = (|| {
        loop {
            for result in receiver.try_iter() {
                result?;
            }
            if started.elapsed() > Duration::from_secs(u64::from(limits.command_seconds) + 2) {
                return Err(ReceiptFailure::Input);
            }
            if let Some(status) = io(owned.child.try_wait())? {
                return if status.success() {
                    Ok(())
                } else {
                    Err(ReceiptFailure::Input)
                };
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    })();
    let cleanup = owned.finish(status.is_err());
    let mut captured = Ok(());
    for worker in workers {
        match worker.join() {
            Ok(Ok(())) => {}
            Ok(Err(e)) => captured = Err(e),
            Err(_) => captured = Err(ReceiptFailure::Input),
        }
    }
    let settled = cleanup.and(captured).and(status);
    let lifecycle=serde_json::to_vec(&serde_json::json!({"group":owned.group,"child_reaped":owned.child.try_wait().ok().flatten().is_some(),"owned_group_empty":owned.settled,"process_result":format!("{settled:?}")})).map_err(|_|ReceiptFailure::Resource)?;
    io(fs::write(
        directory.join(format!("command-{index}.lifecycle.json")),
        lifecycle,
    ))?;
    settled?;
    // All processes and both pipe owners are settled before fallible reads/hash.
    let stdout = read(&out, limits.output_bytes, work)?;
    let stderr = read(&err, limits.output_bytes, work)?;
    Ok((
        Invocation {
            tool: path_string(tool)?,
            arguments: args.to_vec(),
            stdout: pin(&stdout, work)?,
            stderr: pin(&stderr, work)?,
        },
        stdout,
    ))
}

static IDS: AtomicU64 = AtomicU64::new(0);
impl NativeBuild {
    pub(super) fn build(
        build: &NativeBuildImage,
        request: Request<'_>,
    ) -> Result<Self, ReceiptFailure> {
        let limits = request.limits;
        if limits.file_bytes == 0
            || limits.total_bytes == 0
            || limits.output_bytes == 0
            || limits.paths == 0
            || limits.record_bytes == 0
            || limits.command_seconds == 0
            || limits.command_seconds > 120
        {
            return Err(ReceiptFailure::Resource);
        }
        let mut work = TypeWorkBudget::with_limit(limits.work);
        pay(&mut work, 64)?;
        io(fs::create_dir_all(request.directory))?;
        let directory = loop {
            let p = request.directory.join(format!(
                "native-{}-{}",
                std::process::id(),
                IDS.fetch_add(1, Ordering::Relaxed)
            ));
            #[cfg(unix)]
            let created = {
                use std::os::unix::fs::DirBuilderExt;
                fs::DirBuilder::new().mode(0o700).create(&p)
            };
            #[cfg(not(unix))]
            let created = fs::create_dir(&p);
            match created {
                Ok(()) => break io(fs::canonicalize(p))?,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(_) => return Err(ReceiptFailure::Input),
            }
        };
        let original_source = observe(request.source, limits, &mut work)?;
        let original_header = observe(request.header, limits, &mut work)?;
        if request.source.parent() != request.header.parent() {
            return Err(ReceiptFailure::Input);
        }
        let header_name = request
            .header
            .file_name()
            .and_then(|s| s.to_str())
            .ok_or(ReceiptFailure::Input)?;
        if header_name.is_empty()
            || !header_name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b))
        {
            return Err(ReceiptFailure::Input);
        }
        let source = directory.join("helper.c");
        let header = directory.join(header_name);
        io(fs::write(
            &source,
            read(request.source, limits.file_bytes, &mut work)?,
        ))?;
        io(fs::write(
            &header,
            read(request.header, limits.file_bytes, &mut work)?,
        ))?;
        if observe(&source, limits, &mut work)?.pin != original_source.pin
            || observe(&header, limits, &mut work)?.pin != original_header.pin
        {
            return Err(ReceiptFailure::Association);
        }
        let mut abi = format!(
            "#include <stdint.h>\n#include <stddef.h>\n#include <stdlib.h>\n#include \"{header_name}\"\n#if !defined(__x86_64__) || !defined(__linux__) || !defined(__GLIBC__)\n#error unsupported_target\n#endif\n_Static_assert(sizeof(void*)==8 && sizeof(size_t)==8 && sizeof(int)==4,\"target layout\");\n"
        );
        for (index, bridge) in build.bridges.iter().enumerate() {
            abi.push_str(&bridge.plan.c_header_assertion(index, &mut work)?);
        }
        let abi_path = directory.join("abi.c");
        pay(&mut work, abi.len())?;
        io(fs::write(&abi_path, abi))?;
        let mut tools = Vec::new();
        for path in [
            "/usr/bin/cc",
            "/usr/bin/ar",
            "/usr/bin/ld.bfd",
            "/usr/bin/timeout",
            "/usr/bin/as",
            "/usr/bin/kill",
        ] {
            tools.push(observe(Path::new(path), limits, &mut work)?);
        }
        let cc = PathBuf::from(&tools[0].path);
        let ar = PathBuf::from(&tools[1].path);
        let mut commands = Vec::new();
        for args in [
            vec!["-dumpmachine".into()],
            vec!["-dumpfullversion".into()],
            vec!["-print-sysroot".into()],
            vec!["-print-search-dirs".into()],
            vec!["-dumpspecs".into()],
            vec!["-print-prog-name=cc1".into()],
        ] {
            let (cmd, out) = run(&directory, &cc, &args, limits, &mut work, commands.len())?;
            if args[0] == "-dumpmachine" && out != b"x86_64-linux-gnu\n" {
                return Err(ReceiptFailure::Input);
            }
            if args[0] == "-print-prog-name=cc1" {
                let value = std::str::from_utf8(&out)
                    .map_err(|_| ReceiptFailure::Input)?
                    .trim();
                if !Path::new(value).is_absolute() {
                    return Err(ReceiptFailure::Input);
                }
                tools.push(observe(Path::new(value), limits, &mut work)?);
            }
            commands.push(cmd);
        }
        let include = io(fs::canonicalize(
            request.source.parent().ok_or(ReceiptFailure::Input)?,
        ))?;
        let base = vec![
            "-std=c11".into(),
            "-Wall".into(),
            "-Wextra".into(),
            "-Werror".into(),
            // Compile actual helper definitions in the asserted prototype
            // context, even if they otherwise include a different header.
            "-include".into(),
            path_string(&abi_path)?,
            "-I".into(),
            path_string(&include)?,
        ];
        let mut sets = Vec::new();
        for (i, input) in [&source, &abi_path].into_iter().enumerate() {
            let dep = directory.join(format!("discover-{i}.d"));
            let mut args = base.clone();
            args.extend([
                "-M".into(),
                "-MT".into(),
                "ash-native".into(),
                "-MF".into(),
                path_string(&dep)?,
                path_string(input)?,
            ]);
            let (cmd, _) = run(&directory, &cc, &args, limits, &mut work, commands.len())?;
            commands.push(cmd);
            sets.push(dependencies(
                &read(&dep, limits.output_bytes, &mut work)?,
                limits,
                &mut work,
            )?);
        }
        let mut all = BTreeSet::new();
        for set in &sets {
            for p in set {
                all.insert(p.clone());
            }
        }
        all.insert(original_source.path.clone());
        all.insert(original_header.path.clone());
        if all.len() > limits.paths {
            return Err(ReceiptFailure::Resource);
        }
        let mut inputs = Vec::new();
        let mut total = 0u64;
        for p in all {
            let input = observe(Path::new(&p), limits, &mut work)?;
            total = total
                .checked_add(input.pin.bytes)
                .ok_or(ReceiptFailure::Resource)?;
            if total > limits.total_bytes as u64 {
                return Err(ReceiptFailure::Resource);
            }
            inputs.push(input);
        }
        if !inputs.contains(&original_source) || !inputs.contains(&original_header) {
            return Err(ReceiptFailure::Association);
        }
        let verify = |work: &mut TypeWorkBudget| -> Result<(), ReceiptFailure> {
            for input in inputs.iter().chain(&tools) {
                if observe(Path::new(&input.path), limits, work)? != *input {
                    return Err(ReceiptFailure::Association);
                }
            }
            Ok(())
        };
        let mut macro_args = base.clone();
        macro_args.extend([
            "-dM".into(),
            "-E".into(),
            "-v".into(),
            path_string(&abi_path)?,
        ]);
        verify(&mut work)?;
        let (cmd, _) = run(
            &directory,
            &cc,
            &macro_args,
            limits,
            &mut work,
            commands.len(),
        )?;
        commands.push(cmd);
        verify(&mut work)?;
        let object = directory.join("helper.o");
        for (i, input) in [&source, &abi_path].into_iter().enumerate() {
            verify(&mut work)?;
            let dep = directory.join(format!("actual-{i}.d"));
            let mut args = base.clone();
            args.extend([
                "-MD".into(),
                "-MT".into(),
                "ash-native".into(),
                "-MF".into(),
                path_string(&dep)?,
            ]);
            if i == 0 {
                args.extend([
                    "-c".into(),
                    path_string(input)?,
                    "-o".into(),
                    path_string(&object)?,
                ]);
            } else {
                args.extend(["-fsyntax-only".into(), path_string(input)?]);
            }
            let (cmd, _) = run(&directory, &cc, &args, limits, &mut work, commands.len())?;
            commands.push(cmd);
            verify(&mut work)?;
            if dependencies(
                &read(&dep, limits.output_bytes, &mut work)?,
                limits,
                &mut work,
            )? != sets[i]
            {
                return Err(ReceiptFailure::Association);
            }
        }
        let object_pin = observe(&object, limits, &mut work)?;
        total = total
            .checked_add(object_pin.pin.bytes)
            .ok_or(ReceiptFailure::Resource)?;
        if total > limits.total_bytes as u64 {
            return Err(ReceiptFailure::Resource);
        }
        inputs.push(object_pin);
        let archive = directory.join("libchecked-owner.a");
        let args = vec!["crsD".into(), path_string(&archive)?, path_string(&object)?];
        let (cmd, _) = run(&directory, &ar, &args, limits, &mut work, commands.len())?;
        commands.push(cmd);
        let archive = observe(&archive, limits, &mut work)?;
        total = total
            .checked_add(archive.pin.bytes)
            .ok_or(ReceiptFailure::Resource)?;
        if total > limits.total_bytes as u64 {
            return Err(ReceiptFailure::Resource);
        }
        let mut native = Self {
            record: Record {
                version: 1,
                target: super::host::NATIVE_TARGET.into(),
                environment: environment(),
                inputs,
                tools,
                commands,
                helper_dependencies: sets.remove(0),
                abi_dependencies: sets.remove(0),
                archive,
                associations: Vec::new(),
                configuration_before_binding: None,
            },
            limits,
            work,
        };
        native.verify()?;
        Ok(native)
    }
    pub(super) fn limits(&self) -> Limits {
        self.limits
    }
    pub(super) fn archive(&self) -> &Path {
        Path::new(&self.record.archive.path)
    }
    pub(super) fn verify(&mut self) -> Result<(), ReceiptFailure> {
        for input in self
            .record
            .inputs
            .iter()
            .chain(&self.record.tools)
            .chain(std::iter::once(&self.record.archive))
        {
            if observe(Path::new(&input.path), self.limits, &mut self.work)? != *input {
                return Err(ReceiptFailure::Association);
            }
        }
        Ok(())
    }
    pub(super) fn validate_receipt(
        &mut self,
        bytes: &[u8],
        receipt: &ProducerReceipt,
    ) -> Result<(), ReceiptFailure> {
        matches(bytes, receipt, self.limits, &mut self.work)
    }
    pub(super) fn finish(&mut self, receipt: &ProducerReceipt) -> Result<Vec<u8>, ReceiptFailure> {
        self.verify()?;
        self.record.associations = ASSOCIATIONS
            .iter()
            .map(|f| {
                receipt
                    .pin(*f)
                    .map(Pin::from)
                    .ok_or(ReceiptFailure::Association)
            })
            .collect::<Result<_, _>>()?;
        self.record.configuration_before_binding = Some(
            receipt
                .pin(ReceiptField::BuildConfiguration)
                .ok_or(ReceiptFailure::Association)?
                .into(),
        );
        pay(&mut self.work, self.limits.record_bytes)?;
        let bytes = serde_json::to_vec(&self.record).map_err(|_| ReceiptFailure::Resource)?;
        if bytes.len() > self.limits.record_bytes {
            return Err(ReceiptFailure::Resource);
        }
        Ok(bytes)
    }
}
const ASSOCIATIONS: [ReceiptField; 5] = [
    ReceiptField::ProgramImage,
    ReceiptField::ExpectedFacts,
    ReceiptField::OriginalMappings,
    ReceiptField::DeclaredNativeInputs,
    ReceiptField::Policy,
];

pub(super) fn binding(
    bytes: &[u8],
    limits: Limits,
    work: &mut TypeWorkBudget,
) -> Result<(ArtifactPin, ArtifactPin), ReceiptFailure> {
    if bytes.len() > limits.record_bytes {
        return Err(ReceiptFailure::Resource);
    }
    pay(
        work,
        bytes.len().checked_mul(4).ok_or(ReceiptFailure::Resource)?,
    )?;
    let record: Record = serde_json::from_slice(bytes).map_err(|_| ReceiptFailure::Malformed)?;
    if record.version != 1
        || record.target != super::host::NATIVE_TARGET
        || record.environment != environment()
    {
        return Err(ReceiptFailure::Association);
    }
    if record.inputs.len() + record.tools.len() > limits.paths
        || record.commands.len() > 16
        || record.associations.len() != ASSOCIATIONS.len()
    {
        return Err(ReceiptFailure::Resource);
    }
    // Aggregate covers every retained source/header/ABI/object input and the
    // archive, matching production. Tool executables have separate file caps.
    let total = record
        .inputs
        .iter()
        .chain(std::iter::once(&record.archive))
        .try_fold(0u64, |n, input| n.checked_add(input.pin.bytes))
        .ok_or(ReceiptFailure::Resource)?;
    if total > limits.total_bytes as u64 {
        return Err(ReceiptFailure::Resource);
    }
    let mut names = BTreeSet::new();
    for input in record
        .inputs
        .iter()
        .chain(&record.tools)
        .chain(std::iter::once(&record.archive))
    {
        pay(work, input.path.len() + 8)?;
        if !Path::new(&input.path).is_absolute()
            || input.pin.bytes > limits.file_bytes as u64
            || !names.insert(input.path.as_str())
        {
            return Err(ReceiptFailure::Malformed);
        }
    }
    for deps in [&record.helper_dependencies, &record.abi_dependencies] {
        if deps.is_empty() || deps.len() > limits.paths || !deps.windows(2).all(|p| p[0] < p[1]) {
            return Err(ReceiptFailure::Malformed);
        }
        for path in deps {
            pay(work, path.len() + record.inputs.len())?;
            if !record.inputs.iter().any(|i| i.path == *path) {
                return Err(ReceiptFailure::Association);
            }
        }
    }
    if record.commands.len() != 12 || record.tools.len() != 7 {
        return Err(ReceiptFailure::Association);
    }
    let canonical = serde_json::to_vec(&record).map_err(|_| ReceiptFailure::Resource)?;
    if canonical != bytes {
        return Err(ReceiptFailure::Malformed);
    }
    let before = record
        .configuration_before_binding
        .as_ref()
        .ok_or(ReceiptFailure::Association)?
        .into();
    let observed = ArtifactPin::from(&pin(bytes, work)?);
    Ok((before, observed))
}

pub(super) fn matches(
    bytes: &[u8],
    receipt: &ProducerReceipt,
    limits: Limits,
    work: &mut TypeWorkBudget,
) -> Result<(), ReceiptFailure> {
    let (before, observed) = binding(bytes, limits, work)?;
    let record: Record = serde_json::from_slice(bytes).map_err(|_| ReceiptFailure::Malformed)?;
    pay(work, bytes.len())?;
    for (field, value) in ASSOCIATIONS.iter().zip(&record.associations) {
        if receipt.pin(*field) != Some(value.into()) {
            return Err(ReceiptFailure::Association);
        }
    }
    if receipt.pin(ReceiptField::BuildConfiguration)
        != Some(configuration_binding(before, observed, work)?)
    {
        return Err(ReceiptFailure::Association);
    }
    Ok(())
}
pub(super) fn configuration_binding(
    before: ArtifactPin,
    observed: ArtifactPin,
    work: &mut TypeWorkBudget,
) -> Result<ArtifactPin, ReceiptFailure> {
    let mut data = [0u8; 88];
    data[..8].copy_from_slice(b"ASHNAT01");
    data[8..16].copy_from_slice(&before.bytes.to_le_bytes());
    data[16..48].copy_from_slice(&before.sha256);
    data[48..56].copy_from_slice(&observed.bytes.to_le_bytes());
    data[56..].copy_from_slice(&observed.sha256);
    super::checked_receipt::pin(&data, work)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{module::ModuleId, source::SourceFile};
    use std::sync::Arc;
    fn limits() -> Limits {
        Limits {
            file_bytes: 128 * 1024 * 1024,
            total_bytes: 4 * 1024 * 1024,
            output_bytes: 256 * 1024,
            paths: 128,
            record_bytes: 128 * 1024,
            command_seconds: 30,
            work: 2 * 1024 * 1024 * 1024,
        }
    }
    fn genuine() -> (
        crate::core::ValidatedEffectProgram,
        Vec<(ModuleId, Arc<SourceFile>)>,
    ) {
        crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
        )
    }
    fn image(
        program: &crate::core::ValidatedEffectProgram,
        sources: &[(ModuleId, Arc<SourceFile>)],
    ) -> NativeBuildImage {
        super::super::image::encode_checked_preparation(
            program,
            sources,
            super::super::host::NATIVE_TARGET,
            &mut TypeWorkBudget::default(),
        )
        .unwrap()
    }
    #[test]
    fn native_build_abi_uses_actual_checked_originals() {
        let (program, sources) = genuine();
        let image = image(&program, &sources);
        let mut work = TypeWorkBudget::default();
        let assertions = image
            .bridges
            .iter()
            .enumerate()
            .map(|(n, b)| b.plan.c_header_assertion(n, &mut work).unwrap())
            .collect::<Vec<_>>()
            .join("");
        for name in [
            "ash_checked_owner_acquire",
            "ash_checked_owner_release",
            "ash_checked_owner_view",
            "ash_checked_owner_length",
        ] {
            assert!(assertions.contains(name));
        }
        assert!(assertions.contains("void * (*)(size_t, size_t)"));
        assert!(assertions.contains("void (*)(void *)"));
        let cost = work.used();
        for prefix in [0, 7] {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            for (n, b) in image.bridges.iter().enumerate() {
                b.plan.c_header_assertion(n, &mut exact).unwrap();
            }
            assert_eq!(exact.used(), prefix + cost);
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(
                image
                    .bridges
                    .iter()
                    .enumerate()
                    .try_for_each(|(n, b)| b.plan.c_header_assertion(n, &mut short).map(|_| ()))
                    .is_err()
            );
        }
    }
    #[test]
    fn native_build_dependency_parser_refuses_unknown_duplicate_and_short_work() {
        let input = b"ash-native: /source/helper.c /include/owner.h \\\n /usr/include/stddef.h\n";
        let mut measured = TypeWorkBudget::default();
        let expected = dependencies(input, limits(), &mut measured).unwrap();
        assert_eq!(expected.len(), 3);
        let cost = measured.used();
        for bad in [
            b"other: /source/a".as_slice(),
            b"ash-native: relative.h",
            b"ash-native: /a /a",
            b"ash-native: /escaped\\ path.h",
            b"ash-native:",
        ] {
            assert!(dependencies(bad, limits(), &mut TypeWorkBudget::default()).is_err());
        }
        for prefix in [0, 7] {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            assert_eq!(dependencies(input, limits(), &mut exact).unwrap(), expected);
            assert_eq!(exact.used(), prefix + cost);
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                dependencies(input, limits(), &mut short),
                Err(ReceiptFailure::Resource)
            );
            assert!(dependencies(input, limits(), &mut short).is_err());
            let mut fresh = TypeWorkBudget::with_limit(cost);
            assert_eq!(dependencies(input, limits(), &mut fresh).unwrap(), expected);
        }
    }
    #[test]
    fn native_build_command_capture_and_cleanup_are_bounded() {
        let dir = fixture();
        let mut small = limits();
        small.output_bytes = 1024;
        small.command_seconds = 1;
        let (_, output) = run(
            &dir,
            Path::new("/usr/bin/printf"),
            &["canonical".into()],
            small,
            &mut TypeWorkBudget::with_limit(small.work),
            0,
        )
        .unwrap();
        assert_eq!(output, b"canonical");
        assert!(matches!(
            run(
                &dir,
                Path::new("/usr/bin/yes"),
                &["bounded-output".into()],
                small,
                &mut TypeWorkBudget::with_limit(small.work),
                1
            ),
            Err(ReceiptFailure::Resource)
        ));
        assert_eq!(
            fs::metadata(dir.join("command-1.stdout")).unwrap().len(),
            small.output_bytes as u64
        );
        assert!(
            run(
                &dir,
                Path::new("/usr/bin/sleep"),
                &["10".into()],
                small,
                &mut TypeWorkBudget::with_limit(small.work),
                2
            )
            .is_err()
        );
        // Repeated injected state-probe errors still force TERM/KILL + wait.
        let mut command = Command::new("/usr/bin/sleep");
        command.arg("10");
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }
        let child = command.spawn().unwrap();
        let mut owned = OwnedCommand {
            group: child.id(),
            child,
            settled: false,
        };
        assert_eq!(
            owned.finish_with_probe(false, |_| Err(ReceiptFailure::Input)),
            Err(ReceiptFailure::Input)
        );
        assert!(!owned.settled);
        assert!(owned.child.try_wait().unwrap().is_some());
        assert!(!owned.signal("-0").unwrap());
        for n in 0..3 {
            let value: serde_json::Value = serde_json::from_slice(
                &fs::read(dir.join(format!("command-{n}.lifecycle.json"))).unwrap(),
            )
            .unwrap();
            assert_eq!(value["child_reaped"], true);
            assert_eq!(value["owned_group_empty"], true);
        }
    }
    fn fixture() -> PathBuf {
        let target =
            PathBuf::from(std::env::var_os("CARGO_TARGET_DIR").expect("explicit shared target"));
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = target.join(format!(
            "checked-native-build-{}-{nonce}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&dir).unwrap();
        fs::write(
            dir.join("owner.c"),
            include_bytes!("../../tests/fixtures/checked-owner-runtime/owner.c"),
        )
        .unwrap();
        fs::write(
            dir.join("owner.h"),
            include_bytes!("../../tests/fixtures/checked-owner-runtime/owner.h"),
        )
        .unwrap();
        dir
    }
    #[test]
    #[ignore = "explicit compile/query-only slot; no helper or output execution"]
    fn native_build_actual_helper_header_abi_and_changed_input_refusals() {
        let (program, sources) = genuine();
        let image = image(&program, &sources);
        let dir = fixture();
        let mut build = NativeBuild::build(
            &image,
            Request {
                source: &dir.join("owner.c"),
                header: &dir.join("owner.h"),
                directory: &dir.join("inputs"),
                limits: limits(),
            },
        )
        .unwrap();
        build.verify().unwrap();
        assert!(build.archive().is_file());
        let header = fs::read(dir.join("owner.h")).unwrap();
        fs::write(dir.join("owner.h"), b"/* changed */\n").unwrap();
        assert_eq!(build.verify(), Err(ReceiptFailure::Association));
        fs::write(dir.join("owner.h"), &header).unwrap();
        build.verify().unwrap();
        // The wrong header and its implementation agree with one another, but
        // conflict with the independently admitted bridge's size_t ABI result.
        let bad = fixture();
        let h = fs::read_to_string(bad.join("owner.h")).unwrap().replace(
            "size_t ash_checked_owner_length",
            "int ash_checked_owner_length",
        );
        let c = fs::read_to_string(bad.join("owner.c")).unwrap().replace(
            "size_t ash_checked_owner_length",
            "int ash_checked_owner_length",
        );
        fs::write(bad.join("owner.h"), h).unwrap();
        fs::write(bad.join("owner.c"), c).unwrap();
        assert!(matches!(
            NativeBuild::build(
                &image,
                Request {
                    source: &bad.join("owner.c"),
                    header: &bad.join("owner.h"),
                    directory: &bad.join("inputs"),
                    limits: limits()
                }
            ),
            Err(ReceiptFailure::Input)
        ));
        let stderr = fs::read_dir(bad.join("inputs"))
            .unwrap()
            .flat_map(|p| fs::read_dir(p.unwrap().path()).unwrap())
            .filter_map(Result::ok)
            .filter(|p| p.path().extension().is_some_and(|s| s == "stderr"))
            .map(|p| fs::read_to_string(p.path()).unwrap())
            .collect::<Vec<_>>()
            .join("\n");
        assert!(stderr.contains("prototype"));
        println!(
            "same-build original observations retained at {}",
            dir.display()
        );
    }
    #[test]
    #[ignore = "explicit static compile/link-only slot; generated output never executed"]
    fn native_build_actual_static_receipt_and_independent_provenance() {
        let (program, sources) = genuine();
        let dir = fixture();
        let mut config = super::super::host::BuildConfiguration::new(dir.join("program"));
        config.cargo_target_directory =
            Some(PathBuf::from(std::env::var_os("CARGO_TARGET_DIR").unwrap()));
        config.producer_receipt = Some(super::super::checked_receipt::ProducerReceiptLimits {
            artifact_bytes: 1024 * 1024 * 1024,
            receipt_bytes: 4096,
            records: 64,
            work: 2 * 1024 * 1024 * 1024,
        });
        let policy = crate::foreign::source_runtime::CheckedOwnerLimits {
            groups: 1,
            owners: 1,
            pending: 1,
            observations: 5,
            history: 6,
            continuations: 1,
        };
        let prepared = super::super::host::prepare_checked_native_program(
            &program,
            &sources,
            config,
            policy,
            Request {
                source: &dir.join("owner.c"),
                header: &dir.join("owner.h"),
                directory: &dir.join("inputs"),
                limits: limits(),
            },
        )
        .unwrap();
        let built = super::super::host::build_prepared(prepared).unwrap();
        let receipt = ProducerReceipt::decode(
            &fs::read(built.producer_receipt().unwrap()).unwrap(),
            super::super::checked_receipt::ProducerReceiptLimits {
                artifact_bytes: 1024 * 1024 * 1024,
                receipt_bytes: 4096,
                records: 64,
                work: 2 * 1024 * 1024 * 1024,
            },
        )
        .unwrap();
        let provenance = fs::read(
            built
                .producer_receipt()
                .unwrap()
                .parent()
                .unwrap()
                .join("native-provenance.json"),
        )
        .unwrap();
        matches(
            &provenance,
            &receipt,
            limits(),
            &mut TypeWorkBudget::with_limit(limits().work),
        )
        .unwrap();
        let record: Record = serde_json::from_slice(&provenance).unwrap();
        let total = record
            .inputs
            .iter()
            .chain(std::iter::once(&record.archive))
            .map(|i| i.pin.bytes)
            .sum::<u64>();
        let mut exact = limits();
        exact.total_bytes = total as usize;
        binding(
            &provenance,
            exact,
            &mut TypeWorkBudget::with_limit(exact.work),
        )
        .unwrap();
        let mut short = exact;
        short.total_bytes -= 1;
        assert_eq!(
            binding(
                &provenance,
                short,
                &mut TypeWorkBudget::with_limit(short.work)
            ),
            Err(ReceiptFailure::Resource)
        );
        let mut over: Record = serde_json::from_slice(&provenance).unwrap();
        over.inputs[0].pin.bytes = limits().total_bytes as u64;
        assert_eq!(
            binding(
                &serde_json::to_vec(&over).unwrap(),
                limits(),
                &mut TypeWorkBudget::with_limit(limits().work)
            ),
            Err(ReceiptFailure::Resource)
        );
        let mut measured = TypeWorkBudget::with_limit(limits().work);
        binding(&provenance, limits(), &mut measured).unwrap();
        let cost = measured.used();
        for prefix in [0, 7] {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            binding(&provenance, limits(), &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + cost);
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                binding(&provenance, limits(), &mut short),
                Err(ReceiptFailure::Resource)
            );
            assert!(binding(&provenance, limits(), &mut short).is_err());
            binding(&provenance, limits(), &mut TypeWorkBudget::with_limit(cost)).unwrap();
        }
        for field in [
            ReceiptField::RuntimeClosure,
            ReceiptField::NativeClosure,
            ReceiptField::HeaderClosure,
            ReceiptField::ToolClosure,
            ReceiptField::Premises,
            ReceiptField::Context,
        ] {
            assert_eq!(receipt.pin(field), None)
        }
        assert_eq!(
            receipt.activate(),
            Err(ReceiptFailure::ProtectedAuthorityUnavailable)
        );
        // Keep the exact canonical struct encoding so these mutations reach
        // association checks rather than generic JSON member-order rejection.
        let mut changed: Record = serde_json::from_slice(&provenance).unwrap();
        changed.commands[0].arguments[0] = "-unassociated-config".into();
        assert_eq!(
            matches(
                &serde_json::to_vec(&changed).unwrap(),
                &receipt,
                limits(),
                &mut TypeWorkBudget::with_limit(limits().work)
            ),
            Err(ReceiptFailure::Association)
        );
        let mut changed: Record = serde_json::from_slice(&provenance).unwrap();
        changed.tools[0].pin = changed.tools[1].pin.clone();
        assert_eq!(
            matches(
                &serde_json::to_vec(&changed).unwrap(),
                &receipt,
                limits(),
                &mut TypeWorkBudget::with_limit(limits().work)
            ),
            Err(ReceiptFailure::Association)
        );
        let mut changed: Record = serde_json::from_slice(&provenance).unwrap();
        changed.associations[0].sha256[0] ^= 1;
        assert_eq!(
            matches(
                &serde_json::to_vec(&changed).unwrap(),
                &receipt,
                limits(),
                &mut TypeWorkBudget::with_limit(limits().work)
            ),
            Err(ReceiptFailure::Association)
        );
        let mut changed: Record = serde_json::from_slice(&provenance).unwrap();
        let required = changed.helper_dependencies[0].clone();
        changed.inputs.retain(|i| i.path != required);
        assert_eq!(
            matches(
                &serde_json::to_vec(&changed).unwrap(),
                &receipt,
                limits(),
                &mut TypeWorkBudget::with_limit(limits().work)
            ),
            Err(ReceiptFailure::Association)
        );
        let mut changed: Record = serde_json::from_slice(&provenance).unwrap();
        changed.inputs.push(changed.inputs[0].clone());
        assert_eq!(
            binding(
                &serde_json::to_vec(&changed).unwrap(),
                limits(),
                &mut TypeWorkBudget::with_limit(limits().work)
            ),
            Err(ReceiptFailure::Malformed)
        );
        let mut changed: Record = serde_json::from_slice(&provenance).unwrap();
        changed.version = 2;
        assert_eq!(
            binding(
                &serde_json::to_vec(&changed).unwrap(),
                limits(),
                &mut TypeWorkBudget::with_limit(limits().work)
            ),
            Err(ReceiptFailure::Association)
        );
        let text = std::str::from_utf8(&provenance).unwrap();
        let unknown = format!("{},\"unknown\":1}}", text.strip_suffix('}').unwrap());
        let duplicate = format!("{{\"version\":1,{}", text.strip_prefix('{').unwrap());
        for bytes in [unknown.as_bytes(), duplicate.as_bytes()] {
            assert_eq!(
                binding(
                    bytes,
                    limits(),
                    &mut TypeWorkBudget::with_limit(limits().work)
                ),
                Err(ReceiptFailure::Malformed)
            );
        }
        println!(
            "same-build static original observations retained at {}",
            dir.display()
        );
    }
}
