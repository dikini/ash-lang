//! Fixed Linux x86-64 GNU syscall boundary; execution helpers are crate-private.
use crate::{Refusal, io};
use std::{
    ffi::{c_char, c_int, c_long, c_void},
    fs::File,
    os::fd::{AsRawFd, FromRawFd},
};
unsafe extern "C" {
    fn memfd_create(name: *const c_char, flags: u32) -> c_int;
    fn fcntl(fd: c_int, cmd: c_int, ...) -> c_int;
    fn openat(dir: c_int, path: *const c_char, flags: c_int, ...) -> c_int;
    fn fgetxattr(fd: c_int, name: *const c_char, value: *mut c_void, size: usize) -> isize;
    fn fstatfs(fd: c_int, buf: *mut c_void) -> c_int;
    fn getresuid(real: *mut u32, effective: *mut u32, saved: *mut u32) -> c_int;
    fn getresgid(real: *mut u32, effective: *mut u32, saved: *mut u32) -> c_int;
    fn syscall(number: c_long, ...) -> c_long;
}
pub(crate) fn memfd() -> Result<File, Refusal> {
    // SAFETY: NUL-terminated literal; flags CLOEXEC|ALLOW_SEALING|EXEC are the
    // explicit supported Linux executable-memfd policy. No candidate executes.
    let fd = unsafe { memfd_create(c"ash-checked-preparation".as_ptr(), 19) };
    owned(fd)
}
fn owned(fd: c_int) -> Result<File, Refusal> {
    if fd < 0 {
        return Err(Refusal::Input);
    }
    // SAFETY: Every successful syscall here returns a fresh owned descriptor;
    // exactly this File takes ownership, closing it on every later failure.
    Ok(unsafe { File::from_raw_fd(fd) })
}
pub(crate) fn seal(file: &File) -> Result<(), Refusal> {
    // SAFETY: fcntl consumes an integer bitmask, not a pointer; fd is live.
    if unsafe { fcntl(file.as_raw_fd(), 1033, 15) } < 0 {
        return Err(Refusal::Input);
    }
    if seals(file)? != 15 {
        return Err(Refusal::Association);
    }
    Ok(())
}
pub(crate) fn seals(file: &File) -> Result<i32, Refusal> {
    // SAFETY: F_GET_SEALS takes no optional argument and file owns the live fd.
    let n = unsafe { fcntl(file.as_raw_fd(), 1034) };
    if n < 0 { Err(Refusal::Input) } else { Ok(n) }
}
pub(crate) fn open_child(
    dir: &File,
    name: &std::ffi::CStr,
    directory: bool,
) -> Result<File, Refusal> {
    let flags = 0x80000 | 0x20000 | 0x800 | if directory { 0x10000 } else { 0 };
    // SAFETY: Owned live directory and NUL-terminated single-component name;
    // O_NOFOLLOW, read-only, nonblocking/CLOEXEC prevent link/open-type traps.
    let fd = unsafe { openat(dir.as_raw_fd(), name.as_ptr(), flags) };
    owned(fd)
}
pub(crate) fn no_acl(file: &File) -> Result<(), Refusal> {
    for name in [c"system.posix_acl_access", c"system.posix_acl_default"] {
        // SAFETY: size0/null is the documented xattr length query. We reject any
        // present ACL and accept only kernel ENODATA, never unknown failures.
        let n = unsafe { fgetxattr(file.as_raw_fd(), name.as_ptr(), std::ptr::null_mut(), 0) };
        if n >= 0 || std::io::Error::last_os_error().raw_os_error() != Some(61) {
            return Err(Refusal::Context);
        }
    }
    Ok(())
}
pub(crate) fn filesystem(file: &File, expected: i64) -> Result<(), Refusal> {
    // Linux x86-64 statfs is120B aligned8; reserve256 aligned bytes, inspect only
    // initialized f_type. This module is cfg-limited to that exact ABI.
    let mut words = [0u64; 32];
    // SAFETY: Correctly aligned writable buffer exceeds supported ABI struct;
    // kernel/libc writes its fixed struct and file owns a valid fd.
    if unsafe { fstatfs(file.as_raw_fd(), words.as_mut_ptr().cast()) } < 0 {
        return Err(Refusal::Input);
    }
    if words[0] as i64 != expected {
        return Err(Refusal::Context);
    }
    Ok(())
}
pub(crate) fn credentials() -> Result<([u32; 3], [u32; 3]), Refusal> {
    let (mut r, mut e, mut s) = (0, 0, 0);
    let (mut gr, mut ge, mut gs) = (0, 0, 0);
    // SAFETY: Distinct valid u32 pointers match Linux GNU uid_t/gid_t; no change
    // to credentials, privilege, namespace or process state is performed.
    if unsafe { getresuid(&mut r, &mut e, &mut s) } < 0 {
        return Err(Refusal::Input);
    }
    // SAFETY: Same initialized, distinct writable gid_t pointers as above.
    if unsafe { getresgid(&mut gr, &mut ge, &mut gs) } < 0 {
        return Err(Refusal::Input);
    }
    Ok(([r, e, s], [gr, ge, gs]))
}
pub(crate) fn inherited_fds() -> Result<(), Refusal> {
    inherited_fds_for(&[0, 1, 2])
}
pub(crate) fn inherited_fds_for(allowed: &[i32]) -> Result<(), Refusal> {
    let directory = io(File::open("/proc/thread-self/fd"))?;
    filesystem(&directory, 0x9fa0)?;
    let mut buffer = [0u8; 8192];
    let mut total = 0usize;
    loop {
        // SAFETY: SYS_getdents64=217 on this cfg ABI, valid directory fd and
        // writable bounded byte buffer. Returned records are parsed below.
        let count = unsafe {
            syscall(
                217,
                directory.as_raw_fd(),
                buffer.as_mut_ptr(),
                buffer.len(),
            )
        };
        if count < 0 {
            return Err(Refusal::Input);
        }
        if count == 0 {
            break;
        }
        let n = usize::try_from(count).map_err(|_| Refusal::Resource)?;
        if n > buffer.len() {
            return Err(Refusal::Malformed);
        }
        let mut at = 0;
        while at < n {
            total += 1;
            if total > 256 || n - at < 20 {
                return Err(Refusal::Resource);
            }
            let len = u16::from_ne_bytes([buffer[at + 16], buffer[at + 17]]) as usize;
            if len < 20 || len > n - at {
                return Err(Refusal::Malformed);
            }
            let raw = &buffer[at + 19..at + len];
            let end = raw.iter().position(|b| *b == 0).ok_or(Refusal::Malformed)?;
            let name = std::str::from_utf8(&raw[..end]).map_err(|_| Refusal::Malformed)?;
            if name != "." && name != ".." {
                let fd: i32 = name.parse().map_err(|_| Refusal::Malformed)?;
                if !allowed.contains(&fd) && fd != directory.as_raw_fd() {
                    return Err(Refusal::Context);
                }
            }
            at += len;
        }
    }
    Ok(())
}

/// Kernel procfs handle for the calling thread, never the group leader.
pub(crate) fn calling_thread_proc() -> Result<File, Refusal> {
    let file = io(File::open("/proc/thread-self"))?;
    filesystem(&file, 0x9fa0)?;
    Ok(file)
}
pub(crate) fn proc_child(
    dir: &File,
    name: &std::ffi::CStr,
    directory: bool,
) -> Result<File, Refusal> {
    let file = open_child(dir, name, directory)?;
    filesystem(&file, 0x9fa0)?;
    Ok(file)
}
pub(crate) fn namespace(dir: &File, name: &std::ffi::CStr) -> Result<File, Refusal> {
    // SAFETY: Only fixed kernel nsfs magic links beneath an already verified
    // thread proc/ns directory are passed; the resulting object must be nsfs.
    let fd = unsafe { openat(dir.as_raw_fd(), name.as_ptr(), 0x80000 | 0x800) };
    let file = owned(fd)?;
    filesystem(&file, 0x6e736673)?;
    Ok(file)
}
pub(crate) fn standard_fds() -> Result<(), Refusal> {
    use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt};
    let canonical = io(std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(0x80000 | 0x20000 | 0x800)
        .open("/dev/null"))?;
    let expected = io(canonical.metadata())?;
    if !expected.file_type().is_char_device() || expected.rdev() != 0x103 || expected.uid() != 0 {
        return Err(Refusal::Context);
    }
    for original in 0..3 {
        // SAFETY: F_DUPFD_CLOEXEC creates a new owned descriptor; it never takes
        // ownership of or closes the standard slot. File closes the duplicate.
        let copied = owned(unsafe { fcntl(original, 1030, 3) })?;
        let meta = io(copied.metadata())?;
        // Linux's fixed /dev/null major1/minor3 is the only supported endpoint.
        if !meta.file_type().is_char_device()
            || meta.rdev() != 0x103
            || (meta.dev(), meta.ino()) != (expected.dev(), expected.ino())
        {
            return Err(Refusal::Context);
        }
        // SAFETY: F_GETFL takes no argument; duplicate shares the actual open
        // file description/access flags of the original descriptor.
        let flags = unsafe { fcntl(copied.as_raw_fd(), 3) };
        if flags < 0 {
            return Err(Refusal::Input);
        }
        if flags & 0x200000 != 0 {
            return Err(Refusal::Context);
        }
        if flags & 3 != if original == 0 { 0 } else { 1 } {
            return Err(Refusal::Context);
        }
    }
    Ok(())
}
/// Duplicate a fixed inherited DATA role without taking ownership of its slot.
pub(crate) fn duplicate_role(fd: i32) -> Result<File, Refusal> {
    // SAFETY: F_DUPFD_CLOEXEC returns a fresh descriptor; no pointer argument.
    owned(unsafe { fcntl(fd, 1030, 5) })
}
pub(crate) fn close_role(fd: i32) -> Result<(), Refusal> {
    // SAFETY: SYS_close=3; only the verified fixed ingress roles are passed.
    // Linux releases the descriptor even on EINTR: never retry a reused number.
    if unsafe { syscall(3, fd) } != 0 { return Err(Refusal::Input); }
    Ok(())
}
pub(crate) fn role_flags(fd: i32) -> Result<(i32, i32), Refusal> {
    // SAFETY: F_GETFL/F_GETFD only inspect this descriptor; no pointer argument.
    let status = unsafe { fcntl(fd, 3) };
    // SAFETY: Same integer-only descriptor query as above.
    let descriptor = unsafe { fcntl(fd, 1) };
    if status < 0 || descriptor < 0 { return Err(Refusal::Input); }
    Ok((status, descriptor))
}
pub(crate) fn parent_pid() -> Result<i32, Refusal> {
    // SAFETY: SYS_getppid=110 on the cfg-limited Linux x86-64 ABI; no arguments.
    let pid = unsafe { syscall(110) };
    let pid = i32::try_from(pid).map_err(|_| Refusal::Context)?;
    if pid <= 1 { return Err(Refusal::Context); }
    Ok(pid)
}
pub(crate) fn pidfd(pid: i32) -> Result<File, Refusal> {
    // SAFETY: SYS_pidfd_open=434 on this ABI, fixed flags0, no pointer arguments.
    let fd = unsafe { syscall(434, pid, 0u32) };
    owned(i32::try_from(fd).map_err(|_| Refusal::Input)?)
}
pub(crate) fn require_live(pidfd: &File) -> Result<(), Refusal> {
    #[repr(C)]
    struct PollFd { fd: i32, events: i16, revents: i16 }
    let mut descriptor = PollFd { fd: pidfd.as_raw_fd(), events: 1, revents: 0 };
    // SAFETY: SYS_poll=7, valid writable one-element Linux pollfd and timeout0.
    let result = unsafe { syscall(7, &mut descriptor as *mut PollFd, 1usize, 0i32) };
    if result < 0 { return Err(Refusal::Input); }
    if result != 0 || descriptor.revents != 0 { return Err(Refusal::Context); }
    Ok(())
}
/// Follow only a caller-selected fixed kernel magic link below verified procfs.
pub(crate) fn proc_magic(dir: &File, name: &std::ffi::CStr, path_only: bool) -> Result<File, Refusal> {
    // SAFETY: The only callers supply fixed exe or fd/3 under pinned procfs.
    // O_PATH is mandatory for the peer pipe, so this never opens a pipe reader.
    let flags = 0x80000 | if path_only { 0x200000 } else { 0x800 };
    owned(unsafe { openat(dir.as_raw_fd(), name.as_ptr(), flags) })
}

/// Inspect only the fixed launcher ingress slot. A closed slot is not authority.
pub(crate) fn role_absent(fd: i32) -> Result<bool, Refusal> {
    // SAFETY: F_GETFD takes no pointer; only a fixed role is queried.
    let result = unsafe { fcntl(fd, 1) };
    if result >= 0 { return Ok(false); }
    if std::io::Error::last_os_error().raw_os_error() == Some(9) { Ok(true) }
    else { Err(Refusal::Input) }
}
pub(crate) fn seals_or_regular(file: &File) -> Result<Option<i32>, Refusal> {
    // SAFETY: F_GET_SEALS is an integer-only inspection of the owned executable.
    let result = unsafe { fcntl(file.as_raw_fd(), 1034) };
    if result >= 0 { return Ok(Some(result)); }
    if std::io::Error::last_os_error().raw_os_error() == Some(22) { Ok(None) }
    else { Err(Refusal::Input) }
}
pub(crate) fn high(file: File) -> Result<File, Refusal> { duplicate_high(&file) }
pub(crate) fn duplicate_high(file: &File) -> Result<File, Refusal> {
    // SAFETY: Fresh CLOEXEC duplicate above all fixed ingress roles.
    owned(unsafe { fcntl(file.as_raw_fd(), 1030, 10) })
}
pub(crate) fn readonly(file: &File) -> Result<File, Refusal> {
    let proc = calling_thread_proc()?;
    let directory = proc_child(&proc, c"fd", true)?;
    // Fixed i32 descriptor rendering into stack storage, no caller path input.
    let mut name = [0u8; 12]; let mut at = 10; let mut value = file.as_raw_fd() as u32;
    loop { name[at] = b'0' + (value % 10) as u8; value /= 10;
        if value == 0 { break; } at -= 1; }
    let name = std::ffi::CStr::from_bytes_with_nul(&name[at..12]).map_err(|_|Refusal::Malformed)?;
    // SAFETY: Fixed decimal live descriptor under this verified procfs fd
    // directory; open read-only/CLOEXEC without the pipe helper's NONBLOCK bit.
    owned(unsafe { openat(directory.as_raw_fd(), name.as_ptr(), 0x80000) })
}
pub(crate) fn report_pipe() -> Result<(File, File), Refusal> {
    let mut slots = [-1; 2];
    // SAFETY: SYS_pipe2=293 writes two descriptors to the valid array.
    if unsafe { syscall(293, slots.as_mut_ptr(), 0x80000 | 0x800) } != 0 { return Err(Refusal::Input); }
    let reader = owned(slots[0])?; let writer = owned(slots[1])?;
    Ok((duplicate_high(&reader)?, duplicate_high(&writer)?))
}
/// Called in an ordinary single-threaded process, never a post-fork Rust path.
pub(crate) fn occupy_reader(file: &File) -> Result<File, Refusal> {
    if !role_absent(3)? { return Err(Refusal::Context); }
    // SAFETY: dup3 atomically installs this owned reader at the pre-vacant role.
    // Its CLOEXEC bit keeps it out of the child; the parent holds it until reap.
    if unsafe { syscall(292, file.as_raw_fd(), 3, 0x80000) } != 3 { return Err(Refusal::Input); }
    // SAFETY: Only this File owns the newly installed fixed reader descriptor.
    Ok(unsafe { File::from_raw_fd(3) })
}
fn fd_exec_error(file: &File, root: bool, sink: Option<&std::ffi::CStr>) -> std::io::Error {
    let name = if root { c"ash-checked-owner-root-v2" } else { c"ash-checked-launcher-v2" };
    let argv = [name.as_ptr(), sink.map_or(std::ptr::null(), |s| s.as_ptr()), std::ptr::null()];
    let env: [*const c_char; 1] = [std::ptr::null()];
    // SAFETY: SYS_execveat=322 with AT_EMPTY_PATH executes the actual owned FD.
    // All pointer arrays and literals live until syscall replacement/return.
    unsafe { syscall(322, file.as_raw_fd(), c"".as_ptr(), argv.as_ptr(), env.as_ptr(), 0x1000) };
    std::io::Error::last_os_error()
}
pub(crate) fn exec_fixed(file: &File, root: bool, sink: Option<&std::ffi::CStr>) -> Result<std::convert::Infallible, Refusal> {
    let _error = fd_exec_error(file, root, sink);
    Err(Refusal::Input)
}
/// std::process owns fork/error-pipe/reaping. The child hook contains only fixed
/// dup3/execveat syscalls and errno capture; it never allocates or returns Ok.
pub(crate) fn spawn_launcher(executable: &File, writer: &File, request: &File, image: &File)
    -> Result<std::process::Child, Refusal> {
    use std::os::unix::process::CommandExt;
    let exe = duplicate_high(executable)?;
    let sources = [duplicate_high(writer)?, duplicate_high(request)?, duplicate_high(image)?];
    let mut command = std::process::Command::new("/ash-no-path-exec-fallback");
    command.env_clear();
    // SAFETY: Every captured source is owned, immutable and above roles3..5.
    // The hook performs only async-signal-safe syscalls; every return is Err,
    // so Command can never fall through to its sentinel pathname exec.
    unsafe { command.pre_exec(move || {
        for (source, target) in sources.iter().zip([3, 4, 5]) {
            if syscall(292, source.as_raw_fd(), target, 0) != target as c_long {
                return Err(std::io::Error::last_os_error());
            }
        }
        Err(fd_exec_error(&exe, false, None))
    }); }
    io(command.spawn())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    #[ignore = "isolated null-only standard-descriptor predicate; no bootstrap authority"]
    fn standard_fd_probe() {
        let expected = std::env::var("ASH_STDIO_DATA_PROBE").unwrap();
        match expected.as_str() {
            "null" => assert_eq!(standard_fds(), Ok(())),
            "substituted" => assert_eq!(standard_fds(), Err(Refusal::Context)),
            _ => panic!("unknown probe"),
        }
    }
    #[test]
    fn readonly_image_and_high_management_handles_preserve_exact_flags() {
        use std::io::Write;
        let directory = crate::test_directory("readonly-image");
        let path = directory.join("data");
        let mut original = std::fs::OpenOptions::new().read(true).write(true).create_new(true).open(&path).unwrap();
        original.write_all(b"not executable DATA").unwrap();
        let high = high(original).unwrap();
        assert!(high.as_raw_fd() >= 10);
        let readonly = readonly(&high).unwrap();
        let (flags, descriptor) = role_flags(readonly.as_raw_fd()).unwrap();
        assert_eq!(flags & !0x8000, 0);
        assert_eq!(descriptor, 1);
        use std::os::unix::fs::MetadataExt;
        let before = high.metadata().unwrap(); let after = readonly.metadata().unwrap();
        assert_eq!((before.dev(), before.ino(), before.len()), (after.dev(), after.ino(), after.len()));
        drop(readonly); drop(high); std::fs::remove_dir_all(directory).unwrap();
    }
    #[test]
    fn fresh_report_pipe_has_fixed_direction_flags_and_high_owned_endpoints() {
        let (reader, writer) = report_pipe().unwrap();
        assert!(reader.as_raw_fd() >= 10 && writer.as_raw_fd() >= 10);
        assert_eq!(role_flags(reader.as_raw_fd()).unwrap(), (0x800,1));
        assert_eq!(role_flags(writer.as_raw_fd()).unwrap(), (0x801,1));
        use std::os::unix::fs::{FileTypeExt, MetadataExt};
        let a = reader.metadata().unwrap(); let b = writer.metadata().unwrap();
        assert!(a.file_type().is_fifo() && b.file_type().is_fifo());
        assert_eq!((a.dev(),a.ino()),(b.dev(),b.ino()));
        filesystem(&reader, 0x50495045).unwrap();
    }
    #[test]
    fn calling_thread_proc_namespace_and_acl_checks_are_kernel_data_only() {
        std::thread::spawn(|| {
            use std::io::Read;
            let proc = calling_thread_proc().unwrap();
            let ns = proc_child(&proc, c"ns", true).unwrap();
            namespace(&ns, c"user").unwrap();
            namespace(&ns, c"mnt").unwrap();
            let mut status = proc_child(&proc, c"status", false).unwrap();
            let mut text = String::new();
            status.read_to_string(&mut text).unwrap();
            let pid = text
                .lines()
                .find_map(|line| line.strip_prefix("Pid:"))
                .unwrap()
                .trim()
                .parse::<u32>()
                .unwrap();
            assert_ne!(
                pid,
                std::process::id(),
                "test explicitly runs in a nonleader thread"
            );
            let credentials = credentials().unwrap();
            assert_eq!(credentials.0[0], credentials.0[1]);
            let directory = crate::test_directory("acl-data");
            let path = directory.join("file");
            std::fs::write(&path, b"data").unwrap();
            let file = File::open(&path).unwrap();
            no_acl(&file).unwrap();
            assert_eq!(filesystem(&file, 0x9fa0), Err(Refusal::Context));
            std::fs::remove_dir_all(directory).unwrap();
        })
        .join()
        .unwrap();
    }
    #[test]
    fn standard_slots_null_then_regular_substitutions_are_not_authority() {
        use std::os::unix::fs::OpenOptionsExt;
        use std::process::{Command, Stdio};
        let binary = std::env::current_exe().unwrap();
        let directory = crate::test_directory("standard-slots");
        let run = |slot: Option<usize>, variant: &str| {
            let mut command = Command::new(&binary);
            command
                .args(["--exact", "linux::tests::standard_fd_probe", "--ignored"])
                .env(
                    "ASH_STDIO_DATA_PROBE",
                    if slot.is_none() {
                        "null"
                    } else {
                        "substituted"
                    },
                )
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null());
            let path = directory.join(format!("slot-{}-{variant}", slot.unwrap_or(3)));
            if let Some(slot) = slot {
                let file = match variant {
                    "regular" => std::fs::OpenOptions::new()
                        .read(true)
                        .write(true)
                        .create_new(true)
                        .open(&path)
                        .unwrap(),
                    "wrong-access" => std::fs::OpenOptions::new()
                        .write(true)
                        .open("/dev/null")
                        .unwrap(),
                    "opath" => std::fs::OpenOptions::new()
                        .read(true)
                        .custom_flags(0x200000)
                        .open("/dev/null")
                        .unwrap(),
                    _ => panic!("unknown data substitution"),
                };
                match slot {
                    0 => {
                        command.stdin(file);
                    }
                    1 => {
                        command.stdout(file);
                    }
                    _ => {
                        command.stderr(file);
                    }
                }
            }
            let status = command.status().unwrap();
            if slot.is_some() && variant == "regular" {
                std::fs::remove_file(path).unwrap();
            }
            assert!(status.success());
        };
        run(None, "null");
        for slot in 0..3 {
            run(Some(slot), "regular");
        }
        run(Some(0), "wrong-access");
        run(Some(0), "opath");
        std::fs::remove_dir_all(directory).unwrap();
    }
}
