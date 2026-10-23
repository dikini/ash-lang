//! Small Linux x86-64 GNU syscall boundary; no exec interface is declared.
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
