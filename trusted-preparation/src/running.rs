//! Running-image ingress object checks. These observations alone grant nothing.
use crate::{Budget, Refusal, io, linux};
use std::{ffi::CString, fs::File, io::Read, os::fd::AsRawFd, os::unix::fs::{FileTypeExt, MetadataExt}};

const FDINFO_BYTES: usize = 4096;
const PIPEFS: i64 = 0x50495045;
const READER_FLAGS: u64 = 0x80000 | 0x800; // parent CLOEXEC, read-only/nonblocking

#[derive(Debug, Eq, PartialEq)]
struct FdInfo { position: u64, flags: u64, mount: u64, inode: u64 }

fn number(raw: &str, radix: u32) -> Result<u64, Refusal> {
    if raw.is_empty() || !raw.bytes().all(|b| match radix {
        8 => (b'0'..=b'7').contains(&b),
        _ => b.is_ascii_digit(),
    }) { return Err(Refusal::Malformed); }
    u64::from_str_radix(raw, radix).map_err(|_| Refusal::Malformed)
}
fn fdinfo(raw: &[u8], budget: &mut Budget) -> Result<FdInfo, Refusal> {
    if raw.len() > FDINFO_BYTES { return Err(Refusal::Resource); }
    budget.pay(raw.len())?;
    let text = std::str::from_utf8(raw).map_err(|_| Refusal::Malformed)?;
    let (mut position, mut flags, mut mount, mut inode) = (None, None, None, None);
    for line in text.lines() {
        let (key, value) = line.split_once(':').ok_or(Refusal::Malformed)?;
        let (slot, radix) = match key {
            "pos" => (&mut position, 10), "flags" => (&mut flags, 8),
            "mnt_id" => (&mut mount, 10), "ino" => (&mut inode, 10),
            _ => return Err(Refusal::Malformed),
        };
        if slot.is_some() { return Err(Refusal::Malformed); }
        *slot = Some(number(value.trim(), radix)?);
    }
    Ok(FdInfo { position: position.ok_or(Refusal::Malformed)?, flags: flags.ok_or(Refusal::Malformed)?,
        mount: mount.ok_or(Refusal::Malformed)?, inode: inode.ok_or(Refusal::Malformed)? })
}
fn read_info(parent: &File, budget: &mut Budget) -> Result<FdInfo, Refusal> {
    let directory = linux::proc_child(parent, c"fdinfo", true)?;
    let mut file = linux::proc_child(&directory, c"3", false)?;
    // Fixed stack storage; charge the bounded read before kernel writes it.
    budget.pay(FDINFO_BYTES + 1)?;
    let mut bytes = [0; FDINFO_BYTES + 1];
    let mut count = 0;
    while count < bytes.len() {
        let n = io(file.read(&mut bytes[count..]))?;
        if n == 0 { break; }
        count += n;
    }
    fdinfo(&bytes[..count], budget)
}
fn pipe(file: &File) -> Result<(u64, u64), Refusal> {
    linux::filesystem(file, PIPEFS)?;
    let metadata = io(file.metadata())?;
    if !metadata.file_type().is_fifo() { return Err(Refusal::Context); }
    Ok((metadata.dev(), metadata.ino()))
}

/// Pinned actual parent and pipe observations, never a provider/admission token.
/// The authenticated fixed launcher must retain its reader unchanged until reap.
pub(crate) struct ParentPipe {
    pid: i32,
    pidfd: File,
    parent: File,
    parent_identity: (u64, u64),
    writer: File,
    identity: (u64, u64),
    before: FdInfo,
}
impl ParentPipe {
    pub(crate) fn inspect(budget: &mut Budget) -> Result<Self, Refusal> {
        // The running bootstrap already performed the exact inherited census
        // before opening its config/store handles. These temporaries are ours.
        if linux::role_flags(3)? != (0x801, 0) { return Err(Refusal::Context); }
        let writer = linux::duplicate_role(3)?;
        let identity = pipe(&writer)?;
        let pid = linux::parent_pid()?;
        let pidfd = linux::pidfd(pid)?;
        linux::require_live(&pidfd)?;
        let proc = io(File::open("/proc"))?;
        linux::filesystem(&proc, 0x9fa0)?;
        budget.pay(64)?; // bounded i32 decimal name and CString storage
        let name = CString::new(pid.to_string()).map_err(|_| Refusal::Malformed)?;
        let parent = linux::proc_child(&proc, &name, true)?;
        let metadata = io(parent.metadata())?;
        let before = read_info(&parent, budget)?;
        let result = Self { pid, pidfd, parent, parent_identity: (metadata.dev(), metadata.ino()),
            writer, identity, before };
        result.recheck(budget)?;
        Ok(result)
    }
    /// Used only by the fixed launcher-executable/context verifier.
    pub(crate) fn parent(&self) -> &File { &self.parent }
    pub(crate) fn into_writer(self) -> File { self.writer }
    pub(crate) fn recheck(&self, budget: &mut Budget) -> Result<(), Refusal> {
        linux::require_live(&self.pidfd)?;
        if linux::parent_pid()? != self.pid { return Err(Refusal::Context); }
        let metadata = io(self.parent.metadata())?;
        if (metadata.dev(), metadata.ino()) != self.parent_identity { return Err(Refusal::Context); }
        let descriptors = linux::proc_child(&self.parent, c"fd", true)?;
        let reader_path = linux::proc_magic(&descriptors, c"3", true)?;
        if pipe(&reader_path)? != self.identity || pipe(&self.writer)? != self.identity
            || linux::role_flags(3)? != (0x801, 0)
            || linux::role_flags(self.writer.as_raw_fd())? != (0x801, 1) {
            return Err(Refusal::Context);
        }
        let after = read_info(&self.parent, budget)?;
        if after != self.before || after.position != 0 || after.flags != READER_FLAGS
            || after.inode != self.identity.1 { return Err(Refusal::Context); }
        linux::require_live(&self.pidfd)?;
        if linux::parent_pid()? != self.pid { return Err(Refusal::Context); }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const GOOD: &[u8] = b"pos:\t0\nflags:\t02004000\nmnt_id:\t17\nino:\t2048\n";
    #[test]
    fn reader_fdinfo_is_bounded_exact_kernel_data() {
        let result = fdinfo(GOOD, &mut Budget::new(GOOD.len())).unwrap();
        assert_eq!(result, FdInfo { position: 0, flags: READER_FLAGS, mount: 17, inode: 2048 });
        assert_eq!(fdinfo(GOOD, &mut Budget::new(GOOD.len() - 1)), Err(Refusal::Resource));
        for raw in [b"flags: 02004000\nflags: 02004000\n".as_slice(),
            b"pos:0\nflags:8\nmnt_id:17\nino:2048\n",
            b"pos:0\nflags:02004000\nmnt_id:17\nino:18446744073709551616\n",
            b"pos:0\nflags:02004000\nmnt_id:17\nino:2048\nextra:1\n"] {
            assert_eq!(fdinfo(raw, &mut Budget::new(raw.len())), Err(Refusal::Malformed));
        }
    }
}
