use crate::{Budget, Refusal, io, linux};
use ash::build::ArtifactPin;
use sha2::{Digest, Sha256};
use std::{
    fs::File,
    io::{Read, Seek, SeekFrom, Write},
    os::unix::fs::{MetadataExt, PermissionsExt},
};
/// Separate finite copy/hash/ELF inspection policy; it is never approval.
#[derive(Clone, Copy, Debug)]
pub struct PreparationLimits {
    /// Maximum source and sealed-image bytes.
    pub image_bytes: usize,
    /// Combined paid copy, hash and inspection work.
    pub work: usize,
    /// Maximum ELF program headers inspected.
    pub program_headers: usize,
}
/// Owned immutable copied bytes. This type has no protected applicability and no
/// execute method. Its descriptor closes on every error/drop.
#[derive(Debug)]
pub struct SealedData {
    file: File,
    pin: ArtifactPin,
}
impl SealedData {
    /// Copy from this already opened regular object once; apply all four seals,
    /// then hash/strictly inspect the SAME owned sealed descriptor. Replacing a
    /// source pathname cannot redirect this operation. Concurrent byte mutation
    /// can only yield the exact expected final digest or refusal.
    pub fn copy(
        source: &mut File,
        expected: ArtifactPin,
        limits: PreparationLimits,
    ) -> Result<Self, Refusal> {
        Self::copy_metered(source, expected, limits, &mut Budget::new(limits.work))
    }
    fn copy_metered(
        source: &mut File,
        expected: ArtifactPin,
        limits: PreparationLimits,
        budget: &mut Budget,
    ) -> Result<Self, Refusal> {
        if limits.work == 0
            || limits.work > 16 * 1024 * 1024 * 1024
            || limits.image_bytes == 0
            || limits.image_bytes > 2usize.pow(31)
            || limits.program_headers == 0
            || limits.program_headers > 4096
        {
            return Err(Refusal::Resource);
        }
        let before = io(source.metadata())?;
        if !before.is_file()
            || before.len() != expected.bytes
            || expected.bytes > limits.image_bytes as u64
        {
            return Err(Refusal::Association);
        }
        io(source.seek(SeekFrom::Start(0)))?;
        let mut file = linux::memfd()?;
        io(file.set_permissions(std::fs::Permissions::from_mode(0o500)))?;
        let mut buffer = [0u8; 65536];
        let mut remaining = expected.bytes;
        while remaining > 0 {
            let count = usize::try_from(remaining.min(buffer.len() as u64))
                .map_err(|_| Refusal::Resource)?;
            budget.pay(count.checked_mul(2).ok_or(Refusal::Resource)?)?;
            io(source.read_exact(&mut buffer[..count]))?;
            io(file.write_all(&buffer[..count]))?;
            remaining -= count as u64;
        }
        budget.pay(1)?;
        let mut extra = [0u8; 1];
        if io(source.read(&mut extra))? != 0 {
            return Err(Refusal::Association);
        }
        let after = io(source.metadata())?;
        if (
            before.dev(),
            before.ino(),
            before.len(),
            before.mtime(),
            before.mtime_nsec(),
            before.ctime(),
            before.ctime_nsec(),
        ) != (
            after.dev(),
            after.ino(),
            after.len(),
            after.mtime(),
            after.mtime_nsec(),
            after.ctime(),
            after.ctime_nsec(),
        ) {
            return Err(Refusal::Association);
        }
        linux::seal(&file)?;
        // No candidate instruction is executed. Read/hash only after all seals.
        io(file.seek(SeekFrom::Start(0)))?;
        let mut hash = Sha256::new();
        let mut total = 0u64;
        while total < expected.bytes {
            let count = usize::try_from((expected.bytes - total).min(buffer.len() as u64))
                .map_err(|_| Refusal::Resource)?;
            budget.pay(count)?;
            io(file.read_exact(&mut buffer[..count]))?;
            hash.update(&buffer[..count]);
            total += count as u64;
        }
        let actual = ArtifactPin {
            bytes: total,
            sha256: hash.finalize().into(),
        };
        if actual != expected {
            return Err(Refusal::Association);
        }
        inspect(&mut file, total, limits.program_headers, budget)?;
        if linux::seals(&file)? != 15 {
            return Err(Refusal::Association);
        }
        Ok(Self { file, pin: actual })
    }
    /// Inspect an already sealed owned object; never copy a mutable pathname
    /// and never treat a matching data pin as protected applicability.
    pub(crate) fn observe_existing(
        mut file: File,
        expected: ArtifactPin,
        limits: PreparationLimits,
        budget: &mut Budget,
    ) -> Result<Self, Refusal> {
        if limits.work == 0 || limits.work > 16 * 1024 * 1024 * 1024
            || limits.image_bytes == 0 || limits.image_bytes > 2usize.pow(31)
            || limits.program_headers == 0 || limits.program_headers > 4096 {
            return Err(Refusal::Resource);
        }
        let before = io(file.metadata())?;
        if !before.is_file() || before.len() != expected.bytes
            || expected.bytes > limits.image_bytes as u64 || linux::seals(&file)? != 15 {
            return Err(Refusal::Association);
        }
        io(file.seek(SeekFrom::Start(0)))?;
        let mut hash = Sha256::new();
        let mut buffer = [0; 65536];
        let mut total = 0;
        while total < expected.bytes {
            let count = usize::try_from((expected.bytes - total).min(buffer.len() as u64))
                .map_err(|_| Refusal::Resource)?;
            budget.pay(count)?;
            io(file.read_exact(&mut buffer[..count]))?;
            hash.update(&buffer[..count]);
            total += count as u64;
        }
        if <[u8; 32]>::from(hash.finalize()) != expected.sha256 {
            return Err(Refusal::Association);
        }
        inspect(&mut file, total, limits.program_headers, budget)?;
        let after = io(file.metadata())?;
        if (before.dev(), before.ino(), before.len(), before.ctime(), before.ctime_nsec(), before.mtime(), before.mtime_nsec())
            != (after.dev(), after.ino(), after.len(), after.ctime(), after.ctime_nsec(), after.mtime(), after.mtime_nsec())
            || linux::seals(&file)? != 15 {
            return Err(Refusal::Association);
        }
        Ok(Self { file, pin: expected })
    }
    pub(crate) fn same_object(&self, file: &File) -> Result<(), Refusal> {
        let a = io(self.file.metadata())?;
        let b = io(file.metadata())?;
        if (a.dev(), a.ino(), a.len()) != (b.dev(), b.ino(), b.len()) || linux::seals(file)? != 15 {
            return Err(Refusal::Association);
        }
        Ok(())
    }
    /// Exact immutable data pin, not protected approval.
    pub fn pin(&self) -> ArtifactPin {
        self.pin
    }
    /// Read-only observation of the four required seal bits.
    pub fn seals(&self) -> Result<i32, Refusal> {
        linux::seals(&self.file)
    }
}
fn read<const N: usize>(file: &mut File, at: u64, budget: &mut Budget) -> Result<[u8; N], Refusal> {
    budget.pay(N)?;
    io(file.seek(SeekFrom::Start(at)))?;
    let mut b = [0; N];
    io(file.read_exact(&mut b))?;
    Ok(b)
}
fn u16_at(b: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(b[at..at + 2].try_into().unwrap())
}
fn u32_at(b: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(b[at..at + 4].try_into().unwrap())
}
fn u64_at(b: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(b[at..at + 8].try_into().unwrap())
}
fn inspect(file: &mut File, size: u64, cap: usize, budget: &mut Budget) -> Result<(), Refusal> {
    if size < 64 {
        return Err(Refusal::Image);
    }
    let h = read::<64>(file, 0, budget)?;
    if &h[..7] != b"\x7fELF\x02\x01\x01"
        || u16_at(&h, 16) != 2
        || u16_at(&h, 18) != 62
        || u32_at(&h, 20) != 1
        || u16_at(&h, 52) != 64
        || u16_at(&h, 54) != 56
    {
        return Err(Refusal::Image);
    }
    let count = u16_at(&h, 56) as usize;
    let at = u64_at(&h, 32);
    let entry = u64_at(&h, 24);
    if count == 0
        || count > cap
        || at < 64
        || at
            .checked_add((count as u64) * 56)
            .is_none_or(|end| end > size)
    {
        return Err(Refusal::Image);
    }
    let mut executable = false;
    let mut loads = 0;
    for i in 0..count {
        let p = read::<56>(file, at + i as u64 * 56, budget)?;
        let kind = u32_at(&p, 0);
        if kind == 2 || kind == 3 {
            return Err(Refusal::Image);
        }
        if kind == 1 {
            loads += 1;
            let flags = u32_at(&p, 4);
            let off = u64_at(&p, 8);
            let addr = u64_at(&p, 16);
            let filesz = u64_at(&p, 32);
            let memsz = u64_at(&p, 40);
            let align = u64_at(&p, 48);
            if filesz > memsz
                || off.checked_add(filesz).is_none_or(|end| end > size)
                || addr.checked_add(memsz).is_none()
                || (align > 1 && (!align.is_power_of_two() || off % align != addr % align))
            {
                return Err(Refusal::Image);
            }
            executable |= flags & 1 != 0 && entry >= addr && entry < addr + memsz;
        }
    }
    if loads == 0 || !executable {
        return Err(Refusal::Image);
    }
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    fn synthetic() -> Vec<u8> {
        let mut b = vec![0u8; 120];
        b[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        b[16..18].copy_from_slice(&2u16.to_le_bytes());
        b[18..20].copy_from_slice(&62u16.to_le_bytes());
        b[20..24].copy_from_slice(&1u32.to_le_bytes());
        b[24..32].copy_from_slice(&0x400000u64.to_le_bytes());
        b[32..40].copy_from_slice(&64u64.to_le_bytes());
        b[52..54].copy_from_slice(&64u16.to_le_bytes());
        b[54..56].copy_from_slice(&56u16.to_le_bytes());
        b[56..58].copy_from_slice(&1u16.to_le_bytes());
        b[64..68].copy_from_slice(&1u32.to_le_bytes());
        b[68..72].copy_from_slice(&5u32.to_le_bytes());
        b[80..88].copy_from_slice(&0x400000u64.to_le_bytes());
        b[96..104].copy_from_slice(&120u64.to_le_bytes());
        b[104..112].copy_from_slice(&120u64.to_le_bytes());
        b
    }
    #[test]
    fn seals_before_hash_path_replacement_bounds_and_cleanup_data_only() {
        let dir = crate::test_directory("seal");
        let path = dir.join("candidate");
        let b = synthetic();
        std::fs::write(&path, &b).unwrap();
        let mut source = File::open(&path).unwrap();
        std::fs::remove_file(&path).unwrap();
        std::fs::write(&path, b"replacement").unwrap();
        let expected = ArtifactPin {
            bytes: b.len() as u64,
            sha256: Sha256::digest(&b).into(),
        };
        let limits = PreparationLimits {
            image_bytes: 120,
            work: 1024,
            program_headers: 1,
        };
        let mut sealed = SealedData::copy(&mut source, expected, limits).unwrap();
        assert_eq!(sealed.pin(), expected);
        assert_eq!(sealed.seals().unwrap(), 15);
        assert!(sealed.file.write_all(b"!").is_err());
        assert!(sealed.file.set_len(0).is_err());
        let mut measured = Budget::new(limits.work);
        SealedData::copy_metered(&mut source, expected, limits, &mut measured).unwrap();
        let exact = limits.work - measured.remaining;
        SealedData::copy_metered(&mut source, expected, limits, &mut Budget::new(exact)).unwrap();
        let mut short_work = Budget::new(exact - 1);
        assert_eq!(
            SealedData::copy_metered(&mut source, expected, limits, &mut short_work).unwrap_err(),
            Refusal::Resource
        );
        assert!(SealedData::copy_metered(&mut source, expected, limits, &mut short_work).is_err());
        SealedData::copy_metered(&mut source, expected, limits, &mut Budget::new(exact)).unwrap();
        let fd = std::os::fd::AsRawFd::as_raw_fd(&sealed.file);
        drop(sealed);
        assert!(!std::path::Path::new(&format!("/proc/self/fd/{fd}")).exists());
        let mut short = limits;
        short.work = 1;
        assert_eq!(
            SealedData::copy(&mut source, expected, short).unwrap_err(),
            Refusal::Resource
        );
        let mut wrong = expected;
        wrong.sha256[0] ^= 1;
        assert_eq!(
            SealedData::copy(&mut source, wrong, limits).unwrap_err(),
            Refusal::Association
        );
        assert_eq!(
            SealedData::copy(&mut source, expected, limits)
                .unwrap()
                .pin(),
            expected
        );
        std::fs::remove_dir_all(dir).unwrap();
    }
}
