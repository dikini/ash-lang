//! Fixed v2 report framing. Frames are observations, never activation grants.
use crate::{Refusal, io};
use std::{fs::File, io::Write};
const MAGIC: &[u8; 8] = b"ASHOUT02";
const HEADER: usize = 24;
// These are the fixed v2 wire profile, bound by the approved code identity.
const MAX_PAYLOAD: usize = 4096;
const MAX_FRAMES: usize = 1024;
pub(crate) const STREAM_BYTES: usize = 4 * 1024 * 1024;
const MAX_BYTES: usize = STREAM_BYTES;

/// Closed v2 observation channels; no variant conveys admission authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u32)]
pub enum OutcomeFrameKind {
    /// Supported source result or explicit runtime failure.
    Result = 1,
    /// Authored Trace data from the admitted source computation.
    Trace = 2,
    /// One independent structural K closing record.
    ScopeClosing = 3,
    /// Separate KAbsent guard inspection; never a source closing record.
    UnpublishedGuard = 4,
    /// Last frame, followed by EOF; not proof of native consumption.
    Terminal = 5,
}
fn kind(raw: u32) -> Result<OutcomeFrameKind, Refusal> {
    match raw { 1 => Ok(OutcomeFrameKind::Result), 2 => Ok(OutcomeFrameKind::Trace),
        3 => Ok(OutcomeFrameKind::ScopeClosing), 4 => Ok(OutcomeFrameKind::UnpublishedGuard),
        5 => Ok(OutcomeFrameKind::Terminal), _ => Err(Refusal::Malformed) }
}
fn header(sequence: u64, kind: OutcomeFrameKind, bytes: usize) -> Result<[u8; HEADER], Refusal> {
    if bytes > MAX_PAYLOAD { return Err(Refusal::Resource); }
    if kind == OutcomeFrameKind::Terminal && bytes != 0 { return Err(Refusal::Malformed); }
    let mut header = [0; HEADER];
    header[..8].copy_from_slice(MAGIC);
    header[8..16].copy_from_slice(&sequence.to_le_bytes());
    header[16..20].copy_from_slice(&(kind as u32).to_le_bytes());
    header[20..24].copy_from_slice(&(bytes as u32).to_le_bytes());
    Ok(header)
}

pub(crate) struct ReportWriter {
    file: File,
    sequence: u64,
    bytes: usize,
    failed: bool,
    terminal: bool,
    prepared: bool,
    closings_finished: bool,
    reserved_frames: usize,
    reserved_bytes: usize,
}
impl ReportWriter {
    // Only the actual protected verifier supplies this independently bound pipe.
    pub(crate) fn new(file: File) -> Self {
        Self { file, sequence: 0, bytes: 0, failed: false, terminal: false, prepared: false,
            closings_finished: false, reserved_frames: 0, reserved_bytes: 0 }
    }
    pub(crate) fn reserve_closings(&mut self, count: usize) -> Result<(), Refusal> {
        if self.prepared || self.sequence != 0 { return Err(Refusal::Association); }
        let frames = count.checked_add(1).ok_or(Refusal::Resource)?;
        let bytes = count.checked_mul(HEADER + 32).and_then(|n| n.checked_add(HEADER)).ok_or(Refusal::Resource)?;
        if frames > MAX_FRAMES || bytes > MAX_BYTES { return Err(Refusal::Resource); }
        self.reserved_frames = frames;
        self.reserved_bytes = bytes;
        self.prepared = true;
        Ok(())
    }
    pub(crate) fn finish_closings(&mut self) -> Result<(), Refusal> {
        if !self.prepared || self.failed || self.terminal || self.closings_finished { return Err(Refusal::Association); }
        // Only unused closing reservation is released. Terminal stays protected
        // from every optional result/Trace frame until it is actually written.
        self.reserved_frames = 1;
        self.reserved_bytes = HEADER;
        self.closings_finished = true;
        Ok(())
    }
    pub(crate) fn write(&mut self, kind: OutcomeFrameKind, payload: &[u8]) -> Result<(), Refusal> {
        if self.failed || self.terminal { return Err(Refusal::Input); }
        if !self.prepared { return Err(Refusal::Resource); }
        let header = header(self.sequence, kind, payload.len())?;
        let bytes = self.bytes.checked_add(HEADER).and_then(|n| n.checked_add(payload.len())).ok_or(Refusal::Resource)?;
        if self.sequence >= MAX_FRAMES as u64 || bytes > MAX_BYTES { return Err(Refusal::Resource); }
        let closing = matches!(kind, OutcomeFrameKind::ScopeClosing | OutcomeFrameKind::UnpublishedGuard);
        let mandatory = closing || kind == OutcomeFrameKind::Terminal;
        if closing && (self.closings_finished || payload.len() > 32 || self.reserved_frames <= 1) {
            return Err(Refusal::Association);
        }
        if kind == OutcomeFrameKind::Terminal && !self.closings_finished { return Err(Refusal::Association); }
        if !mandatory && (self.sequence as usize + 1 + self.reserved_frames > MAX_FRAMES
            || bytes.checked_add(self.reserved_bytes).is_none_or(|n| n > MAX_BYTES)) {
            return Err(Refusal::Resource);
        }
        if mandatory {
            self.reserved_frames = self.reserved_frames.checked_sub(1).ok_or(Refusal::Association)?;
            self.reserved_bytes = self.reserved_bytes.checked_sub(HEADER + payload.len()).ok_or(Refusal::Association)?;
        }
        // Debit the complete frame before IO. After any partial/error return the
        // writer is poisoned: no frame/native transition can be retried here.
        self.failed = true;
        self.bytes = bytes;
        let mut calls = 0;
        for mut remaining in [header.as_slice(), payload] {
            while !remaining.is_empty() {
                calls += 1;
                if calls > HEADER + MAX_PAYLOAD { return Err(Refusal::Resource); }
                let count = io(self.file.write(remaining))?;
                if count == 0 { return Err(Refusal::Input); }
                remaining = &remaining[count..];
            }
        }
        self.sequence += 1;
        self.terminal = kind == OutcomeFrameKind::Terminal;
        self.failed = false;
        Ok(())
    }
}

/// Parent-side bounded DATA parser. Successful framing is not a native fact.
/// The parent still checks the source-specific payload and child exit/EOF.
pub(crate) struct FrameReader { sequence: u64, bytes: usize, terminal: bool }
impl FrameReader {
    pub(crate) fn new() -> Self { Self { sequence: 0, bytes: 0, terminal: false } }
    pub(crate) fn next<'a>(&mut self, raw: &'a [u8]) -> Result<(OutcomeFrameKind, &'a [u8], usize), Refusal> {
        if self.terminal || raw.len() < HEADER || &raw[..8] != MAGIC { return Err(Refusal::Malformed); }
        let sequence = u64::from_le_bytes(raw[8..16].try_into().map_err(|_| Refusal::Malformed)?);
        let tag = kind(u32::from_le_bytes(raw[16..20].try_into().map_err(|_| Refusal::Malformed)?))?;
        let count = u32::from_le_bytes(raw[20..24].try_into().map_err(|_| Refusal::Malformed)?) as usize;
        if sequence != self.sequence || self.sequence >= MAX_FRAMES as u64 { return Err(Refusal::Association); }
        if count > MAX_PAYLOAD { return Err(Refusal::Resource); }
        if tag == OutcomeFrameKind::Terminal && count != 0 { return Err(Refusal::Malformed); }
        let end = HEADER.checked_add(count).ok_or(Refusal::Resource)?;
        let payload = raw.get(HEADER..end).ok_or(Refusal::Malformed)?;
        self.bytes = self.bytes.checked_add(end).filter(|n| *n <= MAX_BYTES).ok_or(Refusal::Resource)?;
        self.sequence += 1;
        self.terminal = tag == OutcomeFrameKind::Terminal;
        Ok((tag, payload, end))
    }
    pub(crate) fn finish(&self) -> Result<(), Refusal> {
        if self.terminal { Ok(()) } else { Err(Refusal::Input) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn mandatory_closings_and_terminal_survive_optional_frame_exhaustion() {
        let dir = crate::test_directory("report-reservation"); let path = dir.join("frames");
        let file = std::fs::File::create(&path).unwrap(); let mut writer = ReportWriter::new(file);
        assert_eq!(writer.reserve_closings(MAX_FRAMES),Err(Refusal::Resource));
        writer.reserve_closings(1).unwrap();
        assert_eq!(writer.reserve_closings(1),Err(Refusal::Association));
        for _ in 0..MAX_FRAMES-2 { writer.write(OutcomeFrameKind::Trace,b"").unwrap(); }
        assert_eq!(writer.write(OutcomeFrameKind::Result,b""),Err(Refusal::Resource));
        writer.write(OutcomeFrameKind::ScopeClosing,&[0;32]).unwrap();
        writer.finish_closings().unwrap(); writer.write(OutcomeFrameKind::Terminal,b"").unwrap();
        assert_eq!(writer.write(OutcomeFrameKind::Terminal,b""),Err(Refusal::Input));
        drop(writer); std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn failed_output_poison_cannot_publish_another_fact_or_terminal() {
        let dir = crate::test_directory("report-poison"); let path = dir.join("data"); std::fs::write(&path,b"unchanged").unwrap();
        let mut writer = ReportWriter::new(File::open(&path).unwrap()); writer.reserve_closings(1).unwrap();
        assert_eq!(writer.write(OutcomeFrameKind::ScopeClosing,b"facts"),Err(Refusal::Input));
        assert_eq!(writer.write(OutcomeFrameKind::ScopeClosing,b"facts"),Err(Refusal::Input));
        assert_eq!(writer.finish_closings(),Err(Refusal::Association));
        assert_eq!(writer.write(OutcomeFrameKind::Terminal,b""),Err(Refusal::Input));
        assert_eq!(std::fs::read(&path).unwrap(),b"unchanged"); drop(writer);std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn framed_channels_preserve_order_cuts_and_explicit_terminal() {
        let first = header(0, OutcomeFrameKind::UnpublishedGuard, 3).unwrap();
        let mut raw = first.to_vec(); raw.extend_from_slice(b"raw");
        for end in 0..raw.len() {
            assert!(FrameReader::new().next(&raw[..end]).is_err());
        }
        let mut reader = FrameReader::new();
        assert_eq!(reader.next(&raw).unwrap(), (OutcomeFrameKind::UnpublishedGuard, b"raw".as_slice(), raw.len()));
        assert_eq!(reader.finish(), Err(Refusal::Input));
        assert!(reader.next(&raw).is_err());
        let terminal = header(1, OutcomeFrameKind::Terminal, 0).unwrap();
        assert_eq!(reader.next(&terminal).unwrap().0, OutcomeFrameKind::Terminal);
        reader.finish().unwrap();
        assert!(reader.next(&terminal).is_err());
        for _ in 0..2 { assert!(FrameReader::new().next(&raw).is_ok()); }
        assert_eq!(header(0, OutcomeFrameKind::Result, MAX_PAYLOAD + 1), Err(Refusal::Resource));
    }
}
