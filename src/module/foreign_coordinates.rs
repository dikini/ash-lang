//! Compile-time offsets in immutable compiler text, never authenticated facts.
//!
//! Runtime consumers still check the defining source, module identity, origins,
//! shapes and complete candidate inventory. This table only removes text scans.

use super::{FOREIGN_SOURCE, foreign_host::FORMALS};
use crate::source::ByteRange;

/// Coordinates in canonical nominal order; no source or runtime identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ForeignNominalCoordinates {
    pub(crate) declaration: ByteRange,
    pub(crate) name: ByteRange,
    formals: [ByteRange; 3],
    formal_count: usize,
    constructors: [ByteRange; 6],
    constructor_count: usize,
}

impl ForeignNominalCoordinates {
    pub(crate) fn formals(&self) -> &[ByteRange] {
        &self.formals[..self.formal_count]
    }

    pub(crate) fn constructors(&self) -> &[ByteRange] {
        &self.constructors[..self.constructor_count]
    }
}

const fn range(start: usize, end: usize) -> ByteRange {
    assert!(
        start <= end && end <= u32::MAX as usize,
        "Foreign coordinate overflow"
    );
    match ByteRange::new(start as u32, end as u32) {
        Ok(value) => value,
        Err(_) => panic!("invalid Foreign coordinate"),
    }
}

const EMPTY_RANGE: ByteRange = range(0, 0);
const EMPTY_NOMINAL: ForeignNominalCoordinates = ForeignNominalCoordinates {
    declaration: EMPTY_RANGE,
    name: EMPTY_RANGE,
    formals: [EMPTY_RANGE; 3],
    formal_count: 0,
    constructors: [EMPTY_RANGE; 6],
    constructor_count: 0,
};
const NAMES: [&str; 18] = [
    "ConversionError",
    "Call",
    "Output",
    "Nullable",
    "Disposition",
    "Extent",
    "NativeStatus",
    "NativeFact",
    "DiagnosticAbsence",
    "Diagnostic",
    "BoundaryRecord",
    "BoundaryFailure",
    "CheckedCall",
    "FinishResult",
    "CheckedFinish",
    "CheckedCompletion",
    "CheckedScope",
    "ViolationCause",
];
const FORMAL_COUNTS: [usize; 18] = [0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 3, 0];
const CONSTRUCTOR_COUNTS: [usize; 18] = [1, 2, 2, 2, 3, 1, 2, 4, 6, 2, 1, 3, 3, 2, 3, 3, 2, 5];

const fn at(text: &[u8], offset: usize, needle: &[u8]) -> bool {
    if offset > text.len() || needle.len() > text.len() - offset {
        return false;
    }
    let mut index = 0;
    while index < needle.len() {
        if text[offset + index] != needle[index] {
            return false;
        }
        index += 1;
    }
    true
}

const fn unique(text: &[u8], needle: &[u8]) -> usize {
    assert!(!needle.is_empty(), "empty Foreign coordinate marker");
    let mut found = None;
    let mut offset = 0;
    while offset < text.len() {
        if at(text, offset, needle) {
            assert!(found.is_none(), "duplicate Foreign coordinate marker");
            found = Some(offset);
        }
        offset += 1;
    }
    match found {
        Some(offset) => offset,
        None => panic!("missing Foreign coordinate marker"),
    }
}

const fn whitespace(value: u8) -> bool {
    matches!(value, b' ' | b'\n' | b'\r' | b'\t')
}

const fn trimmed(text: &[u8], mut start: usize, mut end: usize) -> ByteRange {
    while start < end && whitespace(text[start]) {
        start += 1;
    }
    while end > start && whitespace(text[end - 1]) {
        end -= 1;
    }
    assert!(start < end, "empty Foreign coordinate segment");
    range(start, end)
}

const fn nominal_table() -> [ForeignNominalCoordinates; 18] {
    let text = FOREIGN_SOURCE.as_bytes();
    let mut rows = [EMPTY_NOMINAL; 18];
    let mut offset = 0;
    let mut local = 0;
    while offset < text.len() {
        let prefix = if at(text, offset, b"pub type ") {
            9
        } else if at(text, offset, b"pub opaque type ") {
            16
        } else {
            0
        };
        if prefix == 0 {
            while offset < text.len() && text[offset] != b'\n' {
                offset += 1;
            }
            if offset < text.len() {
                offset += 1;
            }
            continue;
        }
        assert!(local < rows.len(), "extra Foreign nominal");
        let name = offset + prefix;
        assert!(
            at(text, name, NAMES[local].as_bytes()),
            "changed Foreign nominal order"
        );
        let mut cursor = name + NAMES[local].len();
        assert!(
            text[cursor] == b' ' || text[cursor] == b'<',
            "invalid Foreign nominal name"
        );
        let mut row = EMPTY_NOMINAL;
        row.name = range(name, name + NAMES[local].len());
        if text[cursor] == b'<' {
            cursor += 1;
            loop {
                assert!(text[cursor].is_ascii_uppercase(), "invalid Foreign formal");
                assert!(row.formal_count < row.formals.len(), "extra Foreign formal");
                row.formals[row.formal_count] = range(cursor, cursor + 1);
                row.formal_count += 1;
                cursor += 1;
                if text[cursor] == b'>' {
                    cursor += 1;
                    break;
                }
                assert!(at(text, cursor, b", "), "invalid Foreign formal separator");
                cursor += 2;
            }
        }
        assert!(
            row.formal_count == FORMAL_COUNTS[local],
            "missing Foreign formal"
        );
        assert!(at(text, cursor, b" = "), "missing Foreign constructor body");
        let mut end = cursor + 3;
        while end < text.len()
            && !at(text, end, b"\npub ")
            && !at(text, end, b"\nnative_host_metadata :")
        {
            end += 1;
        }
        row.declaration = trimmed(text, offset, end);
        let mut start = cursor + 3;
        cursor = start;
        let body_end = row.declaration.end() as usize;
        while cursor <= body_end {
            if cursor == body_end || text[cursor] == b'|' {
                assert!(
                    row.constructor_count < row.constructors.len(),
                    "extra Foreign constructor"
                );
                row.constructors[row.constructor_count] = trimmed(text, start, cursor);
                row.constructor_count += 1;
                start = cursor + 1;
            }
            cursor += 1;
        }
        assert!(
            row.constructor_count == CONSTRUCTOR_COUNTS[local],
            "missing Foreign constructor"
        );
        rows[local] = row;
        local += 1;
        offset = end;
    }
    assert!(local == rows.len(), "missing Foreign nominal");
    // Constructor names are unique throughout this fixed inventory. Check the
    // name, not its payload, so a duplicate with a different payload also fails.
    let mut left = 0;
    while left < rows.len() {
        let mut ordinal = 0;
        while ordinal < rows[left].constructor_count {
            let a = rows[left].constructors[ordinal];
            let mut right = left;
            while right < rows.len() {
                let mut other = if right == left { ordinal + 1 } else { 0 };
                while other < rows[right].constructor_count {
                    let b = rows[right].constructors[other];
                    let mut ai = a.start() as usize;
                    let mut bi = b.start() as usize;
                    while ai < a.end() as usize
                        && bi < b.end() as usize
                        && text[ai] != b'('
                        && text[bi] != b'('
                        && text[ai] == text[bi]
                    {
                        ai += 1;
                        bi += 1;
                    }
                    let a_end = ai == a.end() as usize || text[ai] == b'(';
                    let b_end = bi == b.end() as usize || text[bi] == b'(';
                    assert!(!(a_end && b_end), "duplicate Foreign constructor");
                    other += 1;
                }
                right += 1;
            }
            ordinal += 1;
        }
        left += 1;
    }
    rows
}

const NOMINALS: [ForeignNominalCoordinates; 18] = nominal_table();

/// Fixed coordinate data; consumers independently authenticate each candidate.
pub(crate) fn foreign_nominal_coordinates() -> &'static [ForeignNominalCoordinates; 18] {
    &NOMINALS
}

const HOST_START: usize = unique(FOREIGN_SOURCE.as_bytes(), b"pub effect NativeHost<H>");
pub(super) const HOST_NAME: ByteRange = range(HOST_START + 11, HOST_START + 21);
pub(super) const HOST_FORMAL: ByteRange = range(HOST_START + 22, HOST_START + 23);

const fn formal_table() -> [ByteRange; 31] {
    let text = FOREIGN_SOURCE.as_bytes();
    let mut rows = [EMPTY_RANGE; 31];
    let mut seen = [false; 31];
    let mut index = 0;
    while index < FORMALS.len() {
        let (header, locals) = FORMALS[index];
        let start = unique(text, header.as_bytes());
        let mut parameter = 0;
        while parameter < header.len() && header.as_bytes()[parameter] != b'<' {
            parameter += 1;
        }
        assert!(parameter < header.len(), "missing Foreign formal header");
        let mut position = 0;
        while position < locals.len() {
            let local = locals[position] as usize;
            assert!(
                local < rows.len() && !seen[local],
                "duplicate Foreign formal local"
            );
            let offset = start + parameter + 1 + position * 3;
            assert!(
                text[offset].is_ascii_uppercase(),
                "missing Foreign formal name"
            );
            assert!(
                if position + 1 == locals.len() {
                    text[offset + 1] == b'>'
                } else {
                    at(text, offset + 1, b", ")
                },
                "invalid Foreign formal arity"
            );
            rows[local] = range(offset, offset + 1);
            seen[local] = true;
            position += 1;
        }
        index += 1;
    }
    let mut index = 0;
    while index < seen.len() {
        assert!(seen[index], "missing Foreign formal local");
        let mut other = index + 1;
        while other < seen.len() {
            assert!(
                rows[index].start() != rows[other].start(),
                "duplicate Foreign formal coordinate"
            );
            other += 1;
        }
        index += 1;
    }
    assert!(
        rows[22].start() == HOST_FORMAL.start(),
        "changed Foreign host formal"
    );
    rows
}

pub(super) const FORMAL_RANGES: [ByteRange; 31] = formal_table();
