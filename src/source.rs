//! Stable source identities and checked half-open byte ranges.

use std::{
    error::Error,
    fmt,
    sync::atomic::{AtomicU32, Ordering},
};

/// Identifies one admitted source file.
///
/// The process allocator assigns values in `0..u32::MAX`. The value
/// `u32::MAX` is reserved as the allocator's exhaustion sentinel and is never
/// exposed as a [`SourceId`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SourceId(u32);

impl SourceId {
    const fn new(value: u32) -> Self {
        Self(value)
    }

    /// Returns the allocator-provided value in `0..u32::MAX`.
    #[must_use]
    pub const fn value(self) -> u32 {
        self.0
    }
}

static SOURCE_IDS: SourceIdAllocator = SourceIdAllocator::with_next(0);

struct SourceIdAllocator {
    next: AtomicU32,
}

impl SourceIdAllocator {
    const fn with_next(next: u32) -> Self {
        Self {
            next: AtomicU32::new(next),
        }
    }

    fn allocate(&self) -> Result<SourceId, SourceError> {
        self.next
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, checked_add_one)
            .map(SourceId::new)
            .map_err(|_| SourceError::SourceIdExhausted)
    }
}

const fn checked_add_one(value: u32) -> Option<u32> {
    value.checked_add(1)
}

/// A half-open range of UTF-8 byte offsets.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ByteRange {
    start: u32,
    end: u32,
}

impl ByteRange {
    /// Creates an ordered half-open byte range.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidByteRange`] when `start` is greater than `end`.
    pub const fn new(start: u32, end: u32) -> Result<Self, InvalidByteRange> {
        if start > end {
            return Err(InvalidByteRange { start, end });
        }

        Ok(Self { start, end })
    }

    /// Returns the inclusive start offset.
    #[must_use]
    pub const fn start(self) -> u32 {
        self.start
    }

    /// Returns the exclusive end offset.
    #[must_use]
    pub const fn end(self) -> u32 {
        self.end
    }
}

/// An attempt to create a byte range whose end precedes its start.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidByteRange {
    start: u32,
    end: u32,
}

impl InvalidByteRange {
    /// Returns the rejected start offset.
    #[must_use]
    pub const fn start(self) -> u32 {
        self.start
    }

    /// Returns the rejected end offset.
    #[must_use]
    pub const fn end(self) -> u32 {
        self.end
    }
}

impl fmt::Display for InvalidByteRange {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "byte range start {} exceeds end {}",
            self.start, self.end
        )
    }
}

impl Error for InvalidByteRange {}

/// A checked byte range in one admitted source file.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Span {
    source: SourceId,
    range: ByteRange,
}

impl Span {
    /// Returns the source containing this span.
    #[must_use]
    pub const fn source(self) -> SourceId {
        self.source
    }

    /// Returns this span's half-open byte range.
    #[must_use]
    pub const fn range(self) -> ByteRange {
        self.range
    }

    /// Returns the smallest span covering both inputs when they share a source.
    pub(crate) fn cover(self, other: Self) -> Option<Self> {
        if self.source != other.source {
            return None;
        }
        Some(Self {
            source: self.source,
            range: ByteRange {
                start: self.range.start.min(other.range.start),
                end: self.range.end.max(other.range.end),
            },
        })
    }
}

/// Why a compiler-owned node was generated from a source construct.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum GeneratedReason {
    /// A source function presentation was lowered to a function node.
    FunctionLowering,
    /// A source binding presentation was lowered to a binding node.
    BindingLowering,
    /// A simultaneous recursive binding group was lowered to one Core node.
    RecursiveBindingLowering,
    /// A node records checking against a source-supplied type.
    TypeChecking,
    /// A generated literal replaces a literal primitive operation.
    ConstantFolding,
}

impl fmt::Display for GeneratedReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::FunctionLowering => "function lowering",
            Self::BindingLowering => "binding lowering",
            Self::RecursiveBindingLowering => "recursive binding lowering",
            Self::TypeChecking => "type checking",
            Self::ConstantFolding => "constant folding",
        })
    }
}

/// Source provenance retained by parsed and generated compiler nodes.
#[derive(Debug, Eq, PartialEq)]
pub enum Origin {
    /// A node corresponds directly to one source span.
    Source(Span),
    /// A compiler-owned node was generated because of another origin.
    Generated {
        /// The source or generated construct that caused this node.
        cause: Box<Origin>,
        /// The compiler operation that generated this node.
        reason: GeneratedReason,
    },
    /// A primary origin participates in a relation with other source spans.
    Related {
        /// The origin that remains primary for diagnostics.
        primary: Box<Origin>,
        /// The source spans related to the primary origin.
        related: Vec<Span>,
    },
}

impl Clone for Origin {
    fn clone(&self) -> Self {
        enum Frame<'a> {
            Generated(GeneratedReason),
            Related(&'a [Span]),
        }

        let mut current = self;
        let mut frames = Vec::new();
        let span = loop {
            match current {
                Self::Source(span) => break *span,
                Self::Generated { cause, reason } => {
                    frames.push(Frame::Generated(*reason));
                    current = cause;
                }
                Self::Related { primary, related } => {
                    frames.push(Frame::Related(related));
                    current = primary;
                }
            }
        };

        let mut cloned = Self::Source(span);
        for frame in frames.into_iter().rev() {
            cloned = match frame {
                Frame::Generated(reason) => Self::Generated {
                    cause: Box::new(cloned),
                    reason,
                },
                Frame::Related(related) => Self::Related {
                    primary: Box::new(cloned),
                    related: related.to_vec(),
                },
            };
        }
        cloned
    }
}

/// Destroys owned provenance without following host-language recursion.
pub(crate) fn discard_origin_iteratively(root: Origin) {
    let mut current = root;
    loop {
        match current {
            Origin::Source(_) => return,
            Origin::Generated { cause, .. } => current = *cause,
            Origin::Related { primary, .. } => current = *primary,
        }
    }
}

impl Origin {
    /// Returns the causal source span at the base of this origin.
    #[must_use]
    pub fn primary_span(&self) -> Span {
        let mut current = self;
        loop {
            match current {
                Self::Source(span) => return *span,
                Self::Generated { cause, .. } => current = cause,
                Self::Related { primary, .. } => current = primary,
            }
        }
    }

    /// Returns the first retained relation while following the primary cause.
    #[must_use]
    pub fn related_spans(&self) -> &[Span] {
        let mut current = self;
        loop {
            match current {
                Self::Source(_) => return &[],
                Self::Generated { cause, .. } => current = cause,
                Self::Related { related, .. } => return related,
            }
        }
    }

    /// Returns the first generation reason while following the primary cause.
    #[must_use]
    pub fn generated_reason(&self) -> Option<GeneratedReason> {
        let mut current = self;
        loop {
            match current {
                Self::Source(_) => return None,
                Self::Generated { reason, .. } => return Some(*reason),
                Self::Related { primary, .. } => current = primary,
            }
        }
    }
}

/// UTF-8 source text admitted to the compiler.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceFile {
    id: SourceId,
    display_path: String,
    text: String,
    line_starts: Vec<u32>,
}

impl SourceFile {
    /// Admits a UTF-8 source file after checking representation limits.
    ///
    /// # Errors
    ///
    /// Returns [`SourceError::DisplayPathTooLarge`],
    /// [`SourceError::TextTooLarge`], [`SourceError::TooManyLines`], or
    /// [`SourceError::SourceIdExhausted`] when the corresponding source state
    /// cannot be represented by the source model.
    pub fn new(
        display_path: impl Into<String>,
        text: impl Into<String>,
    ) -> Result<Self, SourceError> {
        let display_path = display_path.into();
        let text = text.into();
        u32::try_from(display_path.len()).map_err(|_| SourceError::DisplayPathTooLarge)?;
        u32::try_from(text.len()).map_err(|_| SourceError::TextTooLarge)?;

        let mut line_starts = vec![0];
        for (offset, character) in text.char_indices() {
            if character == '\n' {
                let next_line = offset
                    .checked_add(character.len_utf8())
                    .and_then(|offset| u32::try_from(offset).ok())
                    .ok_or(SourceError::TextTooLarge)?;
                line_starts.push(next_line);
            }
        }
        u32::try_from(line_starts.len()).map_err(|_| SourceError::TooManyLines)?;
        let id = SOURCE_IDS.allocate()?;

        Ok(Self {
            id,
            display_path,
            text,
            line_starts,
        })
    }

    /// Returns this file's source identity.
    #[must_use]
    pub const fn id(&self) -> SourceId {
        self.id
    }

    /// Returns the path used in diagnostics.
    #[must_use]
    pub fn display_path(&self) -> &str {
        &self.display_path
    }

    /// Returns the admitted UTF-8 text.
    #[must_use]
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Associates an ordered range with this source file.
    ///
    /// # Errors
    ///
    /// Returns [`SourceError::RangeOutsideSource`] when the range ends after
    /// the admitted text. Returns [`SourceError::OffsetSplitsCodePoint`] when
    /// either boundary lies inside a UTF-8 scalar. [`SourceError::TextTooLarge`]
    /// and [`SourceError::InvalidLineState`] report an inconsistent stored
    /// source invariant rather than an invalid caller-supplied range.
    pub fn span(&self, range: ByteRange) -> Result<Span, SourceError> {
        let source_len = u32::try_from(self.text.len()).map_err(|_| SourceError::TextTooLarge)?;
        if range.end() > source_len {
            return Err(SourceError::RangeOutsideSource { range, source_len });
        }
        let start = usize::try_from(range.start()).map_err(|_| SourceError::InvalidLineState)?;
        if !self.text.is_char_boundary(start) {
            return Err(SourceError::OffsetSplitsCodePoint {
                offset: range.start(),
            });
        }
        let end = usize::try_from(range.end()).map_err(|_| SourceError::InvalidLineState)?;
        if !self.text.is_char_boundary(end) {
            return Err(SourceError::OffsetSplitsCodePoint {
                offset: range.end(),
            });
        }

        Ok(Span {
            source: self.id,
            range,
        })
    }

    /// Derives one-based line and Unicode-scalar columns for a checked span.
    ///
    /// The span remains a half-open byte range; this method creates only a
    /// display view.
    ///
    /// # Errors
    ///
    /// Returns [`SourceError::ForeignSpan`] when another source admitted the
    /// span, or a position error when either boundary cannot be rendered.
    pub fn location(&self, span: Span) -> Result<SourceLocation, SourceError> {
        if span.source() != self.id {
            return Err(SourceError::ForeignSpan {
                expected: self.id,
                found: span.source(),
            });
        }

        Ok(SourceLocation {
            start: self.line_column(span.range().start())?,
            end: self.line_column(span.range().end())?,
        })
    }

    /// Derives a one-based line and Unicode-scalar column from a byte offset.
    ///
    /// # Errors
    ///
    /// Returns an error when the offset is outside the source or splits a
    /// UTF-8 code point.
    pub fn line_column(&self, offset: u32) -> Result<LineColumn, SourceError> {
        let byte_offset = offset;
        let source_len = u32::try_from(self.text.len()).map_err(|_| SourceError::TextTooLarge)?;
        if offset > source_len {
            return Err(SourceError::OffsetOutsideSource { offset, source_len });
        }
        let offset = usize::try_from(offset).map_err(|_| SourceError::InvalidLineState)?;
        if !self.text.is_char_boundary(offset) {
            return Err(SourceError::OffsetSplitsCodePoint {
                offset: byte_offset,
            });
        }

        let (line_index, line_start) = self
            .line_starts
            .iter()
            .enumerate()
            .rev()
            .find(|(_, start)| usize::try_from(**start).is_ok_and(|start| start <= offset))
            .ok_or(SourceError::InvalidLineState)?;
        let line_start = usize::try_from(*line_start).map_err(|_| SourceError::InvalidLineState)?;
        let line = u32::try_from(line_index)
            .ok()
            .and_then(|line| line.checked_add(1))
            .ok_or(SourceError::TooManyLines)?;
        let line_prefix = self
            .text
            .get(line_start..offset)
            .ok_or(SourceError::InvalidLineState)?;
        let column = u32::try_from(line_prefix.chars().count())
            .ok()
            .and_then(|column| column.checked_add(1))
            .ok_or(SourceError::LineTooLong)?;

        Ok(LineColumn { line, column })
    }
}

/// A one-based display position derived from a UTF-8 byte offset.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LineColumn {
    line: u32,
    column: u32,
}

impl LineColumn {
    /// Returns the one-based line number.
    #[must_use]
    pub const fn line(self) -> u32 {
        self.line
    }

    /// Returns the one-based Unicode-scalar column number.
    #[must_use]
    pub const fn column(self) -> u32 {
        self.column
    }
}

/// The display positions at both boundaries of a half-open span.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourceLocation {
    start: LineColumn,
    end: LineColumn,
}

impl SourceLocation {
    /// Returns the display position at the span's inclusive start.
    #[must_use]
    pub const fn start(self) -> LineColumn {
        self.start
    }

    /// Returns the display position at the span's exclusive end.
    #[must_use]
    pub const fn end(self) -> LineColumn {
        self.end
    }
}

/// A source file or span cannot be represented safely.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceError {
    /// The allocatable `0..u32::MAX` identity domain is exhausted.
    ///
    /// `u32::MAX` is reserved as the allocator's exhaustion sentinel.
    SourceIdExhausted,
    /// The diagnostic display path exceeds the source model's limit.
    DisplayPathTooLarge,
    /// The UTF-8 text exceeds the source model's limit.
    TextTooLarge,
    /// The source contains more lines than the display model can represent.
    TooManyLines,
    /// One source line contains more columns than the display model can represent.
    LineTooLong,
    /// A range ends beyond its source text.
    RangeOutsideSource {
        /// The rejected range.
        range: ByteRange,
        /// The admitted source length in bytes.
        source_len: u32,
    },
    /// A source was asked to render a span admitted by another source.
    ForeignSpan {
        /// The source identity expected by the renderer.
        expected: SourceId,
        /// The source identity carried by the span.
        found: SourceId,
    },
    /// A byte offset lies beyond the admitted source text.
    OffsetOutsideSource {
        /// The rejected byte offset.
        offset: u32,
        /// The admitted source length in bytes.
        source_len: u32,
    },
    /// A byte offset lies inside a UTF-8 code point.
    OffsetSplitsCodePoint {
        /// The rejected byte offset.
        offset: u32,
    },
    /// The stored line index is inconsistent with the admitted source.
    InvalidLineState,
}

impl fmt::Display for SourceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SourceIdExhausted => {
                formatter.write_str("allocatable source identity space is exhausted")
            }
            Self::DisplayPathTooLarge => formatter.write_str("display path exceeds source limits"),
            Self::TextTooLarge => formatter.write_str("source text exceeds source limits"),
            Self::TooManyLines => formatter.write_str("source contains too many lines"),
            Self::LineTooLong => formatter.write_str("source line contains too many columns"),
            Self::RangeOutsideSource { range, source_len } => write!(
                formatter,
                "byte range {}..{} exceeds source length {source_len}",
                range.start(),
                range.end()
            ),
            Self::ForeignSpan { expected, found } => write!(
                formatter,
                "source {} cannot render a span from source {}",
                expected.value(),
                found.value()
            ),
            Self::OffsetOutsideSource { offset, source_len } => {
                write!(
                    formatter,
                    "byte offset {offset} exceeds source length {source_len}"
                )
            }
            Self::OffsetSplitsCodePoint { offset } => {
                write!(formatter, "byte offset {offset} splits a UTF-8 code point")
            }
            Self::InvalidLineState => formatter.write_str("source line index is inconsistent"),
        }
    }
}

impl Error for SourceError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_id_allocation_reserves_maximum_as_the_exhaustion_sentinel() {
        let allocator = SourceIdAllocator::with_next(u32::MAX);

        assert_eq!(allocator.allocate(), Err(SourceError::SourceIdExhausted));
    }
}
