use std::fmt;

use ash::diagnostic::{Diagnostic, SourceLabel};
use ash::source::{ByteRange, GeneratedReason, Origin, SourceError, SourceFile};

#[test]
fn line_break_spans_keep_their_exact_byte_widths() {
    let lf_source = SourceFile::new("lf.ash", "x\n")
        .expect("the test source should fit the source representation");
    let crlf_source = SourceFile::new("crlf.ash", "x\r\n")
        .expect("the test source should fit the source representation");

    let lf = lf_source
        .span(ByteRange::new(1, 2).expect("the LF range should be ordered"))
        .expect("the LF range should belong to its source");
    let crlf = crlf_source
        .span(ByteRange::new(1, 3).expect("the CRLF range should be ordered"))
        .expect("the CRLF range should belong to its source");

    assert_eq!(lf.range().end() - lf.range().start(), 1);
    assert_eq!(crlf.range().end() - crlf.range().start(), 2);

    let lf_location = lf_source
        .location(lf)
        .expect("the LF span should have a display location");
    let crlf_location = crlf_source
        .location(crlf)
        .expect("the CRLF span should have a display location");
    assert_eq!(
        (lf_location.start().line(), lf_location.start().column()),
        (1, 2)
    );
    assert_eq!(
        (lf_location.end().line(), lf_location.end().column()),
        (2, 1)
    );
    assert_eq!(
        (crlf_location.start().line(), crlf_location.start().column()),
        (1, 2)
    );
    assert_eq!(
        (crlf_location.end().line(), crlf_location.end().column()),
        (2, 1)
    );
}

#[test]
fn empty_source_eof_has_a_zero_length_first_position() {
    let source = SourceFile::new("empty.ash", "").expect("the empty source should fit");
    let eof = source
        .span(ByteRange::new(0, 0).expect("the EOF range should be ordered"))
        .expect("EOF should belong to the empty source");

    let location = source
        .location(eof)
        .expect("EOF should have a display location");

    assert_eq!(eof.range().start(), eof.range().end());
    assert_eq!((location.start().line(), location.start().column()), (1, 1));
    assert_eq!(location.start(), location.end());
}

#[test]
fn checked_ranges_reject_reversed_and_out_of_source_offsets() {
    let reversed = ByteRange::new(3, 2).expect_err("a reversed range must be rejected");
    assert_eq!(reversed.start(), 3);
    assert_eq!(reversed.end(), 2);

    let source = SourceFile::new("short.ash", "ok")
        .expect("the test source should fit the source representation");
    let outside = source
        .span(ByteRange::new(0, 3).expect("the range itself should be ordered"))
        .expect_err("a span must not end beyond its source");

    assert_eq!(
        outside,
        SourceError::RangeOutsideSource {
            range: ByteRange::new(0, 3).expect("the expected range should be ordered"),
            source_len: 2,
        }
    );
}

#[test]
fn span_admission_rejects_every_boundary_inside_a_utf8_scalar() {
    let source = SourceFile::new("utf8.ash", "aβ").expect("the UTF-8 test source should fit");

    for range in [
        ByteRange::new(2, 3).expect("the split-start range should be ordered"),
        ByteRange::new(1, 2).expect("the split-end range should be ordered"),
        ByteRange::new(2, 2).expect("the split-empty range should be ordered"),
    ] {
        assert_eq!(
            source.span(range),
            Err(SourceError::OffsetSplitsCodePoint { offset: 2 })
        );
    }
}

#[test]
fn line_and_column_are_views_over_unchanged_utf8_byte_ranges() {
    let source = SourceFile::new("unicode.ash", "aβ\r\nz")
        .expect("the test source should fit the source representation");
    let beta_range = ByteRange::new(1, 3).expect("the beta range should be ordered");
    let beta = source
        .span(beta_range)
        .expect("the beta range should belong to its source");

    let location = source
        .location(beta)
        .expect("the beta span should have a display location");

    assert_eq!(beta.range(), beta_range);
    assert_eq!((location.start().line(), location.start().column()), (1, 2));
    assert_eq!((location.end().line(), location.end().column()), (1, 3));

    let z = source
        .span(ByteRange::new(5, 6).expect("the z range should be ordered"))
        .expect("the z range should belong to its source");
    let z_location = source
        .location(z)
        .expect("the z span should have a display location");
    assert_eq!(
        (z_location.start().line(), z_location.start().column()),
        (2, 1)
    );
}

#[test]
fn a_source_rejects_a_span_admitted_by_another_source() {
    let first = SourceFile::new("first.ash", "x").expect("the first test source should fit");
    let second = SourceFile::new("second.ash", "y").expect("the second test source should fit");
    let first_span = first
        .span(ByteRange::new(0, 1).expect("the test range should be ordered"))
        .expect("the test range should belong to the first source");

    assert_eq!(
        second.location(first_span),
        Err(SourceError::ForeignSpan {
            expected: second.id(),
            found: first.id(),
        })
    );
}

#[test]
fn separately_admitted_sources_cannot_share_an_identity() {
    let first = SourceFile::new("first.ash", "x").expect("the first test source should fit");
    let second = SourceFile::new("second.ash", "y").expect("the second test source should fit");

    assert_ne!(first.id(), second.id());
    assert_eq!(first.clone().id(), first.id());
}

#[test]
fn generated_origins_retain_their_cause_and_related_spans() {
    let source =
        SourceFile::new("origin.ash", "name : Int").expect("the origin test source should fit");
    let definition = source
        .span(ByteRange::new(0, 4).expect("the definition range should be ordered"))
        .expect("the definition range should belong to the source");
    let annotation = source
        .span(ByteRange::new(7, 10).expect("the annotation range should be ordered"))
        .expect("the annotation range should belong to the source");
    let origin = Origin::Related {
        primary: Box::new(Origin::Generated {
            cause: Box::new(Origin::Source(definition)),
            reason: GeneratedReason::FunctionLowering,
        }),
        related: vec![annotation],
    };

    assert_eq!(origin.primary_span(), definition);
    assert_eq!(origin.related_spans(), &[annotation]);
    assert_eq!(
        origin.generated_reason(),
        Some(GeneratedReason::FunctionLowering)
    );
}

#[derive(Debug, Eq, PartialEq)]
enum TestReason {
    ExpectedOperand,
}

impl fmt::Display for TestReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExpectedOperand => formatter.write_str("parse.expected-operand"),
        }
    }
}

#[test]
fn diagnostic_reason_remains_typed_independently_from_rendering() {
    let source =
        SourceFile::new("diagnostic.ash", "1 +").expect("the diagnostic test source should fit");
    let operator = source
        .span(ByteRange::new(2, 3).expect("the operator range should be ordered"))
        .expect("the operator range should belong to the source");
    let diagnostic = Diagnostic {
        reason: TestReason::ExpectedOperand,
        primary: SourceLabel::new(operator, "an expression must follow this operator"),
        related: Vec::new(),
        expected: Some("expression".to_owned()),
        found: Some("end of line".to_owned()),
        help: None,
    };

    let rendered = diagnostic.render_plain();

    assert_eq!(diagnostic.reason, TestReason::ExpectedOperand);
    assert_eq!(diagnostic.primary.span(), operator);
    assert!(rendered.contains("parse.expected-operand"));
    assert!(rendered.contains("expected expression"));
    assert!(rendered.contains("found end of line"));
}
