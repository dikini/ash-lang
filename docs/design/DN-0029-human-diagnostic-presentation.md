# DN-0029: Human Diagnostic Presentation

- ID: `DN-0029`
- Status: exploring
- Related: [AD-0005: Parser Architecture](../decisions/AD-0005-parser-architecture.md), [AD-0006: Front-End Semantic Boundaries](../decisions/AD-0006-front-end-semantic-boundaries.md), [AD-0010: Human Diagnostic Presentation and Localization](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md)

> This design note is informative. It does not define current Ash or accept an architecture.

## Question

How should Ash turn its retained semantic reasons and causal source spans into
plain, source-aware, localized diagnostics without making presentation text a
semantic authority or building a general tooling platform before one is needed?

## Context

AD-0005 and AD-0006 require structured parser, resolution, checking, and
elaboration failures independently from rendering. The current executable
renders the reason, process-local source identity, byte range, and label text as
a minimal stable view. It does not resolve ordinary pipeline spans to file
paths, line and column positions, or excerpts.

Migration of eight recursive-algorithm teaching programs at the exact
`lib-ash` checkpoint exposed a second loss. Each importer receives
`resolve.internal-state` and the phrase “a dependency summary failed body-free
authentication.” Summary validation first collapses many distinct invariant
failures to `InvalidState`; the resolver then replaces that result with one
generic label at the import. The result identifies the boundary crossed but
neither explains the compiler's responsibility nor retains the invariant that
failed.

The term “body-free authentication” names compiler representation work. A
checked dependency publishes an immutable export summary containing the public
and hidden facts required by importers but not executable definition bodies.
Ash source neither declares nor authenticates this summary. User-facing prose
therefore should discuss the imported module; compiler documentation may call
the representation a checked export summary.

## Constraints

- Language validity, first-failure ownership, causal label order, exit status,
  and stdout behavior remain unchanged.
- Compiler stages retain typed reasons and facts. A renderer does not infer
  policy or parse compiler prose.
- Internal validation retains a cause specific enough for compiler
  investigation. An importing boundary may add its source context but may not
  replace that cause.
- Human rendering uses source paths, one-based lines and columns, excerpts, and
  labels. Raw process source identities and byte ranges remain machine facts.
- Human prose may change. Automation receives a versioned machine contract.
- Translated templates may reorder named facts and apply grammatical selection
  without translating Ash identifiers, types, operators, paths, or reason
  codes.
- The first retained checkpoint proves localization with complete English and
  Bulgarian catalogues.
- Existing phase-specific diagnostic types remain the semantic owners. A
  presentation boundary must not duplicate them into a speculative universal
  error algebra.

## Candidate directions

### Human-first default with explicit formats

The default renderer leads with a plain explanation, shows source excerpts and
causal labels, and places the stable reason code after the explanation. An
explicit short format serves compact logs. A versioned JSON-lines format serves
automation and editor consumers.

This direction gives learners the intended default while separating human
wording from the machine contract. Existing downstream checks must migrate from
parsing default prose to JSON at the same checkpoint.

### Code-first human rendering

A Rust-like `error[reason]` heading could preserve a prominent code while
adding excerpts and explanations. It reduces the visible contract change but
continues to lead learner interaction with compiler taxonomy. Long interface,
constraint, and internal reasons remain difficult even when the following
prose is clear.

### Enrich the current stable view

The current reason-first lines could gain paths, excerpts, and explanations.
This is the smallest presentation change, but it preserves display text as an
accidental automation protocol and keeps process-oriented structure ahead of
the reader's question.

The human-first direction best separates the learner, log, and automation
uses. Output selection must be explicit rather than depend on whether stderr is
a terminal. Only optional color may vary with terminal capability.

## Message catalogue directions

### Typed named arguments and locale catalogues

A reason and label role select stable message identities. The renderer supplies
named values derived from typed diagnostic facts. Locale templates may reorder
those values and apply plural or grammatical selection. The catalogue owns
words and sentence structure, not semantic classification, diagnostic order,
source layout, or terminal styling.

This direction supports real translation without asking translators to edit
Rust or copy complete English output blocks. It requires catalogue validation
for missing keys, unknown arguments, invalid templates, and locale fallback.

### Whole-string lookup

Looking up complete English strings is initially small, but punctuation or
wording changes become message identities. It handles variable reordering and
grammar poorly and encourages compiler phases to assemble sentences before
translation.

### Per-locale rendering code

Separate renderer code can express any grammar, but duplicates layout and
control flow and requires Rust changes for ordinary translation work.

Typed named templates are favored. A bounded implementation comparison should
select an existing catalogue format and Rust integration using only the
required criteria: named arguments, grammatical selection, validation,
embedded catalogues, deterministic fallback, and translator workflow.

## Selected presentation model

Phase failures expose their existing typed reason, facts, and source labels
through a small driver-owned presentation view. The view adds responsibility
(`source`, `compiler`, or `environment`) and safe developer details where the
phase failure does not already carry them. A source catalogue resolves spans
for presentation. Three renderers consume the same view:

- `human`, the default, renders localized explanation and source context;
- `short` renders one compact localized log line; and
- `json` emits one locale-independent, schema-versioned object per diagnostic.

The human catalogue uses separate keys for titles, primary labels, related
labels, explanations, and justified help. It never constructs a sentence by
concatenating independently translated fragments. Templates receive semantic
text roles so source spellings remain escaped and visually distinguishable
from prose.

Locale selection follows an explicit `--locale` option, then the supported
process locale. `C`, `POSIX`, an absent locale, or an unsupported locale falls
back to English. Tests always choose a locale explicitly. Requested locales
fall back through their parent to English. The first implementation embeds
catalogues in the executable and does not load arbitrary runtime catalogue
files.

For checked-export-summary validation, a small closed invariant family and a
summary section retain the failed relationship. The design does not require
one public Rust variant per conditional branch. Developer details may carry a
stable check identity and safe observed facts. The importer adds its import
span and module context without converting the failure to a generic resolver
state.

## Evidence and experiments

The catalogue-format comparison is disposable. Retain only its findings and
the selected dependency or small integration layer. Do not build a custom
localization language when an existing format satisfies the required cases.

Compare candidates with English and Bulgarian versions of:

- a type mismatch with expected and found types;
- a plural-sensitive coverage failure;
- a multi-file import or opacity diagnostic;
- the checked-export-summary internal failure; and
- a message containing Ash identifiers, operators, and paths that must remain
  verbatim and escaped.

The product checkpoint must additionally establish:

- every honestly produced checked export summary validates before publication;
- the eight retained migration triggers reach their current-language source or
  execution outcomes rather than a compiler-internal failure;
- every reachable CLI failure uses the new presentation path;
- every English and Bulgarian message key accepts exactly its declared named
  arguments;
- human layout handles tabs, Cyrillic, combining characters, wide characters,
  multiline spans, and labels from several files;
- JSON preserves stable reasons, responsibility, facts, byte spans, and causal
  order independently from localized prose; and
- `ash-doc` migration checks consume JSON rather than default human text.

## Intentional exclusions

The first checkpoint adds no runtime catalogue downloads, third-party catalogue
overrides, editor protocol, telemetry, automatic bug submission, translation
management service, interactive correction, or general rich-text UI. It does
not require colors to complete the human renderer. It reuses `SourceFile` line
data and existing phase diagnostic facts unless evidence shows one missing
relationship.

## Open questions

- Which existing message format and Rust integration satisfy the bounded
  comparison with the least new mechanism?
- Which small invariant families describe checked-export-summary failures
  without losing the exact failed relationship?
- Which Bulgarian terminology guide should govern recurring compiler and source
  concepts?
