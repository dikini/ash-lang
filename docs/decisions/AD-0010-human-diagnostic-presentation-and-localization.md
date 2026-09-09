# AD-0010: Human Diagnostic Presentation and Localization

- ID: `AD-0010`
- Status: accepted
- Related:
  [DN-0029](../design/DN-0029-human-diagnostic-presentation.md),
  [AD-0005](AD-0005-parser-architecture.md),
  [AD-0006](AD-0006-front-end-semantic-boundaries.md),
  [TASK-0021](../tasks/TASK-0021-implement-human-diagnostics.md)

## Decision

Ash renders human-first diagnostics by default. Human diagnostics lead with a
localized plain explanation, resolve causal spans to paths, one-based lines and
columns, show source excerpts and labels, and place the stable reason code after
the explanation.

The executable provides explicit `human`, `short`, and `json` message formats.
`human` is the default. `short` is compact localized log output and is not a
machine protocol. `json` emits one locale-independent, schema-versioned object
per diagnostic and is the automation contract. Format selection does not
otherwise depend on whether stderr is a terminal.

Existing phase-specific diagnostic types continue to own semantic reasons,
facts, and causal spans. The driver exposes only the common presentation data
the renderers require and retains the source catalogue needed to resolve spans.
Rendering neither parses diagnostic prose nor reconstructs static policy.

Compile-time and runtime reporting have distinct interfaces. Compile-time
presentation may allocate for messages, localization and excerpts, subject to
compiler resource limits. Runtime reporting preserves the running program's
failure guarantees: it invokes no source effects, attempts no recovery, and
does not obscure the primary failure or cleanup outcome. Resource-failure
reporting must remain independent of allocation and catalogue formatting.
Shared reason conventions and JSON structure do not require a shared reporting
implementation or a caller-selected safety flag.

Render one diagnostic to a supplied writer; collections call that operation in
their established order. Compiler phases construct diagnostics but do not
print them. The executable selects format, locale and destination.

Compile-time human text comes from embedded locale catalogues selected by message
identities and typed named arguments. Catalogues may reorder arguments and
apply plural or grammatical selection. They do not own diagnostic
classification, ordering, source layout, terminal styling, or Ash semantics.
Ash source spellings, types, operators, paths, and reason codes remain verbatim.
Runtime text uses the same wording ownership, but any required preparation
happens before execution. It does not introduce a second hand-maintained set
of translations or require catalogue formatting on a resource-failure path.

Each message has one compiler-owned declaration of its identity and named,
typed arguments. Construction checks those arguments. Message enumeration,
catalogue validation and formatting must not require independently maintained
copies of that declaration. Ordinary new messages require no renderer changes.
Wording changes belong in catalogues, not compiler passes. Stable semantic
reasons and causal relationships are distinct from presentation identities.

JSON retains named facts and each label's semantic relationship, not merely
whether the label is primary or related. Message arguments must not become a
second independently maintained copy of those facts. Translation wording and
presentation keys are not the machine compatibility contract.

An explicit locale option overrides a supported process locale. `C`, `POSIX`,
an absent locale, and an unsupported locale fall back to English. Locale
fallback proceeds through a parent locale to English. The first retained
checkpoint includes complete English and Bulgarian catalogues and validates
their key and argument agreement.

## Defaults and reporting failures

- Without a format option, use `human`; invalid formats are usage errors.
- Explicit locale selection overrides the first nonempty `LC_ALL`,
  `LC_MESSAGES`, or `LANG`. Normalize POSIX locale spelling and try the
  supported locale, then its parent, then English. Unsupported or malformed
  locale names select English, including explicit names; a missing option
  argument is a usage error.
- Repeated format or locale options are usage errors. For invocation errors,
  honor exactly one valid format supplied before the entry path; otherwise
  use human output. Apply locale fallback independently. Test argument-order
  permutations so error presentation does not depend on an early parse exit.
- Required message declarations and translations must pass completeness,
  argument and formatting tests. A generic default explanation must not hide
  a missing message. Optional help may be absent.
- An unexpected catalogue failure uses a minimal locale-independent fallback
  preserving the original reason and available structured facts. JSON output
  remains JSON. Do not recursively diagnose the renderer failure.
- Stop on stderr write failure. A failed stdout write may receive one bounded
  report on stderr; do not retry a failed diagnostic channel.

## Internal causes

Compiler-internal validation failures retain a structured cause through later
contextual boundaries. A caller may attach an import or other causal source
location but may not replace the underlying failure with a generic internal
state. Human output identifies Ash as responsible and does not recommend source
changes that the compiler cannot justify. Compiler documentation calls the
dependency representation a checked export summary; ordinary human diagnostics
refer to checked information for the imported module rather than “body-free
authentication.”

## Context

AD-0005 and AD-0006 established structured diagnostics and source provenance
independently from rendering. The retained implementation meets that data
boundary for many source failures but exposes a minimal reason and raw span
view at the executable boundary.

The `lib-ash` migration evidence showed both presentation and causal-data loss.
Eight teaching-program importers reported the same internal-state reason and
compiler term. Checked-export-summary validation collapses many invariant
failures before resolution adds the import span, so neither a reader nor a
compiler developer receives the failed relationship.

DN-0029 compared a human-first default, a code-first human view, and enrichment
of the current reason-first view. It also compared typed locale templates,
whole-string lookup, and per-locale renderer code. Human-first output with an
explicit JSON automation contract and typed locale templates separates those
consumers with less continuing coupling.

## Consequences

- Human prose, gutters, wrapping, and color may improve without changing the
  machine contract.
- Exit status, responsibility, reason, phase-owned facts, byte spans, causal
  label order, and JSON schema meanings remain stable within their documented
  compatibility boundary.
- Downstream automation must request JSON instead of parsing default prose.
- Every reachable CLI failure has an explicit format contract. Compile-time
  failures share presentation code; runtime failures use a distinct reporting
  interface with separately verified resource guarantees. No accidental legacy
  path remains at task completion.
- Bulgarian is product evidence for catalogue structure, Unicode layout, and
  translation workflow rather than a promise that every later Ash checkpoint
  adds another locale.
- DN-0029 records the completed Fluent selection. Reuse it without repeating
  the comparison or defining a localization language.
- Runtime catalogue loading, editor protocols, telemetry, automatic reports,
  interactive corrections, and translation services remain outside this
  decision.
- The decision changes tool presentation and compiler failure data, not Ash
  language validity or runtime semantics.

## Verification

The implementation must provide:

- structural tests for responsibility, reason, typed facts, primary and
  related spans, justified help, and internal developer details independently
  from rendering;
- mutation tests for structured causes in specific invariant families;
- producer-side validation before atomic publication and restored
  current-language outcomes for all eight migration triggers at the separate
  post-`effect-ash` repair checkpoint, now verified on `main` in the
  [repair evidence](../design/migration-repair-evidence.md);
  this separate repair does not complete TASK-0021 presentation work;
- English and Bulgarian catalogue completeness and typed-argument validation;
- representative human snapshots across syntax, resolution, kind, type,
  interface, constraint, pattern, coverage, entry, input, and internal failure
  families;
- source-layout cases covering tabs, Cyrillic, combining and wide characters,
  multiline spans, and cross-file labels;
- short-format and versioned JSON-lines tests, including multiple syntax
  diagnostics, causal label relationships and locale-independent JSON facts;
- runtime tests preserving primary and teardown failures, cleanup status,
  allocation-independent resource reporting and stop-on-write-failure behavior;
- tests for defaults, invalid invocations and nonrecursive reporting fallback;
- unchanged stdout and exit-status behavior; and
- updated tool documentation and downstream checks at the same checkpoint.
