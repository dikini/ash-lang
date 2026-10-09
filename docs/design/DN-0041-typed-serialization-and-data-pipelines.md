# DN-0041: Typed Serialization and Data Pipelines

- ID: `DN-0041`
- Status: exploring
- Related: [DN-0040](DN-0040-floating-point-semantics-and-representation.md),
  [DN-0039](DN-0039-files-and-filesystem-resources.md),
  [DN-0023](DN-0023-interfaces-and-implementations.md),
  [DN-0025](DN-0025-library-and-package-milestones.md),
  [DN-0030](DN-0030-typed-compiler-macros-and-hooks.md),
  [DN-0035](DN-0035-region-memory-management-and-verified-providers.md),
  [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md),
  [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0038](DN-0038-resource-properties-and-mutable-variable-usage.md),
  [AD-0007](../decisions/AD-0007-typed-core-dialects.md),
  [AD-0008](../decisions/AD-0008-explicit-evaluator-machine.md)

> This note explores an Ash adaptation of Serde's architecture and executable
> parsing, processing and transformation pipelines. It defines no current
> interfaces, format semantics, derivation facility or runtime optimization,
> and authorizes no implementation. JSON, YAML, CSV, TOML and BSON are first-class
> design cases. This is separate from DN-0036's active completion criteria.

## Question and objective

Can Ash express a reusable checked relationship between application data types
and independent data formats, with useful parsing and processing APIs? Which
existing interfaces, type parameters, effects and resource dependencies suffice,
which language additions need proposals, and which costs arise only from the
framework or rich type machinery?

Adapt Serde's framework architecture to Ash. Application types define their
encoding/decoding relationships, while format modules supply representations.
Serde's data-model and visitor interfaces provide comparison evidence, not an
Ash API or a requirement to reproduce its Rust types.
[Serde architecture](https://serde.rs/),
[Serde data model](https://serde.rs/data-model.html)

The intended deliverables are reusable Ash libraries for the five formats,
typed transformation pipelines, a developer authoring blueprint, and measured
runtime requirements. Test manual and eventually generated implementations,
cross-module generic use, copied and scoped data, and processing on real inputs.
Small successful examples alone do not establish framework expressibility or
controlled memory costs.

## Context and authority

The [current specification](../../spec/README.md) provides primitive `Int`,
`Bool` and `Unit`, tuples, parameterized nominal algebraic data, `newtype`,
rank-1 constrained schemes, higher-kinded parameters, relational interfaces
and method-local type parameters. Nominal constructor payloads are positional;
there is no current record-field reflection or general derivation facility.

[Elaboration](../../spec/elaboration.md) authenticates selected interface
evidence, then lowers methods to ordinary functions. The
[dynamic semantics](../../spec/dynamic-semantics.md#generated-interface-evidence)
do not perform runtime interface selection. Pure type operations and `newtype`
wrappers erase; Effect execution retains lexical instantiation needed by exact
operation identities. Aggregates occupy an evaluator-managed heap. These
facts do not establish zero-cost generic calls, packed collections or bounded
retention over an arbitrarily long pipeline.

The provider [execution record](provider-experiments/execution.md) records
experimental packed `Bytes`, UTF-8 `String`, literals and resource support.
Those branch capabilities require their own adoption before becoming normative.
The current specification has no Float, selectable region policy, general
borrowing, associated types, user compiler macros or native-code backend.
Related design notes do not provide those capabilities by implication.

[DN-0040](DN-0040-floating-point-semantics-and-representation.md) separately
plans normative floating point.
[DN-0039](DN-0039-files-and-filesystem-resources.md) provides prospective
file input/output. The scoped arena and later access regimes provide memory
experiments, not prerequisites for the first owned in-memory format libraries.

## Constraints

- Follow the types before proposing syntax. Identify values, interface
  parameters, effects, error types, storage dependencies and state transitions.
- Put data mappings and format logic in Ash modules. Compiler additions need a
  generic language or runtime contract, not a serializer or format name.
- Preserve passive modules, authenticated implementation evidence, opaque
  representation boundaries and independent linked/Core validation.
- Treat all five formats as framework design and acceptance cases. Delivery
  can be incremental, but each implemented profile must state its coverage.
- Preserve type-specific and format-specific information where the selected
  contract requires it. Unsupported conversion reports an error or uses an
  explicitly selected policy; it never silently discards precision or structure.
- Start with owned/copying values and manual implementations. Borrowing,
  derivation and performance transformations have separate evidence gates.
- Keep arenas lexical and nontransportable. Concurrency, asynchronous pipelines,
  process transfer, reference counting and tracing are separate studies.

## Candidate framework

### Typed roles and state

The following are design roles, not accepted interface declarations. Use complete
parameter applications of fixed kinds and the existing constrained-function
model before requesting associated types or higher-rank source functions.

| Role | Type relationship to establish |
| --- | --- |
| Application value `T` | The nominal or structural value being encoded or constructed; its public representation contract is explicit. |
| Format/profile `F` | A statically identifiable format and admitted options, with runtime configuration only where needed. |
| Encoder state `S` | Output state with the backing storage, progress and effect dependencies required by its operations. |
| Decoder state `D` | Input/cursor state with its storage dependencies, absolute position and incremental state. |
| Error `E` | Structured failure with location/path and any committed progress; dependencies must be visible if error data retains storage. |
| Encoding evidence | Checked methods relating `T`, `S`, `E` and an effect row. |
| Decoding evidence | Checked methods relating `D`, `T`, `E` and an effect row. |
| Construction/visitor evidence | Checked operations that build the requested `T` from the format's admitted categories. |
| Schema/mapping | Explicit names, variant representation, optional/default fields and conversion policy; checked evidence, library data or generated code according to its role. |

One comparison uses ordinary state threading. Schematically, an encoding
operation takes `(S, T)` and returns either updated `S` or `E`; decoding takes
`D` and returns either `(T, D)` or `E`. Their computation types state an exact
effect row. These are logical signatures, not source syntax, first-class
dictionaries or a claim that one interface already expresses the whole design.
An ordinary state value is duplicable; state threading alone proves neither
linearity nor unique access to mutable backing storage.

Another comparison uses identity-indexed resources for mutable decoder or
builder state. Its handles, callbacks and errors must retain the owner and
access-interval dependencies. Compare annotation burden, expression within
current method schemes, state allocation and per-value dispatch. Neither
direction may obtain mutation or one-shot callback authority from a name alone.

Format-specific entry functions fix `F`; the target annotation or contextual
result type fixes `T`. Do not rely on a phantom format name that inference
cannot determine. Specify independent checking of exported generic functions
and imported implementations before selecting convenience syntax.

Authors specify field/variant mappings, profiles, conversion/default policy,
state protocols and borrowing promises. Checking can infer ordinary type
arguments, select available implementation evidence, propagate effects and
retain storage dependencies. It cannot infer a preferred wire schema, whether
an absent field means a default, or whether a runtime number fits a bounded
format scalar. Derived mappings must disclose their conventions and produce
the same checked obligations as manual implementations.

### Expressibility experiment

The first contract corpus should include a generic application ADT, a nested
sequence, a sum type, an opaque nominal with a public custom representation,
and a format-specific scalar. Encode/decode the same eligible application types
in JSON and YAML, then test the other format constraints before freezing the
framework interfaces.

Rust associated types and lifetime bounds do not transfer automatically.
Try explicit state/result/error parameters and relational interfaces first.
Check whether generic visitors or compound builders need constrained
method-local schemes that current Ash does not express. A failing example
becomes a specific design question and potential language proposal, not an
unchecked generated adapter or hidden compiler special case.

Opaque values must be handled by an authorized implementation in their defining
module or an explicit public representation. Derivation must respect visibility
and constructor authority. Live resource handles and provider authority have
no automatic portable serialization: an application may expose ordinary data
such as a path or identifier, but decoding it does not reacquire authority.

### Common data model and format extensions

Start from Ash's actual value forms and library collections. The framework
needs booleans, integers, binary floating point, text, bytes, optional values,
sequences, products, keyed fields and variants. Field names and variant tags
are explicit mappings for positional ADTs, not assumed record reflection.

Exact decimal, dates/times, binary subtypes and other extended scalars can be
library-defined nominal types with custom mappings. Their presence does not
justify adding a compiler primitive for every format tag. A common model must
also allow a format to reject an unsupported category and an application to
select a documented representation.

Determine structural support through checked interfaces where possible. Value
conditions such as an `Int` fitting BSON int32 still require runtime range
checks. Similarly, a valid `String` may violate a format's key restrictions.
Keep these dynamic conditions distinct from evidence that a codec exists.

### Three execution styles

| Style | Use | Cost or limitation to measure |
| --- | --- | --- |
| Materialized document | Inspection and transformations with unknown shape. | A generic tree may duplicate names, strings and numerical representations before building `T`. |
| Direct typed decode/encode | Known application schemas and ordinary library use. | Avoids a mandatory generic tree, but builders, visitors and application values still have costs. |
| Incremental records/events | Filtering, reductions and format conversion as input arrives. | Needs chunk, partial-token, state, error and lifetime contracts; some formats require retained document state. |

A generic document tree is an optional ordinary library type. Direct decoding
must not require it. Event APIs and typed row APIs can share format machinery
without forcing every application to manipulate untyped nodes.

Incremental operations distinguish need-more-input, produced data, completion
and failure. State absolute offsets across chunks and the meaning of trailing
data. A chunk boundary may split a UTF-8 sequence, number, escape or CSV quoted
field; it is not automatically a token or record boundary.

Library collections, byte cursors and output builders are dependencies to
deliver, not existing primitives to assume. Start with the operations the
parsers need: bounded access, incremental accumulation, UTF-8 validation,
numeric conversion and construction of sequences/fields. A full string API or
general collections redesign remains outside the initial scope.

## First-class format contracts

Pin a version and explicit options for every library. A deliberately incomplete
profile must report exclusions and cannot claim full format support.

| Format | Required design pressure | Initial profile questions |
| --- | --- | --- |
| JSON, RFC 8259 | Nested values, string keys, Unicode and numbers beyond a selected numerical target. | Duplicate keys, range/rounding, trailing data and direct/incremental arrays. |
| YAML 1.2.2 | Scalar resolution, tags, anchors, aliases and document structure. | Schema choice, unknown tags, alias preservation/expansion, cycles and retained state. |
| CSV, declared dialect | Rows, headers, textual field conversion, quoting and embedded line breaks. | Column mapping, missing/extra fields, encoding, empty/null distinction and recovery. |
| TOML 1.1.0 | Tables, nested configuration, dates/times and document constraints. | Target mapping, special floats, ordering-independent construction and duplicate definitions. |
| BSON, specification 1.1 | Length-prefixed binary documents, integer widths, doubles, bytes and extended scalar tags. | Range checks, byte order, binary subtypes, decimal128, unknown/deprecated types and output sizing. |

The format contracts derive from their primary descriptions:
[JSON](https://www.rfc-editor.org/rfc/rfc8259.html),
[YAML](https://yaml.org/spec/1.2.2/),
[CSV baseline](https://www.rfc-editor.org/rfc/rfc4180.html),
[TOML](https://toml.io/en/v1.1.0), and
[BSON](https://bsonspec.org/spec.html).

The adapter contract must state unsupported-value behavior. A YAML/TOML
nonfinite float cannot become a JSON number without a selected representation
policy. A BSON decimal must not silently become a binary64 value. CSV's column
mapping needs a schema or explicit conversion; arbitrary nested values do not
gain a universal row representation.

BSON output lengths may require buffering, a sizing pass or a seekable sink.
Compare the costs and make the requirement visible. A sizing pass must not
execute an effectful user mapping twice. YAML aliases and TOML document-wide
constraints may require retained state; a streaming API must report that
requirement rather than promise constant storage for every document.

## Ownership, arenas and borrowing

Owned decoding is the first API. Its result and errors must be independent of
temporary file, input-window and scratch-arena owners. Ordinary immutable
sharing of copied data is permitted; independence does not require gratuitous
deep copying at every binding.

Later distinguish borrowed input, transient callback data and independently
owned output. Serde's deserializer lifetime illustrates the need to tie a
borrowed result to input storage, and its owned decoding separates results from
discarded input. Ash must express the equivalent safety relationship using
its own admitted types and dependencies.
[Deserializer lifetime comparison](https://serde.rs/lifetimes.html)

A file owner is not the owner of bytes already read. A live buffer owner does
not permit refilling while dependent views remain usable. Escaped text may
need newly initialized storage even when unescaped input can be borrowed.
Compound decoded values, closures, evidence methods, errors and captured
continuations must preserve those dependencies.

Gate borrowing on a separately specified access interval and buffer protocol.
An arena result depends on its arena; an explicit independent copy may escape.
Initializing arena objects through parsing needs transactional publication or
an explicit initialized-prefix contract. Immutable arena allocation supplies
no writable-input-buffer permission by itself.

## Errors and laws

Separate syntax errors, schema/type mismatches, numeric conversion failures,
unsupported representations, resource limits and external I/O failures.
Preserve byte offsets, field/variant paths and row/column information where
meaningful. Limit retained snippets and error paths when a bounded pipeline
claims a storage bound.

Specify fail-fast behavior first. Recovery is an explicit format operation,
with a valid resynchronization point; skipping one physical line is not a
general CSV recovery rule. Preserve already emitted output and consumed input
when a later stage fails. Closing a resource does not undo those effects.

Round-trip laws apply to a declared representation domain and equivalence.
Application values need not preserve formatting, comments, original numeric
spelling, alias sharing or byte identity. Floating-point laws use DN-0040's
observations, including signed zero and NaN, rather than assuming ordinary
equality is reflexive. Lossless document editing is a separate profile, with
raw representations retained where needed.

## Semantics, Core and proof obligations

The preferred first account elaborates libraries through current ADTs,
functions, evidence and effects. It adds no JSON/YAML parser node to Core.
If expressibility fails, identify the smallest reusable semantic delta and
return to design/proposal work before implementation.

Each new capability must account for surface typing, module summaries,
elaboration, Core authentication, runtime transitions and the affected
specification. Required obligations include:

- Correct selection and preservation of complete codec/visitor evidence through
  generic calls and separate module checking.
- Construction of a well-typed `T` or an explicit error, with no constructor or
  opaque-representation authority fabricated by schema data or generated code.
- Dependency preservation through owned, transient and borrowed results,
  including continuation capture and cleanup.
- Initialized storage before publication, correct bounds/offset conversion and
  no use after refill, release or access-interval completion.
- Progress of incremental state or a specified need-more/error result; no
  hidden infinite retry when neither input nor output advances.
- Transformation preservation of values, errors, external progress, exact
  effects and completion order.

Manual mappings establish the framework first. Derivation follows only after
their requirements are understood. A derivation mechanism should produce
ordinary checked implementations and preserve origins and visibility. It
needs its own generic design contract; the exploratory macro direction in
[DN-0030](DN-0030-typed-compiler-macros-and-hooks.md) is not an available facility
or current authority about language capabilities.

## Runtime and memory experiments

### Define attributable overhead

The target is zero additional runtime storage for static distinctions that can
erase, and bounded shared metadata where runtime state is necessary. Define
the bound per live pipeline, buffer or owner; do not call a repeated per-value
allocation constant overhead merely because each object has constant size.

Report retained Core, code and static authentication facts as program-resident
storage, separately from per-value state and compiler-phase working memory.
Their absence from source values does not make their physical storage free.
Runtime erasure must preserve the independent validation and provenance
boundaries before execution and after any transformation.

Storage should depend on data and necessary execution state rather than the
complexity of static type expressions or verification evidence. Distinguish:

- Payload, necessary variant tags, alignment and numerical representation.
- Static wrappers, interface/evidence adapters and retained type metadata.
- Collection nodes, builders, cursor state and duplicated document trees.
- Input/output buffers, foreign conversion and bytes copied.
- Closures, environments, handler/continuation state and completion metadata.
- Unreachable retained storage, including state outside arena payload bounds.

The current evaluator heap does not supply a source-level collection policy.
Discarding a row or closing an arena does not, by itself, establish that all
ordinary wrapper, environment or control storage is reclaimed. Measure those
costs. A collector or new storage regime requires separate authorized design
if evidence makes it necessary; it is not introduced silently by this library.

### Comparison method

Compare equivalent concrete and generic Ash pipelines with the same data,
representation, effects and error behavior. Vary erased wrappers and generic
constraints while keeping payload representation fixed. Then vary input size,
record width, nesting, escaped-text frequency, buffer size and retained output.

Use a native implementation as an additional absolute baseline after the Ash
comparison. A native/interpreter gap alone cannot identify rich-type overhead.
Measure wall time/throughput, allocation count and bytes, peak live and retained
storage, copies, metadata, stack/control depth and teardown work. Measure
compile/check time and generated-code size separately when relevant.

For a streaming filter or fixed-state reduction, aim for memory governed by
buffer/token limits, nesting and processing state rather than total row count.
An aggregation by distinct keys, a full output collection or a retained YAML
graph has an additional data-dependent bound. State it. Include native buffers
and runtime metadata; an arena capacity alone is not an execution-memory bound.

### Improvement candidates

Investigate only costs demonstrated by the pipelines. Candidate improvements
include direct typed construction, shared immutable byte backing, packed
collections, immediate scalars, arena scratch batches, builder/cursor reuse,
elimination of redundant evidence adapters and validated specialization or
fusion. None is selected in advance.

Specialization remains optional after evidence-passing execution works. It
must preserve independent checking and body-free module contracts, and its
runtime gain must be weighed against compile time and code growth. Fusion must
preserve error timing, effect order, hooks and resource completion. Borrowing
is admitted only after its access contract; unsafe views are not a performance
result. Keep configured compiler/runtime limits visible and unchanged for
baseline comparisons.

Zero or near-zero type overhead is a design target, not an unmeasured claim or
a requirement to delay every usable library delivery. Each checkpoint reports
its achieved bound and remaining costs. Select numerical acceptance targets
from the first measurements before declaring the runtime goal complete.

## Evidence and executable delivery order

Use connected feature batches and public e2e/integration evidence. Focused
parser, numeric and adapter tests remain useful for demonstrated defects and
conformance boundaries. Batch builds and checks instead of testing every small
edit. A performance claim requires a reproducible workload and counter data.

| Delivery | Ash can execute | Dependencies and gate |
| --- | --- | --- |
| S-0: framework contract | Small manually mapped application types across candidate format interfaces. | Current interface/method schemes; resolve expressibility gaps and profile matrix before freezing APIs. |
| S-1: owned JSON | Decode, process and encode nested typed data in memory, with explicit numeric and Unicode policy. | Minimal Bytes/String/cursor/builder/collection facilities; Float delivery for numerical cases. |
| S-2: owned YAML | The same eligible application types use YAML through the framework. | Defined YAML schema, tags/aliases coverage and errors; no change to application codec just to select another eligible format. |
| S-3: incremental CSV | Parse typed rows, filter and reduce, then emit a JSON array incrementally. | Declared CSV dialect and row mapping; chunk/progress contract and measured memory bounds. |
| S-4: TOML and BSON | Typed configuration processing and binary document transformations. | Date/time and extended-value mappings, integer ranges, lengths and binary conversion; Float64 for double processing. |
| S-5: file pipelines | Read real files, decode, transform, encode, write and observe completion. | DN-0039 copying interface; preserve partial output and independent owned results. |
| S-6: derivation | Generate checked mappings equivalent to the manual corpus. | Separately accepted generic derivation contract, visibility/origin checks and diagnostic evidence. |
| S-7: scoped storage | Arena batches and eligible borrowed fields reduce measured copying. | Agreed arena layout/initialization and access-interval contracts, including negative escape/refill cases. |
| S-8: measured runtime changes | Equivalent pipelines run with demonstrated storage or execution improvements. | A cost reproducer, semantic/validation review, targeted regressions and fresh comparison measurements. |

S-3 and S-4 can proceed independently after the shared framework contracts are
stable. File copying can develop alongside in-memory libraries. Derivation and
runtime work need not delay manual owned APIs. Scope/profile completion is
recorded for every format; JSON/YAML success does not complete the five-format
workstream or establish full YAML support.

Representative public programs include generic nested values in JSON and YAML;
YAML/TOML configuration decoding, validation and JSON output; CSV typed rows
with Float64 processing, filtering/reduction and JSON output; and BSON typed
transformations with integers, doubles and binary payloads. Define framing when
a file contains several binary documents. Later compose scoped arena batches
and measure them against the same owned programs.

Negative cases include malformed/truncated input, invalid Unicode, numbers out
of the requested range, missing/duplicate/unknown fields under the selected
policy, unsupported format categories, mismatched codec evidence, opaque
constructor access, buffer escape, refill during a live borrow and partial
output failure. Deliberately vary chunk boundaries through tokens and test
source/linked/Core validation where a new semantic capability requires it.

## Coordination, tools and adoption

Keep these contracts separate from the common, SQLite and arena active task
scope. Import verified checkpoints and agree one owner for each shared compiler
seam. An independent format library should not wait for the entire SQLite
provider, arena borrowing or the Ash-only FFI authoring program.

Authoring tools should provide schema/evidence diagnostics, field and input
locations, checked generated-code inspection, a conformance fixture runner,
chunk-boundary execution, conversion diagnostics and allocation/copy profiles.
Provide a library blueprint covering manual mappings, format modules,
incremental state, errors, effects, resource composition, derivation and
measurements. A foreign parser backend, if separately chosen, uses DN-0037's
binding contract; it does not replace checked Ash application mappings or
require a format-specific compiler entry point.

A later tasked prototype tests framework expressibility and costs within its
declared profile. Retain successful modules and reusable evidence. Revise the
design before expanding a failed contract; do not merge an unsuccessful
experiment or hide missing semantics in runtime special cases.

Language changes follow proposals, tasks, implementation, tests, specification
updates and relevant proof work. Accepted non-language architecture follows
decisions. Standard-library adoption additionally requires declared format
coverage, executable examples, authoring documentation, compatibility/error
policy and measured costs. This note is design preparation, not an execution
plan or a claim of implemented serialization.

## Open questions

- Can the needed generic visitors/builders be expressed with current rank-1
  method schemes and relational interfaces, and which counterexample requires
  a reusable extension?
- Which field/variant schema conventions are useful for positional Ash ADTs?
- What exact format profiles and extension-preservation policies should each
  first delivery promise?
- Which cursor/builder/collection representations enable the first APIs with
  acceptable measured costs?
- What input and access types express transient versus retained borrowed data
  without transporting storage owners?
- Which costs are removable through ordinary library design, and which justify
  changes to the evaluator or validated transformations?
- What storage and throughput targets should the baseline measurements support
  for fixed-state, retained-document and key-aggregation workloads?
