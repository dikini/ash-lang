# DN-0057: Checked FFI Module Boundaries

- ID: `DN-0057`
- Status: exploring
- Related: [DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0036](DN-0036-foreign-library-and-memory-provider-experiments.md),
  [DN-0018](DN-0018-runtime-established-static-evidence.md),
  [DN-0042](DN-0042-native-interaction-and-efficient-data.md),
  [DN-0054](DN-0054-base-lexical-region-memory-contracts.md)

> This design note is informative. It defines no current Ash semantics,
> accepts no architecture and authorizes no product implementation.

## Question

How can an FFI module export checked Ash values and operations when declarations
cannot guarantee what the foreign implementation delivers? Which obligations
can conversions, resource monitors and isolation enforce, and which remain
explicit native assumptions? How can later laws, proofs and tests strengthen
the evidence without changing the meaning of the exported contract?

## Context

The [current specification](../../spec/README.md) provides passive modules,
opaque exports, ordinary typed values, effects and scoped builtin resources.
It supplies no general FFI or foreign-representation guarantee. Module access
rules erase; this note does not propose a runtime module object. Proposed
boundary checks would execute in binding operations and conversion paths.

[DN-0037](DN-0037-ash-authored-foreign-library-interfaces.md) separates foreign
signatures, representations, conversions, ownership and public binding
contracts. A matching ABI declaration does not establish retention,
invalidation or consumption behavior. The
[readiness analysis](foreign-authoring/dn-0036-readiness.md) identifies
transferable experimental evidence: checked copies, guarded publication,
authenticated resources, completion dispositions and retained-owner quarantine.
Those mechanisms still rely on trusted native adapters and declared foreign
behavior. They do not establish general FFI safety.

Gradual typing supplies a useful comparison: crossing a boundary introduces
checks, and higher-order values require checks during subsequent interaction.
The [type-directed gradual-typing study](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/typedirected-operational-semantics-for-gradual-typing/23C24089997FFBD4FA74409892D244BD)
describes deferred higher-order checking and blame. This note borrows that
boundary discipline without selecting a general dynamic type, implicit casts
or a gradually typed Ash language.

Native execution adds a separate problem: foreign code can corrupt memory
before a result check runs. The
[Racket FFI safety discussion](https://docs.racket-lang.org/rhombus-ffi/unsafe.html)
likewise distinguishes a safe client interface from the unsafe native boundary.
Contracts over returned values cannot alone contain arbitrary native execution.

## Constraints

State each export's actual promise. Distinguish valid Ash representation,
application invariants, resource access, native memory safety, containment,
external effects and functional correctness. Success in one category does not
establish the others.

Keep every remaining native assumption explicit at its owning foreign
declaration or primitive. Client-facing contract information must expose the
assumptions on which its guarantees depend, including transitive dependencies.
Whether this uses compiler metadata, documentation or another checked form
remains open. Export opacity must not hide an assumption's existence.

Ordinary names, constructors, nominal wrappers and foreign declarations cannot
manufacture validation, ownership, completion or proof authority. Checked
conversion must establish the fact represented by a validated wrapper.

Preserve passive imports, exact defining identities, checked effects and
resource dependencies, and independent Core validation. Boundary failure does
not imply rollback of foreign side effects or successful native cleanup.

## Candidate directions

All three approaches belong to the intended design scope. Start exploration
with checked conversions and monitored resources; retain isolation as a
required approach for containing faulty native implementations. They compose
and address different obligations, rather than forming one safety ranking.

### Checked conversions

Decode and validate a foreign result before publishing an Ash value. Prefer
independent Ash-owned copies for the first data cases. A conversion returns
either a value satisfying its contract or an explicit boundary failure.
Do not expose partially constructed values.

Candidate checks include integer ranges, enum tags, lengths, encoding,
structural invariants and bounded application predicates. Opaque exports can
restrict construction of values whose invariants were established by those
checks. Reuse ordinary conversion functions, result types and module opacity
where sufficient; a new dynamic type is not a prerequisite.

A SQLite text result is a useful example: establish the permitted copy window,
obtain length and bytes under that contract, validate encoding, then publish
an independent value. Distinguish null, empty data and conversion failure.
Later native mutation must not invalidate the published copy.

Null and length checks do not prove that an arbitrary native address is
readable or initialized. Copying requires a valid source interval while the
copy executes. In-process conversion therefore retains native assumptions
about the call, memory access and bridge implementation. Its guarantee is
conditional on those assumptions.

### Monitored resources

Keep foreign resources opaque and mediate their operations. An initial check
cannot establish all future behavior of a connection, iterator, callable or
mutable view. Check each relevant interaction against an authenticated resource
identity, live activation, permitted protocol state, arguments and results.
Record state transitions only according to the operation's completion contract.

Reuse static scope and dependency checking where it establishes an obligation;
add runtime monitoring for facts available only during execution. Validate
results before publication and reject forbidden access before native entry.
Completion must distinguish actual consumption, refusal and retained state.
Unknown consumption must not silently permit reuse or release of backing data.
Quarantine preserves required storage; it does not extend source access.

For mutable data, either publish an independent snapshot or protect the
validation interval against invalidating mutation. Recheck on use where
appropriate. A monitor cannot enforce native retention or aliasing behavior
that it cannot observe or control.

Higher-order contracts motivate later callback checks over arguments, results,
invocation state and lifetime. Callbacks, reentrancy and asynchronous execution
need separately bounded contracts; this note does not add them to the initial
synchronous FFI scope.

Boundary diagnostics should identify the operation, violated obligation and
observed condition. Distinguish rejected client input from a foreign result
that violates its declaration. Attribution beyond observed facts requires its
own evidence; a diagnostic cannot reliably identify arbitrary native corruption.

### Isolated foreign execution

Execute native work in a separate process or another boundary with stated
containment guarantees. Exchange bounded, validated messages and expose opaque
remote resource identities. Checked conversion and protocol monitoring still
apply to replies and remote operations.

Compare malformed replies, worker termination, stale handles, timeouts,
resource exhaustion and interrupted operations. A failed worker invalidates
its associated resource session; stale identities must not regain authority
after restart. Define what the caller can conclude about completion when a
reply is lost. Do not retry an operation with external effects merely because
its result is unknown.

Isolation can contain native memory faults under the selected platform's
guarantees. Restricted filesystem, network and other authority is a separate
part of the containment contract. Isolation does not establish answer
correctness, termination or rollback. Shared native memory requires additional
access contracts and must not silently bypass the validated message boundary.

The concrete process or sandbox mechanism, transport and deployment support
remain open. Measure transport, copying, startup and recovery costs against
the containment obtained.

### Explicit assumptions and stronger evidence

Track evidence per obligation. For example, a result range may be checked on
every return, liveness may combine static scopes with runtime identities, and
non-retention may remain a native assumption. Avoid one module-wide label that
conceals these differences.

| Evidence | Contribution and limit |
| --- | --- |
| Foreign declaration | States an assumption; does not verify the implementation. |
| Runtime check or monitor | Establishes an observable property for the checked value or interaction under its own execution assumptions. |
| Law | States a relationship that implementations should satisfy; requires evidence. |
| Tests, including generated cases | Exercise the relationship and retain counterexamples; do not establish universal validity. |
| Proof | Establishes a stated obligation within a model and assumptions; applicability to the executed artifact remains a separate obligation. |
| Isolation evidence | Establishes bounded containment properties for a specified execution configuration. |

Later evidence may discharge an assumption or justify removing a redundant
check only when it establishes the same obligation. Tie evidence to the
relevant contract, implementation, ABI and build configuration. A proof of
the wrapper does not prove an arbitrary loaded binary correct. Tests alone
do not authorize treating an assumed property as proved. Changed native
artifacts require reconsidering evidence whose applicability depended on them.

The intended export promise is that published values satisfy their Ash
contracts and mediated operations enforce their stated checks, conditional on
listed assumptions. Isolation adds a separately stated containment promise.
Stronger evidence should refine those assumptions without weakening the
client's contract.

## Evidence and experiments

The [minimal contract cases](foreign-authoring/minimal-ffi-contract-cases.md)
work through a copied SQLite text result and a connection/statement lifecycle
in both execution modes. Their linked refinements resolve the four identified
blockers at proposed design level before syntax, with implementation evidence
still required. They distinguish common FFI contracts from the selected Linux
ABI and executor profile; other platforms supply their own realizations.

The [canonical transitions](foreign-authoring/minimal-ffi-transitions.md) own
outcome precedence, exhaustion domains and both worked lifecycles. The
[SQLite policy](foreign-authoring/minimal-ffi-sqlite-policy.md) owns portable
library facts, separately from target ABI and executor profiles. The
[consistency review](foreign-authoring/minimal-ffi-consistency-review.md)
records these proposed resolutions and the remaining platform-acceptance gaps.

Compare the three approaches on a copying data operation and a stateful
resource operation. SQLite copying and connection/statement lifecycle cases
provide existing pressure without making a wider borrowing design mandatory.

| Case | Required observation |
| --- | --- |
| Invalid range, tag, length or encoding | Explicit failure; no invalid or partial Ash value is published. |
| Native data changes after successful conversion | Independent copied output remains valid. |
| Stale resource, wrong identity or forbidden transition | Rejection before native entry; no new authority appears. |
| Native retention, close refusal or uncertain consumption | Dependencies remain protected; failure does not claim release. |
| Malformed reply, worker crash or restart | No unchecked reply reaches clients; old resource identities remain invalid. |
| Lost reply after an external effect | Outcome remains explicitly uncertain; no automatic duplicate operation. |
| Native memory fault | In-process limits are documented; the isolated comparison tests the selected containment guarantee. |
| Changed native artifact or removed runtime check | Evidence applicability is reassessed; removal needs evidence for the same obligation. |

Compare client contracts, diagnostics, remaining assumptions, authoring effort,
compiler/Core obligations, copies, runtime monitoring and isolation costs.
Reuse existing experimental evidence only within its tested scope. Native
fault injection belongs in a contained test process.

Any later prototype must select a bounded question from these comparisons,
state its native profile and trust boundary, and define positive and negative
cases before implementation. Retain reproducible comparisons and
counterexamples as design evidence; discard or replace machinery that fails
the comparison. Retention does not establish product semantics. Language
changes require a change proposal; converged non-language architecture needs
an architectural decision and authorized delivery work.

## Open questions

- What contract representation distinguishes checked facts, monitored
  obligations and transitive native assumptions without duplicating signatures?
- Which checks can ordinary Ash wrappers express, and which require
  authenticated bridge or Core operations?
- What is the smallest monitored lifecycle that transfers from SQLite to a
  contrasting native resource?
- Which isolation profile supplies useful containment first, and how should
  interrupted operations and remote completion appear in exported APIs?
- How should later evidence identify its contract and native artifact, and
  which obligations justify check elimination?
- Which borrowed or shared-memory paths preserve the export promise without
  relying on unobservable foreign mutation and retention behavior?
