# Safe non-foreign resource scope

This informative report records the safe-resource checkpoint retained on
`integration/effect-ash-foundations` by unsigned local merge `b8a5398`, above
integration baseline `387c4ef`. Implementation, independent reviews, full
verification, transition cleanup and verified local integration are complete.
The branch specification is prospective until separate integration into `main`.

## Retained boundary

The accepted scope is one mutable integer cell per acquisition, reusable access
while live, scope-owned release and rejection of resource-dependent escape.
It adds no general ownership language, cleanup callback, foreign resource or
escaping continuation. The [branch specification](../../../spec/README.md)
owns the intended resulting semantics; this report records evidence, not rules.

Unsigned local checkpoints retain corrected effect instantiation (`8810a44`),
the sealed API and syntax (`0ae5203`), acquisition typing and Core authority
(`64647d8`), and stored dependencies and scope completion (`a841d46`). The
complete runtime, interaction, specification and verification checkpoint is
`fff611c`. It retains the accepted proposal, task and execution plan in Git;
cleanup commit `ca3922c` removes those completed transition documents from the
active tree. Merge `b8a5398` retains that exact product tree.
No remote push, tag or main integration is part of this work.

## Cross-stage evidence

| Boundary | Evidence retained in the product tree |
| --- | --- |
| Syntax and scope | [Resource syntax tests](../../../tests/resource_scope_syntax.rs) cover the reserved keyword, contextual `cell`, one identity/handle, primary initializer, block scope, malformed forms and bounded nesting. |
| Builtin origin | [Module tests](../../../tests/resource_scope_modules.rs) cover fixed imports, reserved-root precedence, renamed/facade identity, direct acquisition availability, fake APIs, sealed provider introduction and inaccessible constructors. |
| Lifetime and control | [Typing tests](../../../tests/resource_scope_typing.rs) pair hidden closure/evidence/aggregate escape and outward dependent payload rejection with copied results, selected fields, constant closures, live outer dependencies and safe inside-scope discard. |
| Execution | [Runtime tests](../../../tests/resource_scope_runtime.rs) observe read/write, reusable captures, aliases, nested and sequential release, initializer order, exact user interception, capture/resume, imported factories and same-site lexical activation. |
| Published entry | [Core entry tests](../../../tests/resource_scope_core.rs) execute accepted resource modules after independent validation instead of retaining a transitional execution guard. |
| Independent reconstruction | Core validator units reconstruct resource relationships after identity and folding rebuilds, reject authority/identity/owner tampering and run rebuilt imported row-relay programs to `42`. |
| Documented tool use | `resource_cell_documentation_example_has_exact_cli_output` in [the specification harness](../../../tests/spec_examples.rs) checks the exact documented source, exit status, output and empty stderr. |

Stored dependencies and request-carried completion obligations remain separate.
Finite value relationships preserve selected fields, known calls, recursive
activations and imported factories. Owner-relative payload checking does not
reject an outer dependency merely because it crosses an unrelated inner scope.
Resource analysis runs without discard as well as with it. Final Core derives
these properties from actual linked structure rather than trusting a source
permission or transformed summary.

## Corrections exposed by abstraction and review

- Strict inputs previously allowed an unexecuted expression result to enter
  the dependency analysis after discard. Value-reader wakeups now publish the
  result only after required children complete. Paired source tests cover call,
  match, tuple, primitive and resource-initializer forms.
- An imported cell accessor worked directly but failed through a row-generic
  tuple relay. The actual callback kept tail `E` while call-context matching
  substituted only ordinary types. Exact per-row-variable facts now expand the
  referenced tail before matching; independent rows, handled prefixes, lacks,
  conflicting equations and canonical empty rows keep their own meanings.
  Four unchanged local/imported CLI witnesses now return `42`, with outward
  payload and skipped-completion negatives preserved.
- Row-context retention uses the existing finite universe of original type
  subtrees. A derived argument outside that universe remains unproved rather
  than growing recursive contexts indefinitely. This is not a handler-match
  exception based on a handle's owner.
- Resource review exposed uncharged width at seven staging seams and a deep
  method type temporarily outside its iterative owner. Boundary regressions
  and an actual pre-fix small-stack abort were retained; the corrected method
  root guards its body before the fallible parameter copy.
- Row-specific self-review exposed two nullary known/lacks scans with no
  owning visit charge. Each isolated test failed before correction and passed
  after precharging its traversal. No default work or stack limit was raised.
- Final Rust/resource review exposed an uncharged formal-row scan when the
  actual callback was pure or had an unresolved tail: widths 1 and 4,096 cost
  the same 7 or 12 units. The correction precharges formal width and removes
  its duplicate per-iteration charge on the closed-actual path. The durable
  test covers insufficient prefix, exact/one-short limits, two fresh retries
  and failure without context/cache publication. Re-review approves the fix
  and independently passes the regression and all 22 control tests.
- The full gate exposed excessive fixed stack usage in Pure elaboration.
  Four resource/perform phases now run in small helpers with the same order,
  charges and boxed owners. The original 256 KiB synthesized-wrapper witness
  passes without a stack or depth increase.
- Three unchanged large Pure programs exhausted type work during portable
  capture publication. A precharged consumer check now skips publication only
  when no local public term or implementation method needs it. Any demand
  retains the complete graph, including private helpers; every Effect proof
  remains enabled. Exact/retry controls and all three predecessors pass.
- An exported closure factory retained a lexical nominal in its graph, but
  import admission incorrectly demanded an ordinary hidden nominal fact for
  it. Capture-only metadata walkers now inventory external nonlexical facts
  while preserving complete graph types and embedded effects. Ordinary scheme
  admission, lexical-escape rejection and graph authentication remain strict.
  The original factory, generic facade/diamond routes and implementation
  factories pass alongside resource-escape and missing-metadata controls.
  The architecture inventory follows the two borrowed traversal fields into
  their renamed helper without changing ownership classifications.

## Runtime ownership and resource bounds

The explicit machine's resource boundary owns the mutable integer. Runtime
handles contain only private activation keys. A lexical instantiation binds
the validated static identity to that activation, including through type and
row substitutions; neither source types nor validated Core contain an
execution-created inference variable. An Effect metadata negative independently
rejects such a variable at the type-scope boundary.

Live-cell usage equals active resource frames plus resource frames owned by
captured continuations. Acquisition increments it once after all preparation;
normal release decrements it once. Capture and resume move frames without
changing the count. Discard preflights actual retained live owners before
consuming a capture. Static proof, not runtime body inspection, accounts for
required completion outside the discarded segment. Final observation rejects
nonzero resource or captured-control accounting.

Machine tests cover exact two-live capacity, one-short failure, fresh retries,
capacity reuse after release, and a captured outer cell still counting while
an inner cell is acquired. Failed context preparation and malformed key,
operation or operand checks publish no partial acquisition or mutation. A
copied closure retaining an unused handle entry does not retain payload
ownership or consume released capacity.

A durable fresh-process test executes 24 nested source acquisitions on a
256 KiB stack. Owning tests also exercise 32,000-frame normal completion and
failed capture disposal. Compiler tests cover exact work, one-short failures,
fresh retries, wide scans and deep iterative disposal. Internal type-work
accounting is not the milestone's notional work-unit scale; the production
type-work ceiling remains 327,680.

Resource-free Pure execution adds no resource registry, resource frame or live
cell. The fixed Effect carrier and saved lexical instantiation do not create
a machine-global provider lookup, global substitution or general store API.

## Verification and closure

The final focused gate passes 1,099 library tests, 53 scoped-evidence interaction
tests, 20 local-newtype tests, two interface-validation tests, 61 resource typing
tests and 14 resource runtime tests, plus both fresh-process children.
Strict Clippy, formatting and diff checks pass. The parent independently repeats
the new owning and factory tests. All five predecessors exposed by the first
full gate now pass unchanged: one stack failure, three type-work failures and
the closure-factory metadata failure. Their corrections are recorded above.

The medium-reasoning documentation audit covers all eight specification/tool
areas and resolves all 188 local links, including anchors. Re-review approves
three corrections: resource handles in the runtime-value inventory, the
resource carrier in the exhaustive Core list, and source-handler selection
only when no nearer cell interpreter accepts the request.

Fresh high-reasoning semantic review covers the entire accepted resource
contract and finds no product semantic defect. Its imported opaque transport
probes all behave correctly: three execute to `42`, while two hidden closure
or selected-evidence payload escapes reject `type.resource-escape`. The parent
independently repeats all five. The exact sources and helper are now retained
in five driver-backed typing tests. Their focused run and full library/typing
gate pass; semantic re-review approves the retention and closes the evidence
gap. The typing suite now contains 61 tests plus its small-stack child.

Final semantic and Rust/resource reviews approve each correction with no
remaining actionable finding. The complete
`CARGO_INCREMENTAL=0 cargo xtask verify` gate passes 2,365 top-level tests in
67 binaries, plus two reported resource child runs. All 32 architecture checks,
formatting, metadata, build, strict Clippy and warning-denied rustdoc pass.
The parent confirms the verified source, test and specification surface stayed
unchanged from the reviewed tree.
Transition cleanup removes only the completed resource proposal, task and
execution plan, with their index entries. Fresh verification on the unsigned
local merge passes 1,450 top-level tests in 16 binaries, plus two reported
resource child runs: the library and 15 resource, effect, abstraction and
documented-example suites. The merged product tree is identical to the verified
feature tip. The completed feature worktree and branch are removed after a
clean-checkout and retained-ancestry check; the integration checkout is the
continuation point. Existing main-checkout changes, remote refs and tags remain
untouched.

## Downstream reassessment

The implementation keeps provider introduction distinct from ordinary
interface selection and future proof evidence. Static identities, dynamic
activation keys, stored dependencies and release ownership are separate.
Future existential packaging would need an explicit ownership-transfer and
elimination contract; this slice permits no escaping package and claims no
such transfer. Hooks and reliable cleanup would need their own exit and failure
semantics, rather than reinterpreting discard as cleanup. Fresh semantic review
finds no demonstrated contradiction from proof, existential or hook pressure
and no additional machinery justified for this checkpoint. This is not a
promise of zero future refactoring.
