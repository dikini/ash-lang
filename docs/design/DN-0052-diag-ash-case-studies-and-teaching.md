# DN-0052: Diag Ash Case Studies and Teaching

- ID: `DN-0052`
- Status: exploring
- Related: [DN-0024: Executable Learning and Evidence Stream](DN-0024-executable-learning-and-evidence-stream.md),
  [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md),
  [DN-0029: Human Diagnostic Presentation](DN-0029-human-diagnostic-presentation.md),
  [DN-0031: Resource Composition Concept Map](DN-0031-resource-composition-concept-map.md),
  [DN-0041: Typed Serialization and Data Pipelines](DN-0041-typed-serialization-and-data-pipelines.md),
  [DN-0047: ECS and Open Heterogeneous Stores](DN-0047-ecs-and-open-heterogeneous-stores.md),
  [AD-0010: Human Diagnostic Presentation and Localization](../decisions/AD-0010-human-diagnostic-presentation-and-localization.md)

> This design note is informative. It guides the selection and development of
> ash-doc teaching material for an implemented checkpoint. It defines no Ash
> semantics, accepts no architecture, and reports no new executable case results.
> The proposed studies require development and verification in ash-doc.

## Question

Which case studies can teach useful program design in Diag Ash while exposing
concrete language, library, diagnostic and implementation pressure? How should
ash-doc develop them without repeating its existing lessons or presenting
future Ash as available behavior?

## Context

The target is `diag-ash`, commit
`9ec5920e8c395f9a36125805ee93b7f58c0f4764`. This cumulative checkpoint includes
Effect Ash, compiler repairs and improved diagnostics. Its [specification][spec]
owns all language claims in these studies; its [tool guide][tool] owns the
documented invocation and diagnostic controls. Newer `main` experiments and
worktree implementations are outside this target.

The inspected [ash-doc snapshot][ash-doc] is commit
`0b6b9c8a9fba9e9b87f0c8c047001743e81682c1`. Its README reports thirteen Learn,
eight Libraries, twelve Effects and twenty Cases lessons verified at the Diag
Ash pin. This is an inventory of retained documentation evidence, not a fresh
compiler or documentation test run. Its [Cases index][cases] already covers
stateful traversal, requested prices, scripted sessions, search budgets,
buffer-backed decoding and synchronous hook pipelines. Its [Libraries][libraries]
and [Effects][effects] paths introduce their constituent language mechanisms.

The opportunity is to develop interactions and application invariants. Cleanup
lessons trace closing but do not collect typed cleanup failures alongside a
primary outcome. Scoped-evidence lessons use small local examples. No existing
Case develops sorting or a heterogeneous application world. A new decoder or
hook example needs a distinct question beyond the existing pipeline mechanics.

Historical discussions in the sibling `ash/docs` tree supply problem ideas.
The [historical source snapshot][historical] is commit
`f5316f952ee2c0fa7306d864d7f78edfe02d6d42`. Historical syntax, ownership claims,
protocol rules and runtime facilities have no authority for this edition.
Adapt the problem and comparison, then derive its Ash account from the pin.

## Constraints

- Use the target's rank-1 values, nominal data, tuples, newtypes, interfaces,
  scoped exact evidence, passive modules, exact effects, one-shot handlers,
  builtin cells and native buffers, synchronous hooks and cleanup.
- Express bytes as checked integers and ordinary nominal collections. Do not
  depend on experimental `Bytes` or `String`, general foreign declarations,
  library-defined resources, Arena storage, files, networking or Float.
- Keep cell handles reusable and completion scope-owned. Neither an ordinary
  wrapper nor a handler establishes general linearity, borrowing, typestate
  consumption, proof authority or ownership transfer.
- Keep control synchronous. A worker or transaction simulation may use scripted
  decisions and checked discard; it supplies no scheduler, mailbox, escaping
  suspension, concurrent cancellation or native transaction guarantee.
- Derive each public operation's type from the chosen data and invariant.
  Prefer ordinary library definitions where the existing language suffices.
  Record a blocked design as pressure instead of changing the language locally.
- Separate static guarantees, runtime validation, application invariants and
  measured costs. A well-typed program can sort incorrectly, log a secret or
  implement an invalid protocol.

## Candidate directions

Three formats merit comparison:

- A focused teaching extension isolates one new rule or diagnostic repair with
  few prerequisites. It can repeat an existing lesson without adding a
  program-design question.
- An application case study develops meaningful data, operations, invariants
  and interacting features. It can introduce too many mechanisms before the
  reader has a working model.
- A paired model and implementation compares a pure reference calculation with
  an effectful or alternative implementation. It needs an independent comparison
  and a clear account of what agreement establishes.

The leading direction combines these formats: an application question owns the
study, smaller examples introduce its unfamiliar boundary, and a reference
model or contrasting implementation supplies evidence where useful. Diagnostics
explain mistakes arising from that development rather than forming an unrelated
catalogue of errors.

### First development batch

Start with cleanup reporting, scoped pricing and immutable ECS. They cover
completion, local abstraction and application architecture with distinct
questions. This is a suggested order; ash-doc owns assignments, lesson placement
and acceptance. It is not an authorized implementation plan or a requirement to
finish one family before starting another.

### Preserve the primary outcome when cleanup fails

Develop a batch calculation that returns an ordinary success or primary error
while nested cleanup actions report their own failures. Retain the body outcome
and ordered cleanup errors separately. For example, body failure `7` and reports
`22`, then `11`, must preserve all three observations; a successful body must
also survive those reports. Give a finite batch of domain commands a separate
rejection type and name its modeled completion failures in ordinary ADTs.
Develop the report API and its caller's error policy; the pinned tool already
demonstrates the numerical reporting mechanism.

The [specified reporting pattern][cleanup-reporting] resumes each report so the
running action and later actions can finish. Compare it with a reporting handler
that attempts to discard required completion, and with a well-typed program
that constructs an error value but never reports it. Capture the actual
rejection for the former and explain the observed result of the latter.

Use the [cleanup lesson][cleanup-lesson] as a prerequisite. Check normal return,
owned abandonment, no failures, several failures and distinct error categories
combined through an explicit sum. Explain reporting separately from native
release, retries and internal host termination. All completion effects in this
first case are source-level models. The pressure is reusable error reporting and
composition without losing the application's primary result.

### Supply a local pricing policy

Extend [requested order prices][pricing-lesson] with distinct nominal money and
quantity types, then a local nominal policy key whose exact methods capture
configuration such as an integer tariff. Compare explicit function arguments,
selected imported evidence and sequential local `with` evidence. An ordinary
effect handler may supply configuration before that policy is established.

Follow [scoped evidence][evidence-lesson] and the [pinned static rules][static].
The complete evidence selection key must contain the active local nominal.
Use scaled integer arithmetic with a documented domain; do not assume Float,
division, units-of-measure inference or runtime-fresh nominal identity.
An identity-free closure may retain already selected methods, but does not
export an evidence fact for selection by its caller.

Develop mistakes involving mixed nominal units, a constrained call before its
local evidence is available, and an outward result exposing the local type.
Return an ordinary quote whose type contains no local identity. Compare two
configurations and a nested policy without treating lexical evidence as global
implementation search. The [historical domain-primitives discussion][newtypes]
supplies motivation, not a newtype or proof contract.

### Query an immutable ECS world

Represent a world with named position and velocity stores backed by ordinary
immutable collections. Join by entity identifier, run a movement system and
retain the original world as a snapshot. Use explicit component and query-result
types. Begin with a small fixed schema whose expected rows are independently
enumerated.

[DN-0047](DN-0047-ecs-and-open-heterogeneous-stores.md#typed-immutable-stores-and-generic-systems)
suggests a `StoreAccess<W, C>` relationship with both parameters in the key.
One world has several component types, so a determination edge `W -> C` would
state the wrong relationship. The method argument or result context must fix
the requested component type. Missing selected store evidence and mismatched
component values are useful candidate diagnostic episodes.

Compare direct world-specific functions with a generic system. Check absent
components, identifier joins, preservation of the old world and repeated steps.
Explain the lookup and rebuilding work of the actual representation. Automatic
type-index search, associated-output projections, open registries, arbitrary
mutable component stores and efficient packed layout remain outside this case.
An optional heterogeneous-path extension must respect the pinned determination
coverage and decreasing-prerequisite rules; it is not needed by the first world.

### Make rollback explicit in a cancellable journal

Snapshot an integer cell, perform staged updates and either commit or request
cancellation. An explicit cleanup action restores uncommitted state. Observe
final state and closing order for normal completion, cancellation and nesting.
The [historical state/error composition question][journal] motivates comparing
the same work under different handler placement.

Use this to teach the difference between abandoning remaining control and
undoing earlier mutation. Compare an action whose required interpreter remains
around its owner with one depending on an interpreter removed by abandonment;
develop the latter as a diagnostic repair. Start from the scoped-cell and
cleanup lessons. This is an in-memory application protocol with explicit
compensation, without database isolation or automatic rollback semantics.

### Redact before publishing an observable event

Define internal and public event ADTs, project a public view and publish it
through synchronous transformations. Compare audit collection before and after
projection or redaction using a fixture whose sensitive field has an unmistakable
value. Keep observations as returned ordinary data.

The [historical observer/subject/view distinction][observability] motivates the
question. The existing [hook pipeline][hook-lesson] supplies prerequisites.
The [pinned hook contract][hooks] requires endomorphic publication. A proposed
type-changing registration should instead project before publication or use a
separate hook for the public type. Check ordering and nested-root isolation.

Explain which module interfaces prevent passing an internal event to the public
collector, and which redaction properties still depend on application code.
Do not imply runtime introspection, observer grants or automatic secrecy. A
well-typed collector installed too early is an important runtime counterexample.

### Check a worker's proposed edits

Build a deterministic worker that proposes edits to an integer list and a
controller that checks permitted positions and the resulting artifact. Compare
accepted traces with an independent pure model. The [historical controlled-edit
example][worker] supplies the problem; a local script supplies all decisions.

Develop allow, reject and cancellation branches. A continuation resumed twice,
or left unconsumed on a normally completing branch, is a candidate diagnostic
episode. Repair it using exactly one permitted resume or owned discard.
Separately test a well-typed controller that approves an invalid edit: continuation
safety does not establish the controller's policy.

This extends the scripted-session idea with an independently checked artifact
and an explicit authorization boundary. It simulates a worker/controller
interaction; it executes no LLM, process, external tool, filesystem or sandbox.
The pressure is how much of a useful control contract can remain ordinary data,
functions, effects and tests before separate execution authority is needed.

### Cancel a stable sorter without claiming a sorted partial result

Sort records with a finite priority and an identifier, preserving input order
among equal priorities. A finite nominal priority avoids assuming additional
primitive comparisons. Define a result that distinguishes a complete sorted
sequence from cancellation. Supply permission through a synchronous scripted
or budgeted handler and charge comparisons before performing them.

Build on existing ordering, comparison-counting and search-budget cases. Compare
with a pure reference sort, checking sorted order, permutation and stability.
A well-typed unstable implementation should fail the stability examples. A
handler that tries to resume twice to explore alternatives supplies a separate
static mistake; alternatives must instead be ordinary data or fresh calls.

Explain the work of the chosen algorithm and separate it from charged handler
events and wall-clock measurements. The new question is the algorithm's
invariant and result contract; adding only the existing budget handler to a new
traversal would add little. Cancellation is synchronous and does not return a
partial list labeled as sorted.

### Encode and decode a tagged frame

Extend [bounded message decoding][decoder-lesson] with several message
constructors, explicit integer byte tags, encoding and decoding. Return copied
ordinary message data from the native-buffer scope. State a small format profile
and check round trips, malformed tags, truncation, invalid byte values and
acquisition versus operation failures. Preserve nested outcomes where present.

[DN-0041](DN-0041-typed-serialization-and-data-pipelines.md#expressibility-experiment)
supplies pressure for explicit representation contracts and manual typed codecs.
This study claims only its declared format. It supplies no String/Bytes API,
standard JSON/BSON implementation, reflection or derivation facility.

Compare a direct decoder with a small materialized representation only if that
comparison answers a concrete question. A cursor closure that escapes its owner
is a candidate rejection; decode while access remains live and return independent
data as the repair. A deliberately inconsistent encoder/decoder pair supplies
the semantic counterexample that successful typing alone cannot detect.

## Evidence and experiments

### Develop the explanation from the problem

Use ash-doc's [writing guidance][writing] and the teaching discipline in
[DN-0024](DN-0024-executable-learning-and-evidence-stream.md#make-code-executable).
Begin with a meaningful example and the reader's working model. Derive the
data representation, invariants and public operation types, then develop the
smaller calculations. Introduce one unfamiliar boundary at a time, drawing on
the existing learning paths rather than repeating their complete explanations.

Ask the reader to predict a result or diagnose a plausible attempt before
explaining the observation. A diagnostic episode should connect the complete
actual message and causal source labels to the violated contract and repair.
Keep a discovery exercise's answer out of its displayed solution. Explain a
well-typed runtime counterexample where types do not establish the invariant.

End with what the example establishes, its costs and limitations, and an exercise
that changes one meaningful assumption. Keep compiler pins, verification logs,
coverage administration and future design pressure in project records rather
than repeatedly inserting them into the reader's lesson.

### Verify before presenting an observation

No proposed mistake or result in this note is a captured transcript or a new
acceptance receipt. Develop and run each complete candidate at the exact pin.

For an adopted study:

1. Keep canonical source, explanatory prose and local checks together. Transclude
   runnable blocks or check exact source agreement. Mark sketches as sketches.
2. Check successful values, types, stdout, stderr and exit status as applicable.
   Use independently specified examples or reference calculations for application
   invariants; do not derive every expectation from the implementation under test.
3. Check intentional source rejections through structured JSON, including the
   reason and relevant causal locations. Capture complete English human output
   with the pinned tool's explicit format and locale. Normalize only the
   documented checkout prefix. Keep wording checks separate from semantic checks.
4. Retain normal, rejection and runtime-failure cases relevant to the actual
   question. Distinguish a type rejection, a typed error result, an internal
   resource failure and an incorrect application result.
5. Add a bounded scaled case when it answers a cost or analysis question. Report
   logical operations, compiler exhaustion and physical measurements separately.
   A finite successful run establishes no general complexity or soundness theorem.
6. Verify changed navigation and source links. Update any affected family runner
   and coverage expectations; the inspected Cases runner fixes twenty destinations.
   Follow ash-doc's [verification policy][verification] for the affected scope and
   for any later complete-edition verification or migration.

Use hermetic inputs and deterministic scripts. Source failures should explain
the promised boundary without needing a live service or experimental compiler.
When a feature's ordinary behavior requires an unavailable capability, preserve
the useful current-language kernel and record the missing boundary honestly.

### Compare outcomes and retain useful findings

The comparison question is whether these studies improve a reader's ability to
design, predict and repair a program beyond the existing constituent lessons.
Record prerequisite burden, duplication, explanatory gaps, independent positive
and negative examples, and costs exposed by their combination. A case does not
succeed merely because it uses many features or compiles.

Retain a verified study when its application question, invariant and Ash-specific
choices remain useful. Simplify it when several mechanisms obscure the same
point. Revise or discard a duplicate or unsuccessful candidate while preserving
any distinguishing counterexample as evidence. Keep incomplete studies out of
active learning navigation under ash-doc's existing workflow.

Classify discoveries through DN-0024's cooperative evidence flow: repair tutorial
mistakes; minimize failures of specified behavior as potential Ash regressions;
return unspecified behavior to design work; and retain library, diagnostic or
performance pressure with the exact source and compiler commits. The fuller
teaching case remains owned by ash-doc. Selecting it as upstream evidence does
not make its entire implementation a language-conformance test.

## Open questions

- Which first-batch studies remain clear with their stated prerequisites, and
  which need a smaller teaching extension before the application?
- Which candidates should extend an existing Case, and which have enough of a
  distinct invariant and development arc to become separate studies?
- Does the scoped-policy application reveal a useful limit in rank-1 helper
  abstraction, or can explicit ordinary functions keep its API small?
- How much query abstraction improves the immutable ECS example before evidence
  plumbing hides the world and store invariants?
- Which composed cleanup or control examples reach the pinned compiler's work
  limits? An observed limit is evidence to classify, not permission to change it.
- Which diagnostic labels actually help readers find the cause, and which
  examples expose a message or explanation that needs improvement?

[spec]: https://github.com/dikini/ash-lang/blob/9ec5920e8c395f9a36125805ee93b7f58c0f4764/spec/README.md
[static]: https://github.com/dikini/ash-lang/blob/9ec5920e8c395f9a36125805ee93b7f58c0f4764/spec/static-semantics.md
[tool]: https://github.com/dikini/ash-lang/blob/9ec5920e8c395f9a36125805ee93b7f58c0f4764/docs/tools/ash.md
[cleanup-reporting]: https://github.com/dikini/ash-lang/blob/9ec5920e8c395f9a36125805ee93b7f58c0f4764/spec/dynamic-semantics.md#typed-failure-reporting
[hooks]: https://github.com/dikini/ash-lang/blob/9ec5920e8c395f9a36125805ee93b7f58c0f4764/spec/static-semantics.md#synchronous-typed-hooks
[ash-doc]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/README.md
[cases]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/content/cases/README.md
[libraries]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/content/libraries/README.md
[effects]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/content/effects/README.md
[cleanup-lesson]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/content/effects/running-cleanup/README.md
[pricing-lesson]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/content/cases/supplying-order-prices/README.md
[evidence-lesson]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/content/libraries/supplying-scoped-evidence/README.md
[hook-lesson]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/content/cases/controlling-a-hook-pipeline/README.md
[decoder-lesson]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/content/cases/reading-a-bounded-message/README.md
[writing]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/.agents/skills/writing-ash-documentation/SKILL.md
[verification]: https://github.com/dikini/ash-doc/blob/0b6b9c8a9fba9e9b87f0c8c047001743e81682c1/docs/project/verification.md
[historical]: https://github.com/dikini/ash/tree/f5316f952ee2c0fa7306d864d7f78edfe02d6d42/docs
[newtypes]: https://github.com/dikini/ash/blob/f5316f952ee2c0fa7306d864d7f78edfe02d6d42/docs/notes/NOTE-026-NEWTYPE-AND-PHANTOM-TYPES.md
[journal]: https://github.com/dikini/ash/blob/f5316f952ee2c0fa7306d864d7f78edfe02d6d42/docs/notes/NOTE-013-AMBIENT-MONAD-AND-HANDLER-COMPOSITION-ALGEBRA.md
[observability]: https://github.com/dikini/ash/blob/f5316f952ee2c0fa7306d864d7f78edfe02d6d42/docs/ideas/future/OBSERVABLE-STATE-AND-AUTHORIZED-CONTEXTS.md
[worker]: https://github.com/dikini/ash/blob/f5316f952ee2c0fa7306d864d7f78edfe02d6d42/docs/ideas/otp/OTP-004-harnessed-worker-bisimulation-patterns.md
