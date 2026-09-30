# Core one-shot alignment execution plan

Owned by [TASK-0032](TASK-0032-core-one-shot-alignment.md). This temporary plan
does not define language semantics or independently authorize architecture.

## Increment 1: Comparison and first regression

1. Inspect normative handlers, cleanup, cells and Core lowering; inspect current
   M0–M4 endpoints and run their existing grouped check.
2. Reproduce direct/bound effectful resume operands and unsafe discard in
   `tests/core_alignment_resume.rs`. Record the construction failure before a fix.
3. Construct the smallest captured-handler cleanup comparison. Record both Core
   admission and calculus transitions, including the removed-nearest-interpreter
   negative case and a supported cleanup trace.
4. Identify every Core syntax and evaluator transition family applicable to the
   proposed fragment. Map it to an existing calculus constructor or explicit gap.
5. Review the causal discrepancy before choosing a repair. Fix only demonstrated
   current-semantics violations; open a proposal for any semantic change.

Acceptance: reproducible comparison, finite inventories, focused regression
results and a reviewed initial translation design. Expected bounded work: 1–2
active hours; later estimates depend on the admission-evidence gap inventory.

## Increment 2: Complete initial vertical slice

Translate a validated Core program containing sequencing, a one-shot operation,
resume or discard, a cell and cleanup. Derive static evidence into
`InitialAdmission.Program`; relate its actual evaluator states to calculus states
and check its result, cleanup order and ownership. Reuse validators and existing
Lean judgments. A fixture is an integration check, not the general theorem.

Acceptance: executable Core input, constructed admission, nonvacuous finite
execution correspondence and explicit finite-capacity treatment. Final interfaces
and worker file ownership follow C1 findings; no speculative parallel writes.

### Remaining integration order

The finite graph translator and actual Rust exporter are retained. The first
kernel admission attempt exposed D8: a clause interface admitted independently
chosen receiving tails that alias captured owners. Finish the conditional
closing-separation repair and construct the complete fixture's `Program` before
generalizing admission. Derive the condition from existing unwind ownership and
uniqueness; resume-only outside demands remain permitted.

The independent `CoreMachine` now provides concrete configurations for the C3
relation. Verify its successful transitions and the opt-in snapshots taken by
Rust's actual `run_loop`, then connect these representations in this order:

1. Relate scalar values, resource keys, tuple locations and closures to scoped
   calculus values. Heap lookup must preserve binary products. Closure lookup
   must preserve the captured environment suffix and resource instantiation.
   A nonrecursive function template includes itself in Core's environment;
   removing that unused binding requires the nonrecursion evidence.
2. Relate strict evaluation contexts, source handlers, live and consumed clause
   owners, and nested captures. Reverse Rust's outermost-first frame vectors
   exactly once. Assign handler, cleanup and ticket ghost identities to dynamic
   occurrences; static node IDs cannot distinguish repeated activations.
3. Relate discard projection and lexical unwind using the existing closing
   order and route lemmas. Derive that retained lexical handlers cannot change
   callback dispatch for admitted Core cleanup. Equal closing-item order alone
   does not prove callback execution correspondence.
4. Prove each transition match with an explicit rank for administrative steps.
   In particular, Core evaluates literals and variables into return controls
   where the calculus can already have a value. Internal `entered` observations
   are not Rust's dispatch trace: Rust omits cleanup registration entries.
   State which projection supplies observable results, cell operations and
   cleanup order.
5. Compare structured Rust snapshots with this relation, retaining raw identity
   distinctions before any deterministic normalization. Successful preparation
   includes disposal checks during mutation. Keep failed execution prefixes
   separate until their partial observations have been accounted for.

These are dependencies within C3.1–C3.5, not additional packages or a replacement
for the general transition proof. Snapshot tests establish implementation
evidence; they do not construct calculus validity or prove simulation.

## Increment 3: Generalize the declared fragment

Generalize static translation by structural induction and runtime correspondence
by the finite transition inventory. Retain only metadata required by identified
obligations. Prove agreement for actual Core execution rather than selecting a
convenient calculus execution. Resolve C4 findings and feed them back into C2/C3.

Acceptance: every in-scope translation and transition case proved, required
annotations statically authenticated, no circular successor assumptions and no
unrestricted zero-step simulation.

## Increment 4: Integrate and audit

Compose admission, simulation, progress and ownership; verify terminal results and
cleanup accounting. Run grouped verification and independent review. Update the
specification only with retained semantic changes, and keep formal model claims
separate from Rust validation/tests. Deliver the C1–C5 table and theorem entry
points with all assumptions and exclusions. Remove this plan when the task closes.

## Execution discipline

Implementation workers use verified GPT-6.1 Sol medium and disjoint owned files;
GPT-6 Astra reviews decisions and integration. Report after each increment and at
least every 30 minutes, using the task's stable inventory. Preserve blocked and
failed approaches where they change the plan. Re-estimate after C1 rather than
assigning hours to unknown proof obligations.
