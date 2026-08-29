# Multi-Parameter Relational Interfaces Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task by task,
> preserving every RED witness and review checkpoint.

This temporary execution plan is owned by
[TASK-0018](../tasks/TASK-0018-implement-multi-parameter-relational-interfaces.md)
and only organizes implementation. It does not define Ash semantics. The
current `spec/` remains current Ash while accepted
[CP-0011](../proposals/CP-0011-multi-parameter-relational-interfaces.md) alone
authorizes the prospective transition.

**Goal:** Implement accepted CP-0011 as multi-parameter method-only interfaces
with zero or one total determinant key, forward-only improvement, complete
authenticated interface applications, and unchanged runtime erasure.

**Architecture:** Replace the unary interface carrier through the existing
surface, resolved, checked, summary, evidence, linked, elaboration, and Core
authentication path with one ordered application vector. Retain one optional
validated determinant-position key on interface facts. Run ordinary
unification, one isolated dependent-improvement pass, and full-goal evidence
selection as separate rule boundaries; lower the completed application through
the existing method-function evidence forms and erase determination before Core.

**Tech stack:** Rust 2024, the existing event-producing concrete-tree parser,
resolved-surface and fixed-kind boundaries, bidirectional elaborator,
body-free summaries, scoped interface evidence selector and linked validator,
typed pure Core, explicit evaluator machine, Cargo integration tests, and
Markdown specification.

---

Implementation follows `superpowers:test-driven-development`, `rust-skills`,
`superpowers:systematic-debugging` for unexpected results,
`superpowers:subagent-driven-development`,
`superpowers:requesting-code-review`, and
`superpowers:verification-before-completion`. Use one implementation agent at a
time because checkpoints share production state. Parallelize only independent
read-only audits. Report each agent's model and reasoning level.

For each production checkpoint:

1. assign a fresh implementer the complete checkpoint text;
2. write each named behavioral test and observe its expected RED before the
   corresponding production edit;
3. implement the minimum coherent behavior and run the focused GREEN commands;
4. run an independent CP-0011/specification-compliance review and correct every
   actionable finding;
5. run an independent Rust/resource-quality review and correct every actionable
   finding;
6. repeat affected review and focused verification, mark intended new paths
   with `git add -N`, inspect `git status --short`, and run `git diff --check`;
   and
7. create the named unsigned commit with
   `git -c commit.gpgsign=false commit`.

Keep `spec/` authoritative and unchanged through Checkpoint 6. Do not merge or
push the branch, tag a milestone, remove the branch, or remove the worktree.

## Budget and stop rules

The fixed allocation is `4 + 10 + 16 + 10 + 10 + 8 + 7 = 65` notional work
units. Starting a checkpoint reserves its complete allocation through
corrections and both reviews. Do not borrow from a later checkpoint or consume
the final specification-and-closure allocation early.

Stop rather than improvise if a checkpoint cannot reach GREEN plus both reviews
inside its allocation, if any additional work would exceed 65, or if
implementation requires:

- semantics absent from or inconsistent with CP-0011;
- a partial, second, transitive, reverse, or alternative determination edge;
- associated-output or projection syntax, projection normalization, defaults,
  specialization, or context-mediated implementation coverage;
- a general constraint store, higher-order matching, or a second evidence
  selection pipeline;
- a persistent Core representation decision outside AD-0007's replaceable
  private-storage boundary;
- a production resource-limit increase;
- interface evidence generalized into proof, effect, handler, provider, or
  existential authority;
- a new Core interface node, runtime dictionary or registry, or an evaluator
  change.

## Checkpoint 1: Authorize and baseline the increment — 4 units

**Files:**

- Create: `docs/proposals/CP-0011-multi-parameter-relational-interfaces.md`
- Create: `docs/tasks/TASK-0018-implement-multi-parameter-relational-interfaces.md`
- Create: `docs/plans/2026-08-29-multi-parameter-relational-interfaces.md`
- Modify: `docs/proposals/README.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`

### Step 1: Confirm transition authority

Confirm CP-0011 is `accepted`, TASK-0018 is `active`, the current specification
still describes unary predecessor behavior, and no implementation of CP-0011
is present at `a823094`.

### Step 2: Record the clean isolated baseline

Use:

```text
/home/dikini/Projects/ash-lang/.worktree/cp0010-method-local-type-parameters
```

Confirm `.worktree/` is ignored and the feature worktree is clean, then run:

```text
cargo xtask verify
```

Expected: PASS at `a823094` before transition artifacts or production changes.

### Step 3: Validate authorization artifacts

Run:

```text
git add -N docs/proposals/CP-0011-multi-parameter-relational-interfaces.md docs/tasks/TASK-0018-implement-multi-parameter-relational-interfaces.md docs/plans/2026-08-29-multi-parameter-relational-interfaces.md
markdownlint --disable MD013 -- docs/proposals docs/tasks docs/plans docs/trajectory.md
git diff --check
```

Resolve every changed relative link. Confirm that the proposal, task, plan, and
trajectory label current unary semantics, proposed relational semantics, and
future effects/proofs/existentials with their actual authority.

### Step 4: Review and commit authorization

Run independent semantic/authority and artifact/plan-quality reviews. Correct
every finding and repeat affected checks. Commit:

```text
git add docs/proposals/CP-0011-multi-parameter-relational-interfaces.md docs/tasks/TASK-0018-implement-multi-parameter-relational-interfaces.md docs/plans/2026-08-29-multi-parameter-relational-interfaces.md docs/proposals/README.md docs/tasks/README.md docs/trajectory.md
git -c commit.gpgsign=false commit -m "docs: authorize relational interface implementation"
```

Record cumulative reserved use as 4/65 and 61 units remaining.

## Checkpoint 2: Syntax, surface applications, and resolved identities — 10 units

**Files:**

- Modify: `src/parser/grammar.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/surface.rs`
- Modify: `src/resolve.rs`
- Modify: `src/resolved.rs`
- Modify: `tests/interfaces_syntax.rs`
- Modify: `tests/resolution.rs`
- Modify: `tests/diagnostics.rs`

### Step 1: Write and witness multi-parameter syntax RED

Add one exact projection witness containing:

```ash
interface Decode<Format, Source, Value> where (Format, Source) -> Value {
    decode : (Format, Source) -> Value
}

impl Decode<Int, Bool, Unit> {
    decode pair = ()
}
```

Assert token completeness, the three declaration parameter spans and kinds,
both determination-side spans and source order, all three implementation
argument spans, and the complete declaration spans. Run:

```text
cargo test --locked --test interfaces_syntax projects_relational_interface_parameters_and_total_key -- --exact
```

Expected RED: the second interface parameter is rejected where the unary
parameter production expects `>`, and no surface determination carrier exists.

### Step 2: Own malformed syntax and recovery

Add empty parameter list, trailing comma, missing `>`, missing `where` side,
empty side, missing arrow, unparenthesized multi-parameter side, repeated arrow,
and following valid declaration cases. Assert parser ownership, causal spans,
balanced events, token-complete next-line recovery, and refusal to project a
recovery-bearing tree. Preserve every unary predecessor syntax case.

Implement the minimum grammar and projection:

```ebnf
interface_declaration ::=
  [ "pub" ] "interface" upper_identifier interface_parameters
  [ interface_determination ] "{" line_end
  interface_method { line_end interface_method } [ line_end ] "}" ;
interface_parameters ::=
  "<" type_parameter { "," type_parameter } ">" ;
interface_determination ::=
  "where" determination_side "->" determination_side ;
determination_side ::=
  upper_identifier
  | "(" upper_identifier { "," upper_identifier } ")" ;
interface_application ::=
  interface_reference "<" type { "," type } ">" ;
```

Retain named surface application and determination carriers rather than
copying `interface + arguments` fields into every owner.

### Step 3: Write and witness resolved identity RED

Add a resolution test interleaving a three-parameter interface with a nominal,
implementation, and global. Assert module-wide binder identity order,
declaration parameter order, fixed omitted and explicit kinds, resolved
determination identities, and complete ordered requirement and head arguments.
Add duplicate interface binders and an unknown determination name.

Run:

```text
cargo test --locked --test resolution relational_interface_binders_and_applications_preserve_source_order -- --exact
```

Expected RED: resolution owns one interface parameter and one application
argument, so later binders and arguments are unavailable.

### Step 4: Implement surface and resolved vectors

Replace unary surface and resolved declaration/application fields with ordered
fixed-size carriers. Allocate all interface binders in declaration order before
method binders. Resolve determination names only against the owning interface
parameters. Preserve raw repeated, omitted, and reordered positions for later
interface admission unless resolution owns an unknown spelling.

Update every iterative disposal and construction failure path reached by the
new vectors. Preserve exact token/event and projected-surface retention
formulas, and charge the existing resolved binder/type ledgers before
allocation or publication. Do not add a parser resource ledger, checked
multi-parameter semantics, or improvement in this checkpoint.

### Step 5: Verify, review, and commit syntax and resolution

Run:

```text
cargo test --locked --test interfaces_syntax
cargo test --locked --test resolution
cargo test --locked --test diagnostics
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git add src/parser/grammar.rs src/parser/project.rs src/surface.rs src/resolve.rs src/resolved.rs tests/interfaces_syntax.rs tests/resolution.rs tests/diagnostics.rs
git -c commit.gpgsign=false commit -m "feat: retain relational interface syntax"
```

Record cumulative reserved use as 14/65 and 51 units remaining.

## Checkpoint 3: Complete application vectors through checked evidence and Core — 16 units

**Files:**

- Modify: `src/interface.rs`
- Modify: `src/evidence.rs`
- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/evidence_audit.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/driver.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/validate.rs`
- Modify as required by compiler-owned consumers: `src/core/transform.rs`
- Modify: `tests/interfaces.rs`
- Modify: `tests/implementations.rs`
- Modify: `tests/interface_selection.rs`
- Modify: `tests/interface_generic_summary.rs`
- Modify: `tests/interface_validation.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/architecture.rs`

### Step 1: Write and witness ordinary relation RED

Add an interface without a determination edge:

```ash
interface Pairwise<Left, Right> {
    pairwise : (Left, Right) -> Bool
}

impl Pairwise<Int, Bool> {
    pairwise pair = true
}

main : Unit -> Bool
main () = pairwise((1, true))
```

Assert checked parameter and application order, selected complete head,
evaluation, and unchanged evidence priority. Add a method omitting `Right` and
expect `interface.method-parameter`.

Run:

```text
cargo test --locked --test interfaces ordinary_multi_parameter_relation_selects_and_evaluates -- --exact
```

Expected RED: checked interface facts, obligations, evidence plans, and Core
authentication still accept exactly one parameter and argument.

### Step 2: Introduce the canonical checked application

Introduce one private checked carrier equivalent to:

```text
InterfaceApplication {
    interface: InterfaceId,
    arguments: Box<[Type]>,
}
```

Use it in checked requirements, implementation heads, pending and frozen
occurrences, goal keys, evidence-plan roots, summary and linked facts,
elaboration buffers, and Core authentication. Expose read-only interface and
argument-slice accessors. Parse and validate at each owning boundary; do not
make construction alone replace kind, scope, zonking, or provenance checks.

Change checked interface facts from one parameter to an ordered boxed slice of
canonical `ResolvedTypeVariable` records. Use aligned iteration for arity,
kinding, substitution, matching, cloning, equality, validation, and disposal.
Never fold the argument vector into `Type::Tuple` or nested unary interface
applications.

### Step 3: Generalize ordinary multi-parameter rules

With no determinant key:

- require every interface parameter in every method value type;
- instantiate all interface parameters before method-local parameters;
- create one complete application obligation;
- require all arguments zonked before selection;
- match full vectors kind-preservingly;
- generalize full-head overlap, orphan ownership, and structural prerequisite
  decrease across the complete vector; and
- retain abstract, exact-current, concrete, prerequisite, recursive, and
  method-local evidence order.

Add arity and per-position kind failures for requirements, heads, and imported
facts. Require `interface.argument-count` before positional kind checking and
retain `kind.argument` for an arity-correct wrong-kind argument. Preserve unary
behavior as the width-one case.

### Step 4: Authenticate and lower complete vectors

Extend body-free summary cloning/admission and linked evidence validation to
authenticate parameter and argument count, order, identity, kind, origin, and
complete method substitution. Extend method-evidence catalogs and Core
validation to rederive each method scheme by aligned substitution of all
interface parameters before method-local arguments.

Keep generated adapter head-binder then method-binder order. Add no determinant
metadata to Core, no Core node, and no evaluator behavior. Update identity and
literal-folding transforms only where complete authentication facts require
copying or remapping.

### Step 5: Add complete-vector tampering RED and GREEN

Add missing, extra, reordered, wrong-kind, and wrong-identity parameter and
argument mutations at checked-summary, linked-evidence, and independent Core
boundaries. Each must fail before Core construction or evaluation according to
its owning stage. Add a polymorphic method whose higher-kinded interface
arguments precede method-local arguments in authentication and Core type
application.

### Step 6: Verify, review, and commit vector migration

Run:

```text
cargo test --locked --test interfaces --test implementations --test interface_selection
cargo test --locked --test interface_generic_summary --test interface_validation
cargo test --locked --test core_validation --test architecture
cargo test --locked --lib -- interface
cargo test --locked --lib -- evidence
cargo test --locked --lib -- resolved
cargo test --locked --lib -- evidence_validation
cargo test --locked --lib -- core
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git add src tests
git -c commit.gpgsign=false commit -m "feat: carry complete interface applications"
```

Record cumulative reserved use as 30/65 and 35 units remaining.

## Checkpoint 4: Total-key admission, coherence, ownership, and termination — 10 units

**Files:**

- Modify: `src/interface.rs`
- Modify: `src/evidence.rs`
- Modify: `src/resolved.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `tests/interfaces.rs`
- Modify: `tests/implementations.rs`
- Modify: `tests/interface_modules.rs`
- Modify: `tests/interface_identity_diamond.rs`
- Modify: `tests/interface_generic_summary.rs`
- Modify: `tests/diagnostics.rs`

### Step 1: Write and witness determinant-admission RED

Add exact positive cases for `I -> Item`, `(Format, Source) -> Value`, and a key
whose dependent parameter is not last in declaration order. Add repeated,
omitted, reordered, overlapping, empty, and full-key invalid cases. Assert the
single `interface.determination-parameter` reason and causal parameter spans.

Add method seed tests:

- all parameters required without a key;
- every key parameter required with a key;
- dependent in a domain, result, nested type, and absent entirely;
- a missing composite-key member rejected before outer-function shape.

Run:

```text
cargo test --locked --test interfaces determined_methods_require_the_complete_key_only -- --exact
```

Expected RED: the resolved determination has no checked positional metadata or
method-seed rule.

### Step 2: Admit one validated positional key

Validate the source identities as a nonempty proper declaration-order subset
whose complement is exactly the other parameters. Retain only declaration
positions in the checked fact and every summary mirror; derive dependents as
the complement. Add accessors for selection-key and dependent aligned slices.
Do not store an edge graph or output-last split.

### Step 3: Write and witness self and pair coherence RED

Add:

```ash
interface Relation<A, B> where A -> B {
    relate : A -> Int
}

impl<B> Relation<Int, B> { ... }
```

Expect `impl.determination-coverage`. Add accepted constant and
`Relation<List<A>, A>` heads. Implement the first-order rule
`FV(dependents) subset-of FV(key)` without consulting prerequisites.

Generalize `impl.variable-head`: reject a head whose every selection-key
argument is a bare type variable, including a determined relation with a
constant dependent. Accept a key with at least one non-variable outer
structure. Use the full vector for a no-edge interface.

Add one local generic/ground pair and one imported/local pair whose importing
module first combines the facts. Independently freshen each head and unify
keys. Preserve
`impl.overlap` when complete heads unify; otherwise report
`impl.determination-conflict`. Stable `ImplId` deduplication happens first, and
one diamond proves that two routes to the same identity do not self-conflict.
The first combined effective environment owns a real pair failure.

### Step 4: Generalize orphan ownership and prerequisite decrease

Use the determinant slice as the selection key when present and the full vector
otherwise. Add a foreign-interface positive case with a local outer nominal in
the key and negative cases where the local nominal occurs only in a dependent
argument or outside the accepted outer spine.

Require equal-width selection-key tuples. Compare corresponding positions in
declaration order: every prerequisite component must be identity-equal to or a
strict syntactic subterm of the head component, and at least one component must
be strict. Add multi-input decreasing and non-decreasing cases, one
different-width rejection, a rejected case where only a dependent shrinks, and
a ground active-goal cycle over the full application. Retain the rule that
every prerequisite variable occurs in the complete implementation head.

### Step 5: Authenticate key metadata across summaries

Add summary mutations for missing, extra, duplicate, reordered, out-of-range,
wrong-interface, and mismatched key positions. Authenticate imported key
metadata before local header checking and recheck coherence when an import or
facade first combines implementation closures.

### Step 6: Verify, review, and commit total-key checking

Run:

```text
cargo test --locked --test interfaces --test implementations
cargo test --locked --test interface_modules --test interface_identity_diamond
cargo test --locked --test interface_generic_summary --test diagnostics
cargo test --locked --lib -- interface
cargo test --locked --lib -- resolved
cargo test --locked --lib -- evidence_validation
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git add src tests
git -c commit.gpgsign=false commit -m "feat: enforce total interface determination"
```

Record cumulative reserved use as 40/65 and 25 units remaining.

## Checkpoint 5: Forward improvement and determined requirements — 10 units

**Files:**

- Modify: `src/interface.rs`
- Modify: `src/evidence.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/resolved.rs`
- Modify: `tests/interfaces.rs`
- Modify: `tests/interface_selection.rs`
- Modify: `tests/implementations.rs`
- Modify: `tests/polymorphism.rs`
- Modify: `tests/interface_diagnostics.rs`

### Step 1: Write and witness concrete improvement RED

Use:

```ash
interface Convert<From, To> where From -> To {
    convert : From -> To
}

impl Convert<Int, Bool> {
    convert value = true
}

main : Unit -> Bool
main () = convert(1)
```

Run:

```text
cargo test --locked --test interface_selection known_key_improves_the_complete_goal_before_selection -- --exact
```

Expected RED: ordinary checking fixes `From = Int`, leaves `To` unresolved,
and predecessor selection reports `constraint.ambiguous`.

Add composite-key and generic-head cases. Assert that improvement fills only
dependents, retains no evidence selection, and full-head selection later
chooses the expected implementation.

### Step 2: Add the separate improvement boundary

While the elaborator still owns mutable inference state, visit pending complete
applications in source order. If every key component is inference-free, use the
existing source priority: identity-equal abstract key, exact current key, then
the unique coherent visible key match. Instantiate the source's complete head
and unify only dependent positions. Do not inspect prerequisites, fill an
evidence slot, or modify key positions.

Before improvement mutates inference state, snapshot which obligations already
have inference-free keys. Process only that set once in source order.
Improvement is mandatory when a source exists, even when ordinary checking
already fixed every dependent, and it unifies the complete dependent tuple
atomically. An output filled by one obligation cannot unlock another obligation
in the same pass. Reject every determined obligation outside the snapshot as
`constraint.ambiguous` for this closure even if later zonking makes its key and
complete application inference-free. For snapshot members, retain the existing
close path: zonk the full application, reject any remaining inference variable
as `constraint.ambiguous`, and perform full-goal evidence selection. No-edge
obligations retain their predecessor close path. Do not add an edge worklist,
repeated saturation, or cross-obligation closure.

### Step 3: Prove ambiguity, agreement, and non-reversal

Add cases for:

- incomplete single and composite keys;
- known dependent with an unknown key;
- a dependent fixed by expected typing that agrees or disagrees with
  improvement, with disagreement owned by
  `constraint.determination-conflict` and no partial inference publication;
- no visible improvement source, retaining ambiguity until full selection can
  own unsatisfied evidence;
- abstract requirement priority over a visible concrete implementation;
- exact-current recursion and prerequisites;
- a method-local parameter that never affects key matching; and
- no higher-order matching through a higher-kinded key.

Add one source-order isolation RED in which improvement of an earlier
obligation would make a later key known. Give the later obligation an already
fixed dependent so that the indirect update would make its whole application
complete. It must still remain ambiguous because its key was incomplete in the
pre-improvement snapshot and it cannot bypass mandatory improvement by entering
full selection.

### Step 4: Write and witness determined-requirement RED

Add a constrained global whose dependent binder occurs only in:

```ash
size<I, Item> : I -> Int where Iterator<I, Item>
```

Require every key variable in the value type, retain the dependent-only binder
in scheme order, and lower its complete abstract evidence. Keep the current
rule for interfaces without keys.

Add duplicate full requirements, two identity-equal keys with distinct
dependents, and separate requirements that could form a chain. Reject the
same-key pair as `constraint.determination-conflict`; do not equate outputs or
perform cross-requirement improvement.

### Step 5: Verify, review, and commit improvement

Run:

```text
cargo test --locked --test interfaces --test interface_selection
cargo test --locked --test implementations --test polymorphism
cargo test --locked --test interface_diagnostics
cargo test --locked --lib -- evidence
cargo test --locked --lib -- elaborate
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git add src tests
git -c commit.gpgsign=false commit -m "feat: improve determined interface goals"
```

Record cumulative reserved use as 50/65 and 15 units remaining.

## Checkpoint 6: Adversarial linking, resources, and downstream pressure — 8 units

**Files:**

- Modify: `src/resolved.rs`
- Modify: `src/evidence.rs`
- Modify: `src/evidence_audit.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/validate.rs`
- Modify: `src/core/transform.rs`
- Modify: `src/driver.rs`
- Modify: `tests/interface_generic_summary.rs`
- Modify: `tests/interface_modules.rs`
- Modify: `tests/interface_identity_diamond.rs`
- Modify: `tests/interface_validation.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/interface_resources.rs`
- Modify: `tests/method_parameter_resources.rs`
- Modify: `tests/architecture.rs`
- Modify: `tests/interface_corpus.rs`

### Step 1: Retain one complete linked relational program

Create a definition module with a public higher-kinded three-parameter
interface, one composite key, a polymorphic method, and a public
implementation. Re-export names and implementation authorization through a
facade, consume only body-free summaries in the entry, link, independently
validate Core, run both retained transforms, revalidate, and evaluate the
expected result.

Assert full parameter and application order, stable identities through a
diamond, shortest authorization route, abstract and concrete evidence,
adapter-head then method-local argument order, and no new runtime state or
transition.

### Step 2: Complete the minimum tampering matrix

At summary admission, reject parameter missing, extra, reordered, wrong
identity or kind; invalid determinant positions; and application missing,
extra, or reordered. At linked validation, reject key and dependent mismatch,
abstract and implementation application mismatch, and substitution of a
same-shaped but identity-distinct hidden nominal. At Core validation, reject
wrong simultaneous substitution, swapped application authentication, and
reordered head-versus-method arguments. One transformed-Core stale-authority
case is sufficient; predecessor route, method, binder, and prerequisite-tree
tampering remains migration evidence.

Include separate private-hidden and public-opaque nominals in dependent
positions and prove that each identity crosses summaries without becoming
constructible or otherwise more accessible than its current boundary permits.

Authenticate the complete application at every selected occurrence and
adapter. Keep `EvidenceSelection` opaque and current producers interface-only;
do not generalize it into a universal witness.

### Step 3: Audit downstream representation pressure without new semantics

Use the hidden and opaque dependent fixtures plus the existing closed-inventory
architecture guards. Review that no effect row, handler, proof term,
existential binder, pack/unpack node, runtime witness, or common evidence family
enters the source, checked, Core, or evaluator inventories. Do not add provider-
shaped, proof-shaped, or existential-proxy product fixtures.

### Step 4: Derive exact resource formulas RED-first

Inventory every new boxed vector, position set, aligned traversal, candidate
match, coherence pair, improvement visit, summary copy, validation fact, and
Core authentication copy. Add exact-success and one-short cases for:

- interface parameter width and application width;
- imported and local implementation closure width;
- key and full-head pair coherence;
- improvement candidate scanning and dependent unification;
- summary admission, linked validation, Core construction, transforms, and
  independent Core validation; and
- rejected then retried atomic publication.

Add one owner-level wide-vector exact boundary, one cross-stage graph-wide
integration boundary, one deep dependent type, and accepted and rejected
disposal on a 256 KiB stack. Rebaseline predecessor probes only where formulas
change. Charge before allocation or retention and use iterative disposal for
every owned type vector. Do not raise a production limit.

### Step 5: Verify, review, and commit retained evidence

Run:

```text
cargo test --locked --test interface_corpus
cargo test --locked --test interface_generic_summary --test interface_modules
cargo test --locked --test interface_identity_diamond --test interface_validation
cargo test --locked --test core_validation --test architecture
cargo test --locked --test interface_resources --test method_parameter_resources
cargo test --locked --lib -- resolved
cargo test --locked --lib -- evidence_validation
cargo test --locked --lib -- core
cargo fmt --check
cargo check --locked --all-targets
cargo clippy --locked --workspace --all-targets --all-features -- -D warnings
git diff --check
```

After both reviews and corrections, commit:

```text
git add src tests
git -c commit.gpgsign=false commit -m "test: retain relational interface evidence"
```

Record cumulative reserved use as 58/65 and preserve all 7 remaining units for
specification and closure.

## Checkpoint 7: Specification, retained evidence, and transition closure — 7 units

**Files:**

- Modify: `spec/README.md`
- Modify: `spec/syntax.md`
- Modify: `spec/name-resolution.md`
- Modify: `spec/static-semantics.md`
- Modify: `spec/elaboration.md`
- Modify: `spec/dynamic-semantics.md`
- Modify: `docs/design/DN-0025-library-and-package-milestones.md`
- Create: `docs/design/lib-ash/relational-interfaces-evidence.md`
- Modify: `docs/trajectory.md`
- Modify: `tests/spec_examples.rs`
- Modify: `tests/corpus.rs`
- Modify: `README.md` if its current-language summary is affected
- Update then remove after the retained checkpoint: `docs/proposals/CP-0011-multi-parameter-relational-interfaces.md`
- Update then remove after the retained checkpoint: `docs/tasks/TASK-0018-implement-multi-parameter-relational-interfaces.md`
- Remove after the retained checkpoint: `docs/plans/2026-08-29-multi-parameter-relational-interfaces.md`
- Modify: `docs/proposals/README.md`
- Modify: `docs/tasks/README.md`

### Step 1: Reserve the normative specification checkpoint

Record the completed product evidence in TASK-0018 before changing `spec/`.
Run a semantic reconciliation review against CP-0011 and every retained test.
If implementation evidence contradicts an accepted rule, stop and return to
the proposal instead of changing semantics locally.

### Step 2: Update normative syntax and name resolution

Update the grammar with the exact multi-parameter and determination productions
implemented in Checkpoint 2. Explain canonical binder and application order,
determination-name scope, complete argument arity, kind checking, and stable
identity through summaries. Add executable source examples.

### Step 3: Update normative static semantics

Replace unary interface, requirement, implementation, coherence, orphan,
termination, improvement, and selection rules with complete applications and
the optional total key. Use `sequent` fences only for actual inference-rule
families and explain every fence in prose. State failure precedence and exact
resource ownership from implemented evidence.

### Step 4: Update elaboration and dynamic semantics

Specify aligned substitution of every complete application, evidence and
adapter ordering, authenticated summary and Core facts, determinant erasure,
and the unchanged evaluator inventory. Do not describe effects, proofs, or
existentials as current Ash.

### Step 5: Retain evidence and revise the milestone boundary

Record the exact implementation commits, positive and negative corpus,
tampering matrices, resource formulas, migration, reviews, Core transforms,
linked program, evaluation, and verification in
`docs/design/lib-ash/relational-interfaces-evidence.md`. Revise DN-0025 and the
trajectory to record why relational-only single-total-key interfaces were
retained and associated syntax, general graphs, and defaults were deferred.

Add a corpus manifest proving every predecessor unary fixture remains the
width-one no-edge case and every normative relational example executes or has
its exact structured rejection.

### Step 6: Run independent final reviews and the full gate

Run independent reviews for:

- CP-0011 and normative semantic compliance;
- Rust ownership, API, diagnostics, and exact resource accounting;
- summary, linked-evidence, and Core authentication security;
- effects, proofs, and existential pressure boundaries;
- specification and documentation authority, links, examples, and migration;
  and
- whole-branch scope and simplification.

Correct every actionable finding and repeat affected focused checks. Then run:

```text
cargo xtask verify
markdownlint --disable MD013 -- docs spec README.md AGENTS.md
git diff --check
git status --short
```

Expected: all Rust gates, exact tests, rustdoc, Markdown, links, diff hygiene,
and intended-path inspection pass with no warning or unexpected path.

### Step 7: Retain the product checkpoint and clean transition artifacts

Commit specification and retained evidence before cleanup. Update CP-0011 and
TASK-0018 with final evidence while they still exist, then remove the accepted
proposal, completed task, execution plan, and their active index entries in a
separate cleanup commit. Run the full gate again after cleanup.

Do not merge to `main`, push, tag `lib-ash`, delete the feature branch, or
remove the worktree. Report the verified branch and commits to the user and
request integration direction.

Record final reserved use as 65/65.
