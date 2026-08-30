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
- Modify as compiler-owned unary predecessor migrations: `src/kind.rs`
- Modify as compiler-owned unary predecessor migrations: `src/elaborate.rs`
- Modify as compiler-owned unary predecessor migrations: `src/evidence.rs`
- Modify as compiler-owned unary predecessor migrations: `src/evidence_audit.rs`
- Modify as compiler-owned unary predecessor migrations: `src/evidence_validation.rs`
- Modify for resource-fixture alignment: `src/driver.rs`
- Modify: `tests/interfaces_syntax.rs`
- Modify: `tests/resolution.rs`
- Modify: `tests/diagnostics.rs`
- Modify as compiler-owned unary predecessor migrations: `tests/core_validation.rs`
- Modify as compiler-owned unary predecessor migrations: `tests/interface_modules.rs`
- Modify as compiler-owned unary predecessor migrations: `tests/kinds_syntax.rs`
- Modify as compiler-owned unary predecessor migrations: `tests/spec_examples.rs`
- Modify for resource-fixture alignment: `tests/interface_resources.rs`
- Modify for bidirectional type-site inventory: `tests/architecture.rs`
- Modify for syntax/resource formula alignment: `tests/method_parameter_resources.rs`

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

At each migrated unary checked consumer, authenticate the predecessor shape
before indexing: exactly one interface parameter, no determination, and exactly
one application argument. Relational shapes remain available to resolution and
defer unary kind work, but fail closed before checked publication until
Checkpoint 3. Independent validators reauthenticate this boundary rather than
trusting upstream publication. This guard is transitional internal-state
ownership, not the source `interface.argument-count` or determination admission
implemented by later checkpoints.

### Step 5: Verify, review, and commit syntax and resolution

Run:

```text
cargo test --locked --test interfaces_syntax
cargo test --locked --test resolution
cargo test --locked --test diagnostics
cargo test --locked --lib -- evidence
cargo test --locked --lib -- evidence_validation
cargo test --locked --test interface_resources
cargo test --locked --test architecture
cargo test --locked --test method_parameter_resources
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git add docs/plans/2026-08-29-multi-parameter-relational-interfaces.md docs/tasks/TASK-0018-implement-multi-parameter-relational-interfaces.md src/parser/grammar.rs src/parser/project.rs src/surface.rs src/resolve.rs src/resolved.rs src/kind.rs src/elaborate.rs src/evidence.rs src/evidence_audit.rs src/evidence_validation.rs src/driver.rs tests/interfaces_syntax.rs tests/resolution.rs tests/diagnostics.rs tests/core_validation.rs tests/interface_modules.rs tests/kinds_syntax.rs tests/spec_examples.rs tests/interface_resources.rs tests/architecture.rs tests/method_parameter_resources.rs
git -c commit.gpgsign=false commit -m "feat: retain relational interface syntax"
```

Record cumulative reserved use as 14/65 and 51 units remaining.

## Checkpoint 3: Complete application vectors through checked evidence and Core — 16 units

**Files:**

- Modify: `src/interface.rs`
- Modify as a compiler-owned checked kind boundary: `src/kind.rs`
- Modify: `src/evidence.rs`
- Modify: `src/resolved.rs`
- Modify: `src/resolve.rs`
- Modify as the existing summary-authentication test owner: `src/resolve/module_tests.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/evidence_audit.rs`
- Modify: `src/evidence_validation.rs`
- Modify: `src/driver.rs`
- Modify: `src/core/dialect.rs`
- Modify: `src/core/validate.rs`
- Modify as required by compiler-owned consumers: `src/core/transform.rs`
- Modify: `tests/interfaces.rs`
- Modify: `tests/implementations.rs`
- Modify: `tests/diagnostics.rs`
- Modify: `tests/kinds_syntax.rs`
- Modify: `tests/kind_modules.rs`
- Modify: `tests/interface_resources.rs`
- Modify: `tests/interface_selection.rs`
- Modify: `tests/interface_generic_summary.rs`
- Modify: `tests/interface_validation.rs`
- Modify: `tests/core_validation.rs`
- Modify: `tests/architecture.rs`
- Modify as a compiler-owned checked-carrier API migration: `tests/interface_modules.rs`
- Modify as compiler-owned checked-carrier API migrations: `tests/library_imports.rs`
- Modify as compiler-owned checked-carrier API migrations: `tests/interface_identity_diamond.rs`

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

Keep vector-container and recursive type work distinct. Charge complete-vector
allocation and positional authentication at each owner before publication;
retain exact, one-short, and retry witnesses for local checking, summary
cloning and linking, evidence selection, elaboration, and Core authentication.

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
cargo test --locked --test diagnostics --test kinds_syntax --test kind_modules
cargo test --locked --test interface_resources
cargo test --locked --test interface_generic_summary --test interface_validation
cargo test --locked --test core_validation --test architecture
cargo test --locked --test interface_modules
cargo test --locked --lib -- interface
cargo test --locked --lib -- kind
cargo test --locked --lib -- evidence
cargo test --locked --lib -- resolved
cargo test --locked --lib -- elaborate
cargo test --locked --lib -- evidence_validation
cargo test --locked --lib -- core
cargo test --locked --lib -- driver
cargo fmt --check
cargo check --locked --all-targets
git diff --check
```

After both reviews and corrections, commit:

```text
git add docs/plans/2026-08-29-multi-parameter-relational-interfaces.md docs/tasks/TASK-0018-implement-multi-parameter-relational-interfaces.md src tests
git -c commit.gpgsign=false commit -m "feat: carry complete interface applications"
```

Record cumulative reserved use as 30/65 and 35 units remaining.

## Checkpoint 4: Total-key admission, coherence, ownership, and termination — 10 units

**Status:** Complete in the coherent Checkpoint 4 tree recorded by the commit
that contains this update. Final semantic and whole Rust/resource reviews
approve without findings. The specification remains unchanged; this is
implementation evidence under accepted CP-0011, not current language truth.

**Files:**

- Modify for global application-preflight calibration: `src/driver.rs`
- Modify: `src/interface.rs`
- Modify for body-free method-seed authentication: `src/kind.rs`
- Modify: `src/resolved.rs`
- Modify for source-to-summary publication: `src/resolve.rs`
- Modify as the detached summary-authentication test owner: `src/resolve/module_tests.rs`
- Modify: `src/elaborate.rs`
- Modify: `src/evidence_validation.rs`
- No modification required: `src/evidence.rs`; determinant metadata uses the
  existing interface-fact and evidence boundaries.
- Modify: `tests/interfaces.rs`
- Modify: `tests/implementations.rs`
- Modify: `tests/interface_modules.rs`
- Modify: `tests/interface_identity_diamond.rs`
- Modify: `tests/interface_generic_summary.rs`
- Modify: `tests/diagnostics.rs`

### Step 1: Write and witness determinant-admission RED — completed

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

### Step 2: Admit one validated positional key — completed

The implementation validates the source identities as a nonempty proper
declaration-order subset whose complement is exactly the other parameters. It
retains only private declaration positions in checked, local, and body-free
interface facts and derives dependents as the complement. Review removed the
planned public selection-key and dependent aligned-slice accessors; private
position-key access is sufficient. No edge graph or output-last split is
stored.

### Step 3: Write and witness self and pair coherence RED — completed

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

### Step 4: Generalize orphan ownership and prerequisite decrease — completed

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

### Step 5: Authenticate key metadata across summaries — completed

Add summary mutations for missing, extra, duplicate, reordered, out-of-range,
wrong-interface, and mismatched key positions. Authenticate imported key
metadata before local header checking and recheck coherence when an import or
facade first combines implementation closures.

### Step 6: Verify, review, and retain total-key checking — completed

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
git add docs/plans/2026-08-29-multi-parameter-relational-interfaces.md docs/tasks/TASK-0018-implement-multi-parameter-relational-interfaces.md src tests
git -c commit.gpgsign=false commit -m "feat: enforce total interface determination"
```

Record cumulative reserved use as 40/65 and 25 units remaining.

### Checkpoint 4 closure record

The retained implementation evidence has these boundaries:

- Admission authenticates an exact total partition. A no-edge interface
  requires every parameter in each method; a determined interface requires
  every determinant and permits dependents in a domain, result, nested type, or
  nowhere. Body-free checking selects an explicit
  `AllInterfaceParameters` or `Determined` seed, and imported and linked facts
  derive and authenticate that seed from key positions.
- One unconditional global arity preflight precedes partition, method, and
  implementation-header failures across global requirements, implementation
  heads, and prerequisites. Positional kind preflight follows only for
  arity-complete applications, so incomplete arity defers positional kinding.
  Elaboration independently preflights arity. No production resource limit
  changed.
- Header checking iteratively establishes `FV(dependents) subset FV(key)`.
  All-bare selection and foreign orphan ownership inspect the key alone.
  Generic prerequisite decrease is pointwise across equal-width keys and keeps
  the complete active application as cycle identity. Coherence deduplicates
  stable `ImplId`s, independently matches keys and then complete heads, and
  lets the first effective combiner own `impl.overlap` or
  `impl.determination-conflict`.
- Source-to-summary publication authenticates the source key. Detached summary
  admission authenticates key structure, method seeds, variable-head,
  dependent-coverage, orphan, prerequisite-decrease, and pair-coherence
  relationships. Imports authenticate before local checking, and facade and
  first-combiner paths authenticate their effective closures.
- Linked validation indexes the complete registry, authenticates every group's
  source, token, and fact key in a first phase independent of dependency and
  group order, and only then authenticates relationships. Generic prerequisite
  termination uses selection-key tuples while retaining the complete
  prerequisite for groundness. Honest dependent growth passes, and a coherent
  dependent-only-shrink tamper fails. Each source occurrence's identity,
  spelling, origin, and span and the determined linked-method seed remain
  authenticated. An honest stable-identity re-export diamond passes.
  Determinant metadata erases before Core.
- Raw determinant-position and key getters are crate-private. A crate unit test
  retains exact representation evidence; public integration tests assert
  admission, coherence, ownership, termination, summary, and linking behavior
  without observing private positions. CP4 adds no public selection/dependent
  API, edge graph, Core determinant metadata or node, evaluator state, or
  runtime metadata.

Exact resource evidence is compactly recorded below. `P` is the complete
application width and `D` is determinant width.

- The local selection-key helper costs exactly `P` without an edge and `2D`
  with one. Its one-short failures stop at `0` and `D`, respectively, after the
  charge-before-reserve correction. The mirrored summary collector has the
  same staging property. Total formulas did not change.
- Local determination coverage costs 12, key-variable admission 2, and foreign
  orphan selection 3. Local and summary prerequisite decrease each cost 23;
  effective pair coherence costs 46 and summary pair coherence costs 23.
- A determinant diagnostic's causal declaration label costs 14. A complete
  non-decreasing header costs 59. The local-interface predecessor boundary
  remains 92.
- The local source-to-summary key fixture costs 11. Detached determined-summary
  relationship authentication costs 77 constraint units and 105 type units;
  key relationship work accounts for the 17-unit constraint delta.
- Linked selection-key termination costs exactly 23 constraint units: `2D = 2`
  for the head key, `P = 2` for the complete prerequisite, `2D = 2` for the
  prerequisite key, and 17 for groundness and subterm comparison. The complete
  public linked fixture costs 396 constraint units and 22 type units. Splitting
  key authentication from remaining relationship validation only reorders
  existing work and adds zero units.
- Linked authentication costs 151 constraint and 16 type units for the
  ordinary fixture and 167 constraint and 16 type units for the determined
  fixture. Determinant authentication accounts for the 16-unit constraint
  delta.
- The linked registry boundary remains exactly 102 constraint units.
- At calibrated width `W = 4890`, the driver boundaries are entry
  `64W + 13`, linked `67W + 25 = 327655`, and validation
  `118W + 80 = 577100`. The unchanged production limit remains 327680, so
  `327655 < 327680 < 577100`.

Focused verification passes with these counts:

```text
cargo test --locked --lib                                      # 771 passed
cargo test --locked --test interfaces                          # 40 passed
cargo test --locked --test implementations                     # 73 passed
cargo test --locked --test diagnostics                         # 44 passed
cargo test --locked --test interface_generic_summary           # 4 passed
cargo test --locked --test interface_identity_diamond          # 2 passed
cargo test --locked --test interface_modules                   # 23 passed
cargo test --locked --lib -- resolved                          # 111 passed
cargo test --locked --lib -- evidence_validation               # 108 passed
```

The named exact and one-short resource tests, `cargo fmt --check`,
`cargo check --locked --all-targets`, strict workspace all-target/all-feature
Clippy, and `git diff --check` also pass. The controller repeats the complete
Checkpoint 4 command set after this documentation-only closure edit. CP4 does
not claim a `cargo xtask verify` run.

Independent review proceeded in stages. The implementation Task A and B
semantic reviews approved their behavior. Rust/resource review found uncharged
infallible determinant and header related-label retention; the charged fallible
fix and its exact 14- and 59-unit tests passed re-review. CP4 Step 5 semantic
review then found that detached summaries did not recheck full-vector
variable-head, dependent-coverage, and orphan relationships after a valid
alternate-key mutation. The correction passed semantic re-review. Step 5
Rust/resource review found allocate-before-charge ordering in the two mirrored
selection-key collectors; the corrections and exact staging tests passed
re-review.

The final whole semantic review then reported one important linked-validation
finding: generic prerequisite termination still followed complete applications,
and a relationship could read another group's key before that key was
authenticated. The correction authenticates all group keys in phase one, uses
selection-key termination in phase two, accepts honest dependent growth, and
rejects coherent dependent-only shrink. The same review reported one minor API
finding: public raw determinant getters exposed representation rather than
behavior. The getters are now `pub(crate)`, exact representation evidence lives
in a crate unit test, and public integrations assert behavior. Semantic
re-review approves both final corrections without findings. A fresh whole
Rust/resource review independently approves the complete checkpoint without
findings.

The checkpoint deviated from its evidence plan in these recorded ways:

- The initial file list omitted `src/driver.rs`, `src/kind.rs`,
  `src/resolve.rs`, and `src/resolve/module_tests.rs`. Existing driver,
  body-free kind, summary-publication, and detached summary-authentication
  owners and fixtures required their migrations. The planned `src/evidence.rs`
  edit was unnecessary because the existing fact/evidence boundary already
  carries the private metadata.
- Honest determined-summary accounting adds key-position work at the exact
  publication, detached-authentication, and linked boundaries recorded above.
- Semantic review exposed a global failure-precedence defect: an earlier valid
  edge method seed or kind could preempt a later malformed application. The
  unconditional arity pass, conditional positional kind pass, and elaboration
  arity preflight correct it. Narrowing the driver fixture from 4,900 to 4,890
  preserves the boundary inequality without raising the production limit.
- The Task B summary-pair test and the Step 5 first-combiner and stable-diamond
  extensions were immediately GREEN because their shared implementation was
  already present. They remain evidence; they do not indicate missing
  behavior.
- Summary mutation evidence is split by owner. Source-to-summary publication
  owns the pure source/key mismatch. Detached admission owns structural
  malformation and relationship-changing valid alternate keys; it does not add
  a redundant source-edge carrier.
- Linked token and fact `WrongInterface` determinant rows duplicated position
  mismatches because position-only keys carry no interface identity. Removing
  them leaves 21 independent linked mutations. Enclosing token and fact guards
  continue to authenticate interface identity.
- The two selection-key collectors initially reserved before their owning
  charge. Moving aggregate charge before reserve changed staging, not totals.
- Final whole semantic review found that linked generic prerequisite
  authentication still used complete-application termination and could consult
  a group key before authenticating it. The two-phase validation correction
  authenticates every group key first and then applies selection-key
  termination. Honest dependent-growth and coherently tampered
  dependent-only-shrink cases retain the boundary. The phase split adds no
  resource work.
- The same review found that raw determinant getters exposed a minor public
  representation API. They are now crate-private, exact position evidence moved
  to a crate unit test, and public integration evidence asserts behavior.
  Semantic re-review approves both final corrections.

Cumulative reserved use is 40/65; 25 units remain. Neither TASK-0018 nor
lib-ash is complete. `spec/` remains unchanged through Checkpoint 6; Checkpoint
7 retains the normative reconciliation allocation.

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
