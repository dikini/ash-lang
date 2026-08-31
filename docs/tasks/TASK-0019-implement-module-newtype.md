# TASK-0019: Implement Module `newtype`

- ID: `TASK-0019`
- Status: active
- Related:
  - [CP-0012](../proposals/CP-0012-module-newtype.md)
  - [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md)
  - [DN-0027](../design/DN-0027-effect-ash-program-design.md)
  - [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md)
  - [Execution plan](../plans/2026-08-31-module-newtype.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

CP-0012 is accepted after independent semantic, compiler/Core, and
Rust/resource review. The current `d1e323d` `main` remains the pure predecessor
and passes `cargo xtask verify`. Product work will use the isolated
`.worktree/cp0012-module-newtype` worktree and the
`feature/cp0012-module-newtype` branch rooted at that baseline. The accepted
proposal follows the reviewed planning commits `f79ce51`, `65b339c`,
`328c4a5`, and `209bfe5`, in that order. Those commits and the authorization
commit containing this task and plan cross onto the product branch as
transition authority; they do not make `newtype` current Ash.

Stop and return to CP-0012 if implementation needs a semantic rule absent from
the proposal. Do not add local or runtime-fresh identity, implicit coercion,
representation-derived evidence, recursive zero-storage representation,
local implementations or changed overlap/orphan rules, effects, resources,
providers, hooks, proof evidence, existential packaging, dynamic loading,
runtime type tags, a value-level registry, a heap-inspection API, special
`newtype` rendering, an ABI or foreign-representation guarantee, or a
production resource-limit increase.

Do not merge or push the product branch, tag a checkpoint or Effects Ash
milestone, delete a branch, or remove a worktree without separate user
direction. The Effects Ash milestone must receive independent final review
before any merge is considered.

## Work

Execute the linked plan to:

- reserve and project the `newtype` keyword and exact declaration shape while
  preserving token-complete recovery and syntax-resource accounting;
- retain explicit declaration kind, module-owned nominal and constructor
  identities, ordered parameters, one canonical representation template, and
  visibility through resolution and body-free summaries;
- kind-check all ordinary payloads and `newtype` representations before one
  deterministic, iterative, type-work-budgeted representation-cycle pass;
- type explicit wrapping and irrefutable matching without equating the nominal
  and representation types or lifting interface evidence;
- lower constructor values through fresh generated type binders and a unary
  function whose body contains an authenticated representation conversion;
- extend pure typed Core, both transforms, independent validation, and the
  explicit evaluator machine so conversion erases without wrapper allocation;
- retain positive, negative, import, opacity, diamond, tamper, failure-order,
  exact-resource, retry, and stack-safe teardown evidence; and
- reconcile every affected specification section, retain an Effects Ash
  evidence report, complete independent reviews and full verification, then
  remove the completed transition artifacts from the product branch.

## Progress

- CP-0012 is accepted with no remaining Critical or Important review finding.
- Repository mapping found one existing nominal pipeline from surface syntax
  through resolution, summaries, checking, Core, and evaluation. The task adds
  an explicit declaration kind and canonical representation relation to that
  path rather than introducing parallel subsystems.
- The pure `d1e323d` baseline passes `cargo xtask verify`, including formatting,
  build, Clippy, all tests, and Rustdoc.
- The product branch carries the reviewed planning and authorization history as
  unsigned commits `9b483ce`, `d542103`, `a0996d1`, `487ed30`, and `686011c`.
  It contains exactly five commits after `d1e323d`, has no `src/` or `spec/`
  delta, and is clean before product implementation.
- Checkpoint 2 is complete at unsigned commit `be4e2e5`. The retained RED showed
  `newtype` lexing as an ordinary identifier. The GREEN boundary reserves the
  keyword, projects one explicit nominal declaration kind through the existing
  type-declaration order, owns malformed one-constructor/one-field recovery,
  defers constructor-name equality to resolution, and proves exact cumulative
  syntax work, one-short failure, retry, and identifier-position migration.
  Focused lexer, parser, projection, formatting, all-target check, and diff
  hygiene pass. Independent semantic/Core and Rust/resource reviews approve
  the checkpoint with no remaining finding.
- Checkpoint 3 is complete at unsigned commit `c7c2fa1`. The retained RED showed
  that resolved declarations and summaries had no `newtype` identity or
  representation carrier. The GREEN boundary preserves one authenticated
  canonical representation and its provenance through transparent, opaque,
  hidden, imported, and re-exported routes; validates owner-scoped parameters
  and declaration origins; kind-checks representations before an iterative,
  newtype-only cycle pass; and refuses constructor expressions and patterns
  until Checkpoint 4 can lower explicit conversions. Exact, one-short, retry,
  facade-diamond, malformed-summary, cycle, and stack-safe teardown evidence
  passes. Independent semantic/Core and Rust/resource reviews approve the
  corrected checkpoint with no remaining finding.
- No normative specification file has changed.

## Verification

Each product checkpoint must preserve its first RED witness, pass focused GREEN
commands, receive independent semantic/Core and Rust/resource review, correct
every Critical or Important finding, and end with formatting, all-target
checking, status inspection, and diff hygiene.

The final gate is:

```text
cargo xtask verify
markdownlint --disable MD013 -- docs spec README.md AGENTS.md
git diff --check
git status --short
```

Manual verification checks changed relative links, formal notation, executable
specification examples, artifact authority, diagnostic precedence, exact
resource formulas, atomic publication and retry, stack-safe disposal, closed
pure Core and evaluator inventories, and the absence of wrapper allocation.

## Discoveries

Ordinary one-field data cannot identify a `newtype`; declaration kind must
cross every authenticated carrier. One canonical representation template must
derive constructor, matching, and conversion views so summary and Core facts
cannot diverge.

Source access belongs to resolution and linked-summary admission. Core has no
import-route information and validates only the linked canonical conversion
relation. Parameterized constructor values require fresh Core type binders;
the canonical declaration parameters remain the position-and-kind substitution
authority and are never rebound.

The representation graph belongs to module type work after all payload and
representation kind checking and before interfaces. Core validation retains
its separate resource ledger and failure reason.

## Deviations

None.
