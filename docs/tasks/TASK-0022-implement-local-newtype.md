# TASK-0022: Implement Local `newtype`

- ID: `TASK-0022`
- Status: active
- Related:
  - [CP-0014](../proposals/CP-0014-local-newtype.md)
  - [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md)
  - [DN-0027](../design/DN-0027-effect-ash-program-design.md)
  - [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md)
  - [Execution plan](../plans/2026-09-02-local-newtype.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

CP-0014 is accepted. The product branch starts from the verified combined
module-`newtype` and effect-kernel checkpoint `fa26025`. The isolated
`.worktree/cp0014-local-newtype` worktree uses
`feature/cp0014-local-newtype`; `main` remains unchanged.

Return to CP-0014 if implementation requires a semantic rule absent from the
proposal. Do not add another nominal pipeline, existential packaging,
runtime-fresh identity, local implementation search, resource lifetime rules,
or a general Core authority framework.

Do not merge or push the branch, tag a checkpoint or milestone, delete a
branch, or remove a worktree without separate direction. Do not merge the
Effects Ash milestone without independent final review. Intermediate commits
must not be GPG-signed.

## Work

Execute the linked plan to:

- parse and project the module `newtype` shape as a private sequential block
  declaration;
- add stable lexical nominal ownership and scoped name lookup while reusing
  existing nominal facts and representation resolution;
- retain local canonical facts only for checking and linked Core;
- reuse constructor typing, pattern typing, conversions, and erasure;
- reject local identity in every outward type, row, scheme, or requirement
  while accepting identity-free closure capture;
- add one erased Core local-nominal scope carrier and independently validate
  its exact ownership; and
- retain behavioral, tamper, resource, teardown, migration, and specification
  evidence before closing the transition artifacts.

## Progress

- CP-0014 records the accepted identity-free closure boundary.
- Compiler and resource audits found that the module-newtype parser, fact
  shapes, kinding, constructor and pattern typing, conversion node, transforms,
  and evaluator erasure are reusable.
- Module registry invariants require lexical owner distinction and logically
  separate local facts, but not a second type or conversion system.
- `CARGO_INCREMENTAL=0 cargo test --locked --workspace` passes at the product
  baseline, including 902 library tests and every integration and doc test.
- No Rust or normative specification file has changed.

## Verification

Each implementation checkpoint preserves its RED witness, runs focused GREEN
tests, checks formatting and diff hygiene, and uses unsigned commits. Review
semantic/Core and Rust/resource boundaries at the two implementation gates,
then correct every Critical or Important finding.

The final gate is:

```text
cargo xtask verify
markdownlint --disable MD013 -- docs spec README.md AGENTS.md
git diff --check
git status --short
```

Manual verification checks relative links, artifact authority, diagnostic
ownership, exact resource accounting, atomic publication and retry,
stack-safe disposal, complete Core carrier traversal, runtime erasure, and the
absence of local facts from summaries and imports.

## Discoveries

The existing module registry validates dense module declaration ordinals and
exportable module ownership. Local facts need a lexical owner and a separate
retained partition, while shared lookup can continue to return the existing
nominal and constructor fact types.

The elaborator's reverse block fold is the exact point to wrap the following
remainder in one local-nominal Core scope. The existing iterative nominal
identity traversal already reaches function types, effect rows, and effect
arguments and should own outward escape inspection.

## Deviations

None.
