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

The user authorizes finishing Task 5, then merging and reconciling the closed
checkpoint into `integration/effect-ash-foundations`. Apply its accepted
worktree lifecycle after verification and ancestry checks. This does not
authorize a push, tag, or merge into `main`. Intermediate commits must not be
GPG-signed.

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
- Tasks 2–4 are retained through `b5f6c12`: syntax, lexical facts, outward
  escape, one Core scope carrier, transforms, and erased evaluation.
- Task 5 is complete through its verification gate. Specification examples and
  the rule manifest were
  first tested against the previous specification and failed for the missing
  documented examples/rules. Independent closure reviews identified bounded
  inference, linked/Core binder, representation-scope, and resource-accounting
  corrections, with regression tests preceding the fixes.
- Corrective code is retained at `f7c657b`. The accompanying specification and
  example harness close the accepted semantic delta. The retained
  [evidence report](../design/effect-ash/local-newtype-evidence.md) records the
  exact resource formulas, reviews, corrections, and intentional exclusions.
- The user authorizes finishing Task 5 and merging and reconciling the closed
  checkpoint into `integration/effect-ash-foundations`. All review agents use
  high reasoning as the upper bound. The existing integration branch adds only
  the accepted milestone worktree lifecycle to the `fa26025` product baseline.

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

The final gate passed on 2026-09-05: `CARGO_INCREMENTAL=0 cargo xtask verify`
completed format, metadata, build, Clippy, all 1,968 tests in 59 test binaries,
and rustdoc with warnings denied. This included 20 local-newtype tests, 71
specification examples, and 31 architecture checks. Markdown lint and diff
checks passed; changed relative links and the manual obligations above were
reviewed. The initial full run exposed an elaborator stack-frame regression;
helper extraction restored the original 256 KiB predecessor without changing
stack limits, semantic operations, or work charges.

Independent semantic/specification, compiler/Core, and Rust/resource reviews
covered the complete checkpoint from `fa26025`, including the corrections
after `b5f6c12`, and closed with no outstanding Critical or Important findings.
All reviewers used high reasoning. The specification commit retains this
record; the following closure commit removes the transition artifacts before
the separately authorized local integration.

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

Closure review found accepted cases that the earlier focused evidence had not
carried through linking, Core, or final inference closure. The retained
corrections cover enclosing inference escape, delayed relational improvement,
parameterized lexical facts, captured global and implementation parameters,
unused representation dependencies, and charge-before-retention ordering.
They reuse the accepted mechanisms and require no semantic amendment.

The current user instruction extends the plan's former leave-unmerged endpoint
to include verified local integration. It does not extend language scope.
