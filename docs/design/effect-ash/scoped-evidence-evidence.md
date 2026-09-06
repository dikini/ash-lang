# Scoped exact evidence

This report retains implementation and review evidence from `90f517d`, the
combined module/local-newtype and resume-required kernel baseline. It is
informative. Both independent reviews, the full gate, and transition artifacts
are closed; the checkpoint is locally integrated. The branch specification is prepared
with the implementation. Neither this report nor milestone integration makes
the change current on `main`.

## Retained boundary

CP-0015 was accepted at `2f657d8` under the user's request to implement the
bounded slice autonomously. TASK-0025 and its execution plan were activated at
`cee0af0`. The first direct/forwarding path is retained at `f01e8e3`; method and
selection interactions are retained at `d87203d`.
The reviewed nested-body scheduling correction is retained at `bceb688`.
Complete source/capture/header authentication and resource corrections are
retained at `85bbe0d`.
The specification, executable examples, and evidence are retained at `c16cd5d`.
CP-0015, TASK-0025, and its execution plan were removed from the product tree after this
verified checkpoint; Git retains their transition authority and work history.

Sequential private `with` declarations supply every method for one exact
complete interface application. Its selection key must contain an active local
nominal identity. Abstract requirements and exact-current evidence precede the
lexical source; concrete matching follows it. Improvement retains the existing
fixed snapshot and single transactional forward pass. Recursive prerequisites
still select by complete goal, not by a new determinant-key barrier.

One flat parent link per source and one optional head per pending occurrence
retain the occurrence's original lexical scope through deferred inference.
Independent linked validation reconstructs scope from the ordered resolved
tree. Supplied bodies see preceding values and evidence, with no implicit self
or sibling selection. Their contextual method parameters are independently
rigid and introduce no source type names.

Lowering uses ordinary nonrecursive bindings, functions, captures, type
abstractions, and applications. The existing method-evidence catalog retains
inert owner/use authentication facts; it is not a runtime registry. Lexical
facts do not enter summaries or imports. This adds no runtime identity,
dictionary, evaluator operation, proof authority, existential package,
acquisition, resource lifetime, or checked-discard rule.

## Behavioral evidence

- `tests/scoped_evidence.rs` carries the complete pure relation through direct
  and constrained calls, linked authentication, Core validation, and execution.
  Both observe `42`.
- `tests/scoped_evidence_syntax.rs` covers sequential projection and excludes
  module, visibility, head-parameter, prerequisite, and recursive-group forms.
- The verified 50-case interaction corpus covers exact
  identity and key admission; deterministic method membership and diagnostics;
  lexical/concrete priority; enclosing abstract/current context; mandatory
  improvement conflicts; fixed-snapshot and delayed closure behavior; recursive
  complete-goal prerequisites; polymorphic and higher-kinded methods; and
  enclosing parameters.
  Two final cases preserve an enclosing generic implementation parameter,
  including an unused dependent absent from the method type and representation.
- Closure cases execute selected methods after their evidence block returns
  and identity-free closures after their nominal scope returns. Disjoint
  sources can supply different behavior for the same identity. Repeated
  evaluation of one static source preserves distinct ordinary captures.
  A cross-module factory exports its ordinary closure without exporting its
  private interface or lexical evidence.
- Method bodies may capture preceding recursive functions but gain no implicit
  self or sibling evidence. Effect cases preserve rows, operation/resume
  traces, and nested handler ownership, while rejecting enclosing resume
  capture. Accepted interaction cases revalidate both Core transforms and
  preserve their values; effect cases also preserve their traces.
- `tests/spec_examples.rs` adds the direct/forwarding example, the owned
  missing-local-key rejection, and a normative-fragment manifest. The
  suite contains 74 tests.

## Review corrections

Independent high-reasoning semantic and Rust/resource reviews covered the
complete `90f517d`-to-product diff. Both closed without outstanding Critical or
Important findings after the following corrections.

- Supplied methods receive independent declaration-context rigids. Nested
  methods do not reuse canonical interface parameter identities. Existing
  canonical substitution coalesces closed effect instances; contextual body
  weakening uses the existing row subset relation.
- Linked validation derives preceding evidence and nominal scope from the
  ordered resolved tree. Complete-goal checks reject concrete substitution for
  an available exact lexical source while preserving the different-dependent
  recursive-prerequisite fallback.
- Complete headers participate in nominal and rigid scope checks even when an
  argument occurs in no method type. Authenticated enclosing implementation and
  lexical-method mappings apply only beneath their actual Core subtrees.
  Supplementary implementation owners are retained only for lexical-header
  dependencies, after the original catalog stages.
- Core authenticates contextual parameter count, membership, module, positional
  kinds and spellings, ordered identities, group provenance, and exclusive
  ownership. Generated Core alpha-renaming stays independent.
- Every lexical header also passes the existing complete-application kind
  checker. The last regression coherently changed an unused dependent from
  `Int` to unapplied `Box` in both its catalog owner and matching anchor.
  Core accepted it before correction. The unchanged valid fixture passes;
  the malformed complete header now rejects.
- Capture authentication preserves ordered occurrences, not just a binder set.
  Retargeting one occurrence in `x + x + y` initially escaped set-based
  checking. Owner/ordinal anchors now identify each use. Distinct ordinals
  cannot share one node within an owner; nested owners may share an occurrence.
  Temporary address-based routing never dereferences addresses and remains
  local to synthesis; only canonical identities survive.
- Linked validation rejects empty retained method groups and wrong equation
  binders even for unused sources. It charges the equation scan before work.
- Nested supplied bodies use the existing projector, resolver, and elaborator
  queues. Final outer Core construction happens after the body driver returns.
  Shared equation preparation/finishing and a small continuation payload
  preserve the historical 256 KiB predecessor and new depth-32/512 KiB success
  and rejection cases. No stack or production limit was raised.
- Handler cleanup preserves the original supplied-body diagnostic under the
  existing poisoned-elaborator contract, rather than replacing it with an
  internal cleanup error.
- Deep replacement retention and four temporary-Type failure paths use the
  existing iterative owners through fallible work. Separate depth-16,384,
  256 KiB regressions first overflowed during selection, scheduling, or method
  finishing; they now report structured failure without recursive teardown.
  New vectors and replacement storage reserve fallibly after precharging.

Two proposed negative tests were rejected during review. Reordering intact
supplied groups is valid because interface order defines canonical slots.
Coherently renaming otherwise unobserved placeholders and diagnostic origins
preserved actual type and scope relations; it did not justify universal
source-provenance authority.

## Additive work and failure evidence

The following are implementation accounting formulas, not language limits.
Existing type walks, kind operations, and source-free paths retain their owners.
Focused tests require exact success, one-short failure, and a fresh valid retry;
publication checks reject partial sources, selections, and Core results.

### Selector

Let `w(T)` be existing constraint-budget type-walk cost and `h` indicate a
retained lexical head. Source ingress costs `2 + sum(w(arguments))`; owned
pending ingress costs `1 + h + sum(w(arguments))`. For `<N, Int>`, these are
six and `5 + h` constraint units.

Cloned method ingress costs `2 + m + r + v + h`, plus application/method
argument and retained-value type walks. Here `m` counts method arguments,
`r` is zero or one plus rigid arguments, and `v` marks a checked value type.
The conditional-method fixture costs `14 + h` constraint units and four
type-work units. Tests cover scope-chain depths zero, one, and 256; failures
preserve earlier records and occurrence-owned heads through later traversal.

### Elaboration and resolution

Declaration preparation without preceding lexical sources costs
`3M + K + sum(P) + MG + G` constraint units in checking and
`4M + K + sum(P) + MG + G` in synthesis. Here `M` counts interface methods,
`G` supplied groups, `K` key positions, and `P` copied interface parameters
per method. The one-method `Read<N, Int>` fixture costs eight and nine.
Replacement-map reservation separately costs `P + Q` type-work units per
method, with `Q` method-local parameters, before argument cloning.

Cleanup precharges `(M + 1)C` for `M` members and backing-map capacity `C`
before removing the declaration from its iterative owner. The sparse-capacity
test fills 128 entries, clears them, and retains one without shrinking.

Resolver method lookup costs `I + M + 2P + 2C`: local interface-table width
`I`, canonical method width `M`, two `P`-slot parameter buffers, and two
metadata copies with existing cost `C`. Imported lookup omits `I` because
the interface is indexed. Tests vary local/imported widths and parameter counts.
Unknown methods deferred to membership checking add no lookup work.

### Linked checks and capture collection

The two-method linked node fixture costs 16 constraint units. Owner retention
costs `30 + 2T` for complete method-table width `T`: 34 at width two and 40
at width five. Block scheduling costs 12 for that lexical fixture versus eight
for its source-free predecessor. Lexical plan ingress costs `1 + M` for
`M` method IDs.

The header-only scope pass costs 50 constraint and three type-work units for
its fixture. Empty-owner gating adds zero to either budget. Lexical-header
dependency detection has a seven-constraint-unit helper fixture; Core's
two-parameter authentication fixture costs eleven type-work units.

The audit group fixture costs `2 + G + GE`: declaration, `G` groups, result,
and `GE` equation slots. Kind checking precharges `G` group visits in addition
to unchanged header checks and equation-edge charges. Empty groups therefore
remain bounded.

The borrowed capture walker returns `y, x, x` in occurrence order. Its simple
fixture costs eleven type-work units, or fourteen with binder retention. Nested
groups cost `7 + G + 5GE`. Routing adds fourteen collection units and nine
lookup units for three captures, separately from ordinary synthesis scheduling.
Builder and Core tests cover exact capture-owner lookup, anchor publication,
initializer-subtree membership, duplicate-use exclusion, and source-free gates.
The builder fixture costs `19 + A + 7R` per anchor, where `A` counts prior
anchors and `R` reached expectations; existing builder setup retains two
carriers per expectation. Core capture envelopes cost
`A + sum(1 + H + S_i)`: all-anchor visits `A`, backing-map capacity `H`, and
subtree work `S_i = 1 + popped nodes + scheduled edges` per capture. Sparse
capacity and fresh-validator retries are included.

### Core complete headers and prerequisites

A concrete lexical prerequisite precharges `L + M` for owner and method scans.
The smallest regression previously used eleven units instead of thirteen;
one/two-method and unrelated-owner fixtures cover exact boundaries.

Complete-header kind checking adds `L + L*M` scan units, for `L` lexical
method-owner rows and `M` catalog methods, plus existing argument synthesis
and kind-comparison costs. No lexical owners add no work. The one-owner,
one-method, two-argument fixture costs eleven units including five existing
catalog checks; it passes exact, one-short, and fresh retry probes.

## Verification

The baseline full gate passed on 2026-09-05: formatting, metadata, build,
Clippy, 1,968 tests across 59 binaries, and rustdoc with warnings denied.
The vertical, interaction, and scheduling commits above each retain their
review and focused verification in Git history.

Before the last header-kind correction, the stable tree passed 978 library
tests, all-target Clippy with warnings denied, and 221 tests across eight
targets: 31 architecture, 32 data/ADT, six interface-resource, 20 local-newtype,
two vertical, 50 interaction, six syntax, and 74 executable-specification tests.
The architecture inventory names only actual new static carriers; scanner
rules, runtime inventories, and production limits are unchanged.

After the correction, all 979 library tests passed. The final exact-budget
assertions passed in a separate fresh run. Both independent reviewers closed
the correction; the complete semantic and code/resource reviews remain closed.
The full `CARGO_INCREMENTAL=0 cargo xtask verify` gate passed on 2026-09-06:
formatting, metadata, build, Clippy, 2,088 tests across 62 binaries, and rustdoc
with warnings denied. Markdown lint and diff checks passed after consolidation;
all 194 local file links in the thirteen changed Markdown files resolved.
After transition cleanup, Markdown lint and diff checks pass, and all 187
remaining local file links in the thirteen changed Markdown files resolve.

The requirement audit found no missing evidence category. Manual ordering
review confirms resolution and header arity/kinds before local-key admission,
then active-key conflicts, complete membership, and body checking. The corpus
isolates key-before-membership and duplicate-before-membership; it does not
claim a separate executable test for every mixed-error combination. Grammar
and selection-rule notation agree with their prose; the specification changes
retain the proposal's explicit non-goals and branch-versus-main distinction.

An isolated target directory with incremental compilation disabled avoids a
corrupted pre-existing build cache. Ignored build logs are disposable and carry
no semantic authority.

## Local integration

The explicit merge `1f691ad2282d25e18eb4732eed7b2cd36240c28d` retains exact
feature tip `64bcf494f71d04ec38a7369fab7e11ab13032638` on
`integration/effect-ash-foundations`. Both tips have tree
`a5e21c0f8ed6270f9b6cc979fb5dbea50a896a45`; the merge changed no product content.
Integration documentation now records that retained boundary. A fresh full
`CARGO_INCREMENTAL=0 cargo xtask verify` run from the integration checkout passed
on 2026-09-06: formatting, metadata, build, Clippy, 2,088 tests across 62 binaries,
and rustdoc with warnings denied. Only integration-status documentation differs
from the merged feature tree. Markdown lint, diff checks, and all 188 local
file links in the thirteen changed Markdown files pass.

After proving the feature checkout clean and its exact tip an ancestor of
integration, `git worktree remove` removed `.worktree/scoped-exact-evidence`
and its disposable build cache. The merged `codex/scoped-exact-evidence` branch
was deleted. Its commits remain reachable through integration. Only
`.worktree/effect-ash-foundations` remains under the repository's `.worktree/`.
Main stays at `7195500b7a165f8191efa1485e1ca6f4114180fb`; its unrelated tracked
and untracked changes, the two historical worktrees, other branch refs, remote
refs, and tags are unchanged. No push or merge into `main` was performed.

## Remaining boundary

Capture/usage and checked discard remain separate work. This slice supplies no
resource-lifetime, provider, proof, existential, acquisition, or runtime-dispatch
authority. Local integration targets `integration/effect-ash-foundations`;
merging into `main`, pushing, and tagging are not authorized by this checkpoint.
