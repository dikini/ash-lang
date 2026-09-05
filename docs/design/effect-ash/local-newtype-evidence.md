# Local `newtype` evidence

This report retains evidence for the local-newtype product checkpoint from
`fa26025`, the combined module-newtype and resume-required kernel baseline.
It is informative. The [branch specification](../../../spec/README.md) defines
the implemented boundary; integration into `main` and the wider Effects Ash
milestone remain separate.

## Retained boundary

CP-0014 was accepted at `e42bcfd`; TASK-0022 authorized implementation at
`48260bd`. Syntax, lexical facts, and escape/scope implementation were retained
at `39cfb93`, `f22586d`, and `bf1d22c`, with closure corrections through `f7c657b`.
Git retains these transition artifacts after closure.

Local declarations are private and sequential. Each source declaration has one
stable compile-time lexical nominal identity. Its representation uses preceding
nominals and enclosing type parameters, extended with its own fixed-kinded
parameters. Names and constructors shadow and restore together. The identity
cannot escape through an outward type, row, scheme, requirement, or inferred
enclosing binding. A closure may retain the erased representation when its
exposed computation contains no local identity.

The implementation reuses nominal equality, constructor schemes, type traversal,
representation conversions, and ordinary closure environments. One unary
`LocalNominalScope` in the shared pure Core family authenticates the lexical
boundary. Canonical lexical facts stay out of summaries and imports. The
evaluator enters the child directly without a new value, heap cell, environment
entry, continuation frame, identity, or runtime registry.

## Evidence map

- `tests/local_newtypes_syntax.rs` covers projection, parameters, malformed
  shape, recovery, token coverage, and excluded visibility syntax. Parser unit
  tests retain exact syntax charging, one-short rejection, and retry.
- `tests/local_newtypes.rs` covers nested and sibling identities, shadowing,
  preceding representations, self/forward/after-scope rejection, recursive-term
  use, summary exclusion, the outward escape matrix, polymorphic consumption,
  and accepted and rejected deep scopes on a small host stack.
- `tests/kinds.rs` covers representation and parameter kind admission.
  `tests/diagnostics.rs` owns the escape reason and causal source labels.
- End-to-end local-newtype tests execute fixed-kinded parameterized
  constructors and following recursive groups, and reject representation-only
  interface evidence. Both transforms revalidate and preserve their results.
- `tests/spec_examples.rs` invokes an identity-free escaping closure after its
  defining scope returns, observes `42 : Int`, checks the stable escape example,
  and retains the normative-rule manifest.
- Core unit and integration tests cover the scope/fact bijection, forged
  owners and metadata, representation dependencies, scope escape, both
  transforms, and revalidation. `tests/effect_runtime.rs` exercises the shared
  scope carrier in Effect Core.
- `eval::machine::tests::local_newtype_closure_allocates_no_wrapper_or_scope_state`
  directly measures zero heap cells and an empty effect trace while invoking
  the escaping closure after its defining scope returns.

## Resource ownership

The existing syntax, type-work, constraint-work, Core-construction, and
Core-validation ledgers remain separate. New proportional work charges before
allocation or publication, and failed attempts leave no checked product.
Owner-local tests retain exact success, one-unit-short failure, retry, and
iterative disposal. No production limit changes.

The principal additive formulas are:

- Resolution retains six fixed units per declaration (nominal, constructor,
  parameter row, arity, and two name entries), plus parameter and representation
  work. `Token(Int)` therefore uses seven units. Lexical lookup charges one unit
  per probed scope, including empty scopes.
- Registry publication charges `2N + 2C` for `N` lexical nominals and `C`
  constructors, plus existing parameter and representation copies. Checker-view
  construction precharges those carriers before cloning; one parameterless
  scalar local costs five units.
- Linked registry retention adds `3N + 2F + 2C` constraint units and
  `4N + F + 2C` type-storage units, plus representation cells, for `F`
  representation facts. Declared parameters additionally use
  `P + 2 * sum(1 + kind_nodes)` type-work units for the retained binder copies.
- Independent lexical registry indices charge `N + 2P`: one nominal identity
  slot and separate parameter-owner and parameter-name slots. The two-scalar,
  one-parameter fixture costs `18 = N + 2P + 2P + 6N`, including record/kind
  comparison and representation/provenance checks.
- Scope/fact bijection checking costs `2L + S` for `L` local facts and `S`
  scope carriers. A first retained local-owner requirement costs one unit;
  copying a retained requirement costs another unit.
- Row inspection charges one row, one optional tail, every known or lacks
  instance, and the existing type traversal for each argument. The retained
  sixteen-member, two-owner row fixture costs 54 units.
- A Unit-typed Core scope uses one construction type-work unit plus ordinary
  node admission. Transforms rebuild through that existing builder boundary.
- Deferred escape retention costs `T + 5U`: `T` visited type cells, `2U` for
  the distinct-inference collection, and `3U` for the retained owner, inference
  identity, and diagnostic span. It retains no type snapshot. Final checking
  charges each inference lookup and the existing zonk/identity traversal;
  an empty deferred list costs zero.
- Deriving a scoped representation costs two validator units for `Int`, or
  four for a template consisting of its own parameter `A`. The additional
  representation-dependency checks cost four units per parameterless scalar
  scope and two per scalar conversion. Enclosing implementation parameters
  reuse authenticated binder mapping and charged graph traversal.
- Finding one captured implementation parameter in one lexical representation
  costs five constraint units per pass: nominal visit, traversal scheduling,
  type visit, variable retention, and parameter comparison. The existing count
  and retention passes charge separately.

The registry, lexical lookup, and Core disposal probes reach depth 32,768 on
bounded host stacks. The end-to-end scope test additionally checks accepted
and rejected source cases without changing production limits.

## Review corrections and closure

Independent compiler/Core and Rust/resource review found gaps in enclosing
inference escape, parameterized lexical facts, enclosing representation
parameters, unused representation dependencies, and charge-before-retention
ordering. Corrections retain the accepted scope and reuse the existing
contexts, nominal facts, binder authentication, and work ledgers.

Independent semantic/specification, compiler/Core, and Rust/resource reviews
covered the complete checkpoint from `fa26025`. All used high reasoning and
closed with no outstanding Critical or Important findings. The semantic review
also checked the final generic-owner and unused-representation tamper cases;
the resource review checked the exact formulas above against the final paths.

The full gate exposed a predecessor stack regression before expression
elaboration began. Moving block finalization and local-scope checks into
dedicated helpers reduced the expression driver's frame from 114,920 to
101,464 bytes. The original 256 KiB type-depth test changed from failure to
success; the 512 KiB pattern test and all 20 local-newtype tests also passed.
This correction changed no semantic operation, work charge, or stack limit.

The final product gate passed on 2026-09-05 at corrective code commit
`f7c657b`, together with the accompanying specification and example harness:

- `CARGO_INCREMENTAL=0 cargo xtask verify`: format, metadata, build, Clippy,
  all 1,968 tests across 59 test binaries, and rustdoc with warnings denied;
- `markdownlint --disable MD013 -- docs spec README.md AGENTS.md`; and
- `git diff --check` and inspection of the complete changed-file list.

The test run included 20 local-newtype cases, 71 specification examples, 31
architecture checks, and the unchanged small-stack predecessor tests. Manual
review covered relative links, formal rules and their prose, executable
examples, diagnostic ownership, Core traversal, resource formulas, atomic
publication and retry, teardown, runtime erasure, and summary/import exclusion.

Scoped exact evidence is the next identity-track checkpoint after integration.
This checkpoint does not add local implementation search, runtime-fresh
acquisition identity, resource lifetime, proof authority, existential packaging,
or a general Core authority framework.
