# Synchronous Hooks Implementation Plan

> Execute in this task with subagent-driven development: one product writer,
> then independent semantic and Rust/resource review at each retained increment.

**Goal:** Implement the complete accepted [CP-0018](../proposals/CP-0018-synchronous-typed-hooks.md).

**Architecture:** Reuse exact effect APIs, generated forwarding handlers,
ordinary callback application, saved lexical instantiation and the explicit
machine. Retain authenticated hook-root row behavior and a non-interpreting
registration completion owner outside its generated handler. Extend existing
dependency/control analysis rather than introducing a registry or second engine.

**Tech stack:** Rust; current lexer/parser, resolved and checked summaries,
typed Effect Core, finite capture analysis and explicit evaluator.

**Owner:** [TASK-0028](../tasks/TASK-0028-implement-synchronous-hooks.md).

**Baseline:** `ec8f86165689306a5301732a2ec995f8f7487686`.

## Work and review boundary

- [x] Accepted contract and separate implementation authorization.
- [x] Clean product checkout under `.worktree/synchronous-hooks`.
- [x] Fresh full baseline verification before source or test edits.
- [x] Step 1: primary syntax, projection and fail-closed staging.
- [x] Step 2: authenticated, executable hook roots and absent-target rows.
- [ ] Step 3: registration typing, generated forwarding and completion proof.
- [ ] Step 4: runtime registration ownership and complete source execution.
- [ ] Step 5: full interaction corpus, specification, reviews and verification.
- [ ] Retained checkpoint, transition cleanup, unsigned local integration,
  merged-checkout verification and completed worktree removal.

The parent owns documentation, staging, commits and branch operations. One
high-reasoning implementer owns product/test edits at a time. Independent
semantic review precedes high-reasoning Rust/resource review; documentation
review uses medium. No reasoning level exceeds high. Reviewers do not edit.

Every bounded change starts with a failing test for missing behavior. Record
the exact failing reason; repair malformed fixtures before product edits. Pass
the unchanged witness, add its negative and exact-resource controls, self-review,
then freeze for both reviews. The parent independently repeats the relevant
gate before an unsigned commit. Do not hide a failing predecessor by changing
its expected result, stack size, input depth, resource ceiling or concurrency.

Prefer a small extraction over a general framework. Proportional scans and
retained collections need charged, fallible work and iterative owners from their
first introduction. Update architecture inventories only for real carrier moves
or additions, preserving the existing exhaustive checks and classifications.

## Step 1: Primary syntax and projection

**Files:** `src/lexer/mod.rs`, `src/lexer/token.rs`, `src/parser/mod.rs`,
`src/parser/grammar.rs`, `src/parser/expression.rs`, `src/parser/project.rs`,
`src/surface.rs`, necessary exhaustive surface readers in `src/resolve.rs`;
create `tests/hooks_syntax.rs`. Use `tests/resource_scope_syntax.rs` as the
existing real lexer/parser/projection test pattern, not as a semantic template.

1. Add the following lexer/parser/projection witness before keyword support:

   ```rust
   use ash::{lexer::lex, parser::{parse, project_module}, source::SourceFile};

   fn parses(expression: &str) -> bool {
       let source = SourceFile::new(
           "hooks-syntax.ash",
           format!("main : Unit -> Int\nmain () = {expression}\n"),
       ).unwrap();
       let tree = parse(lex(&source).unwrap());
       tree.lexical_diagnostics().is_empty()
           && tree.parse_diagnostics().is_empty()
           && project_module(&source, &tree).is_ok()
   }

   #[test]
   fn hook_and_registration_forms_parse_as_primary_expressions() {
       for expression in [
           "hook Adjust {\n3\n}",
           "register Adjust increment {\n3\n}",
           "f hook Adjust {\n3\n}",
           "f register Adjust increment {\n3\n}",
       ] {
           assert!(parses(expression), "{expression}");
       }
   }
   ```

2. Run `CARGO_INCREMENTAL=0 cargo test --test hooks_syntax`. Require the
   new-form assertion to fail because the syntax is missing.
3. Add reserved `hook`/`register`, primary-form parsing and exact source-owned
   projection. Unlike existing `resource`, these are primary expressions, not
   only expression prefixes. Preserve complete spans, target arguments and
   transformer-before-body order. Add no source-visible registration binder.
4. Test qualified/generic targets, nested roots/registrations, parenthesized
   non-primary transformers, missing targets/bodies and keyword collisions;
   `publish` remains ordinary. Test structural-depth exhaustion and fresh retry.
   Extend iterative visitors and disposal for every new surface child.
5. Keep new forms fail-closed at resolution until the corresponding typed
   authority exists. Use one narrow temporary rejection, not a fake ordinary
   handler or a public successful checked-module path. Do not define this
   temporary boundary as resulting Ash semantics.
6. Run the following gate, formatting, strict Clippy and both reviews:

   ```text
   CARGO_INCREMENTAL=0 cargo test --lib --test hooks_syntax --test lexer \
     --test parser --test provenance --test resource_scope_syntax \
     --test effect_modules
   cargo fmt --all -- --check
   CARGO_INCREMENTAL=0 cargo clippy --workspace --all-targets --all-features \
     -- -D warnings
   git diff --check
   ```

Retain the reviewed syntax-only increment unsigned. Later steps replace its
temporary rejection as complete semantic boundaries become available.

## Step 2: Exact API and hook-root execution

**Files:** `src/resolve.rs`, `src/resolved.rs`, `src/elaborate.rs`,
`src/core/effect.rs`, `src/core/dialect.rs`, `src/core/validate.rs`,
`src/core/transform.rs`, `src/core/capture.rs`, `src/core/capture/control.rs`,
`src/eval/machine.rs`; create `tests/hooks_typing.rs`, `tests/hooks_modules.rs`,
`tests/hooks_core.rs`, `tests/hooks_runtime.rs` as their first cases are needed.
Change other exhaustive owners only when a new carrier actually crosses them.

1. Start with real-driver root witnesses: `hook Adjust { perform
   Adjust.publish 3 }` returns 3, and `hook Adjust { 42 }` returns 42.
   They currently reach the Step 1 rejection. Pair with wrong API name,
   multiple operations and `Convert<A, B>.publish : A -> B` at equal concrete
   arguments, which must reject `type.hook-api`.
2. Resolve existing effect identity and arguments. Compare the declared generic
   domain/result before use-site substitution, preserving kind/type diagnostic
   precedence. Authenticate the full relation through ordinary module imports,
   facade aliases, hidden facts and final Core; add no hook identity namespace.
3. Retain a typed hook-root distinction while sharing identity-handler behavior.
   Remove an explicitly present target; retain provable absence, including a
   tail with an existing lacks fact; reject unresolved-tail ambiguity. Preserve
   synthesized least rows and ordinary source-handler/Core admission. No dummy
   request, body thunk or unchecked mode that merely skips validation.
4. Retain roots through generic instantiation and both transforms. Use phantom
   payload `Mark<T>.publish : Int -> Int` so `Mark<T>` inside `hook Mark<U>`
   distinguishes later equal and unequal arguments. An equal inner root must
   cut off an outer source handler that transforms the value; a distinct root
   must leave forwarding unchanged. Cover required resource-payload and
   continuation safety, not only final integers.
5. Use ordinary handler/request/resume execution, with exact saved contexts.
   Prove the root's generated identity clause and scope row equation
   independently. Registration remains unavailable until its owner/proof/runtime
   boundaries exist; pure callbacks are not a safe exemption.
6. Run all new hook suites, `effect_core`, `effect_rows`, `effect_runtime`,
   `effect_typing`, `effect_modules`, resource typing/runtime/Core, library,
   architecture, strict Clippy/fmt/diff and both reviews. Add owning exact-work,
   one-short/retry and small-stack controls before retaining the increment.

## Step 3: Registration structure and completion proof

**Files:** Step 2's resolved, elaboration and Core owners;
`src/core/capture.rs`, `src/core/capture/control.rs`, `src/core/capture/value.rs`;
hook typing/module/Core tests and owning validator/capture units.

1. Begin with callback/body typing and the missing discard rejection. An unused
   registration with a pure callback is still a live completion owner; outward
   discard must not become admissible because source contains no publication.
   Pair it with subscriber-local discard preserving every surrounding owner.
2. Evaluate the transformer once before entering its owner. Generate ordinary
   bind, forward-request, callback-application and resume structure in that
   order. Put a non-interpreting registration owner outside the generated
   handler. Do not reuse a cell interpreter as a generic owner or allocate an
   unused cell as a deregistration witness.
3. Calculate outward initializer/body/callback effects and retain forwarded H
   even for unused bodies. Preserve function result B independently of payload
   P. Test outer versus publisher-local handlers, missing outward effects,
   ordinary interception, generic factories and conservative unused-effect rows.
4. Extend required completion and retained callback dependencies using existing
   finite value/control relationships. Registration must disable the shortcut
   that skips inference in programs without discard, cells or portable globals.
   Keep generic target coincidence, restored contexts and imported evidence
   flows; a registration owner is not a fresh type brand proving H disjoint.
5. Use a function-valued payload to show a transformer adding a live-cell
   dependency without changing type. Admit it inside its owner, reject escape;
   reject outward dependent input even if a later callback would erase it.
   Cover actual opaque/facade/method factories, not type-only approximations.
6. Independently reconstruct owners, generated order, rows and dependency/control
   safety in linked Core and after both transforms. Reject detached or duplicated
   owners, changed targets/callbacks/forwarding and forged summary permissions.
   Keep executable registration publication closed until Step 4's ownership is
   complete; never authorize a checked program by an unproved callback class.
7. Run the full hook/capture/effect/resource corpus, library and architecture
   checks, strict Clippy/fmt/diff, exact/one-short/retry and deep disposal tests,
   then semantic and Rust/resource review. Retain this boundary only with clear
   evidence distinguishing structural/proof completion from runtime support.

## Step 4: Runtime registration and complete source execution

**Files:** `src/eval/machine.rs`, `src/eval/value.rs` only if an actual owner
requires it, `src/core/effect.rs` dispatch seams; hook runtime/Core/typing tests,
existing resource/effect predecessor tests and owning machine units.

1. Retain the exact CP-0018 program before implementing execution: outer
   increment, inner double, input 3 must return 8. Reverse nesting must return
   7. Observe the missing runtime behavior before adding transitions.
2. Prepare all fallible state before activating a fresh registration owner.
   Reuse ordinary explicit handler and function execution. Count owners in both
   active frames and captures; normal exit releases capacity once. Callback
   copies remain ordinary functions, not retained registration authority.
3. Run HOOK-03/04/05: initializer once, repeated entries, normal removal, older
   prefix visibility, temporary callback registration, nested root isolation,
   and registration-site effect handling. Resume restores saved entries without
   reacquiring or replaying callbacks; do not copy a global chain snapshot.
4. Run HOOK-06/07: live captured cells, function-valued transformed dependencies,
   same-site overlapping registration activations, outward capture/resume,
   safe local discard and rejected outward/skipped completion. Only now remove
   all temporary registration execution/admission guards and migrate their tests.
5. Add machine-owned exact/one-short capacity and work tests, two fresh retries,
   release/reuse and captured ownership controls. Failed preparation, stale or
   duplicated internal identity checks must publish no partial activation or
   callback invocation. Add deep success and internal failure on fresh small
   stacks, including nested cells and pending resume capabilities.
6. Run all hook suites, every affected predecessor, library, architecture,
   Clippy/fmt/diff and both independent reviews. A passing demo does not close
   the owner, generic, imported, transform, budget or failure cases.

## Step 5: Full contract, specification and closure

The parent updates every CP-0018-named specification/tool area and adds the exact
documented program to `tests/spec_examples.rs`. Its CLI observation is
`8 : Int` plus a newline with empty stderr. Retain
`docs/design/effect-ash/synchronous-hooks-evidence.md` with HOOK-01 through
HOOK-10 mapped to actual tests, exact resource formulas, reviews and limitations.
No design note or task may substitute for updated language truth on the branch.

Run a fresh high-reasoning complete semantic review, then high-reasoning
Rust/resource review and medium documentation audit. Preserve the accepted
boundaries for effects, proofs, existentials and later cleanup; remove machinery
that has no current consumer, without pruning required behavior or tests.

```text
CARGO_INCREMENTAL=0 cargo xtask verify
markdownlint --disable MD013 -- docs spec
git diff --check
```

Check local links/anchors, formal notation, exact examples, diagnostic ownership
and current/proposed authority manually. Full verification must include the
unchanged deep Pure, interface and recursion predecessors, not only hook tests.
Record process exit status and counts; do not restart a live verification run
because its observation timed out.

Retain one complete unsigned product checkpoint before deleting CP-0018,
TASK-0028 and this task-owned plan with their index entries. Recreate the local
integration checkout, merge with an explicit unsigned commit, verify the merged
product, then prove feature cleanliness and ancestry before removing its
worktree/branch. Preserve main's original edits and remote/tag refs. No main
integration, push or milestone tag is authorized by this plan.

## Execution record

The product branch starts at the accepted proposal tip. Only task/plan/status
documentation changes precede the fresh full baseline gate. No implementation
step is complete at plan creation. The original nine-unit milestone weight
remains open until the complete verified local checkpoint closes.

The fresh baseline completed with exit status zero before product edits:
`CARGO_INCREMENTAL=0 cargo xtask verify`, including 1,099 library tests, all
integration suites, strict Clippy and rustdoc. Step 1 may now modify product
source and tests under its fail-closed boundary.

Step 1 passed independent high-reasoning semantic and Rust/resource review.
The original missing-syntax witness failed before implementation and now passes.
The parent repeated the complete focused gate: 1,101 library tests, seven hook
syntax tests and 93 predecessor tests passed, as did formatting, strict Clippy,
the bidirectional architecture inventory check and diff checks. The inventory
adds only nine actual fields; its scanner and limits are unchanged. Both forms
remain rejected at resolution until their later typed authority is implemented.

Step 2 passed independent high-reasoning semantic and Rust/resource review after
correcting exact-row diagnostic precedence, identity-pattern origin checking and
two partial-target-clone failure paths. The final parent gate passed 1,111 library
tests and 176 focused hook/effect/resource tests, formatting and strict Clippy.
All 32 architecture checks passed before the final root-only clone correction;
that correction changes no carriers. Original RED witnesses cover unavailable
roots, the two semantic gaps and small-stack partial-clone failure. GREEN
evidence includes exact/one-short/fresh-retry work, row rollback, imported
open-lacks helpers, both transforms and the predecessor-shaped 24-root pipeline
on a 256 KiB stack. The full driver wrapper is not covered by that stack claim.
Registration remains rejected until its completion proof and runtime are ready.
