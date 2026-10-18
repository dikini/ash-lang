# TASK-0046: Generic Cell Contents and Dependencies

- ID: `TASK-0046`
- Status: active
- Related: [CP-0023](../proposals/CP-0023-scoped-generic-cells.md),
  [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md),
  [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md),
  [TASK-0048](TASK-0048-generic-cell-integrated-verification.md),
  [TASK-0049](TASK-0049-close-generic-cell-checkpoint.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

Start connected implementation from TASK-0045's reviewed foundation receipt,
not from completion of all its acceptance cases. Use CP-0023 and the pinned
ash-ffi base identified in TASK-0049. Coordinate shared elaboration, summary and
Core writers; TASK-0047 can develop runtime behavior against the same agreed
carrier. Public checked admission requires this task's dependency checks.

## Work

1. Track current cell contents separately from access and earlier read results.
   Propagate possible targets and value relationships through aliases, selected
   fields, closures, evidence, indexed operation metadata, imports, type/row
   instantiation, branches and recursive calls. Preserve each earlier snapshot
   rather than updating it with the slot's later contents.
2. Prove strict enclosing-owner dependencies for initialization and actual slot
   replacements. Reject self-retention, indirect resource cycles and younger or
   incomparable owners, including hidden captures. Do not reject permitted
   immutable cycles or mistake recursive activations of one site for one owner.
3. Follow exact handler selection and actual replies. An intercepted request
   contributes no builtin replacement, but clause, other-handler and resumed-
   computation mutations update contents facts in order. Preserve both
   CELL-P13's independent reply and CELL-N12's dependent later read.
4. Preserve the existing outward payload-crossing, scoped escape, native
   revocation and structural completion rules. Add source diagnostics at the
   causal retention/escape with the precedence required by CP-0023.
5. Carry the inferred relationships through public helper summaries and linked
   preparation. Independently reconstruct them from admitted linked Core;
   source summaries, cached assertions or runtime key checks supply no substitute
   authority. Copying, restoration and transforms must re-establish the proof.
6. Make joins and recursive analysis finite and charged before proportional
   work or retention. Refuse without partial module/summary/permission publication
   and permit a fresh sufficient-budget retry. Required positive cases cannot
   be dropped as a shortcut to termination.
7. Update static semantics and the dependency/summary/Core validation portions
   of elaboration with the delivered behavior. Record algorithm choices and
   measured limitations without adding source lifetime or capture annotations.

Start from baseline `src/core/capture.rs`, `src/core/capture/value.rs`,
`src/core/capture/control.rs`, `src/elaborate.rs`, `src/resolved.rs`,
`src/core/validate.rs` and `src/core/transform.rs`. Keep source admission and
independent linked validation distinct even if they reuse authenticated data
structures or analysis machinery.

## Progress

Implementation has not started. All acceptance remains pending.

- [ ] CELL-P02: earlier scalar snapshots and snapshot-only closures escape with
  their original value after replacement.
- [ ] CELL-P03: inner cells retain and return outer access while its owner lives.
- [ ] CELL-P04: an earlier independent function snapshot escapes after a later
  outer-dependent replacement and still returns `7`.
- [ ] CELL-P05: same-site recursion stores an enclosing activation's capture,
  returns `9`, and retains distinct activations with one release each.
- [ ] CELL-P08: handler-provided closures retain their actual dependencies;
  local use and independent reply escape remain admitted.
- [ ] CELL-P09: independent outward payloads and outer-dependent values crossing
  unrelated inner scopes remain admitted at their permitted recipients.
- [ ] CELL-P10: admitted ordinary immutable cycles remain usable and preserve
  observable sharing without a resource-cycle diagnostic.
- [ ] CELL-P13: a handler writes an A-dependent closure into B but replies with
  an independent function; that reply snapshot escapes and returns `7`.
- [ ] CELL-N02: handles, wrappers and live-reader/evidence closures cannot escape
  their own resource scope, including through imports.
- [ ] CELL-N03: a fixed-type stored closure capturing its own cell rejects.
- [ ] CELL-N04: indirect cycles through younger cells, wrappers and helpers
  reject; a later clearing write does not repair retention.
- [ ] CELL-N05: younger/incomparable retention and unsafe branch alternatives
  reject even without a resource cycle.
- [ ] CELL-N06: later dependent reads and dependent handler replies cannot escape.
- [ ] CELL-N07: outward request payloads preserve hidden capture, evidence and
  indexed metadata dependencies despite an independent eventual body answer.
- [ ] CELL-N12: the builtin read after CELL-P13's handler retains A and rejects
  escape at A's close.
- [ ] Independent reconstruction and charged analysis cover all these cases;
  TASK-0048's adversarial and budget checks confirm the connected boundary.

Each ID includes every CP-0023 variant. Positive observations requiring runtime
remain open until TASK-0047 connects; a source-only pass is partial delivery.

## Verification

Add named cases to `tests/resource_scope_typing.rs`,
`tests/resource_scope_modules.rs` and `tests/resource_scope_core.rs`, plus
analysis and summary unit tests. Run:

```sh
CARGO_BUILD_JOBS=1 cargo test \
    --test resource_scope_typing --test resource_scope_modules \
    --test resource_scope_core
```

For every negative case assert the prescribed phase/reason and causal labels;
pair it with the relevant permitted case. Reconstruct dependency proofs after
transforms and imported-summary substitution. Coordinate runtime observations,
recursive activation counts and cyclic-value tests with TASK-0047. TASK-0048
checks tampering and exact/insufficient/retry budgets across all paths.
Retain frozen inputs, focused results, independent review and retained-commit
verification. TASK-0049 owns the full checkpoint gate.

## Discoveries

None recorded. An analysis that cannot admit a required positive is unfinished
work or a semantic question for CP-0023, not an implicit reduction in scope.

## Deviations

None authorized. Cell scope lifetime and resource-cycle rejection are fixed;
temporary younger retention, new capture annotations and DN-0054 region
mechanisms are excluded.
