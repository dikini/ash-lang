# TASK-0047: Generic Cell Execution and Completion

- ID: `TASK-0047`
- Status: active
- Related: [CP-0023](../proposals/CP-0023-scoped-generic-cells.md),
  [TASK-0045](TASK-0045-generic-cell-api-and-acquisition.md),
  [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md),
  [TASK-0048](TASK-0048-generic-cell-integrated-verification.md),
  [TASK-0049](TASK-0049-close-generic-cell-checkpoint.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

Use TASK-0045's reviewed authenticated carrier foundation and CP-0023's
execution contract on the ash-ffi base named in TASK-0049. Runtime work may
proceed alongside TASK-0046, with shared-file coordination. Public execution
requires TASK-0046's completed source/Core dependency admission; runtime keys
cannot replace that proof. No task's positive acceptance is complete until the
connected public path supplies its required observations.

## Work

1. Generalize the owned runtime payload root to an ordinary checked value while
   keeping the new and legacy APIs distinct. Preserve fresh activation keys,
   lexical type/row instantiation, non-owning handles and exact operation/type
   authentication. Reads share values; they do not deep-copy or freeze cells
   reachable through a snapshot.
2. Evaluate initialization once and operands in source order. Admit work,
   storage and capacity before publication or replacement; a refusal cannot
   publish a partial cell or partially mutate its root. Existing operand effects
   remain performed. Charge every new proportional path in its owning ledger.
3. Preserve source handler precedence, clauses bypassing their selected handler,
   restored handlers at resume, direct and indirect mutation, and the actual
   handler reply. Implement the stateful scenarios without a special pure-
   override assumption. Primitive slot transitions invoke no user callback.
4. Capture/resume must move the same owner and latest payload without reacquiring
   or copying ownership. Normal return and checked discard remove the root
   once after required inner completion. Cleanup can use still-live enclosing
   cells; outside or running completion cannot be skipped.
5. Count captured scopes toward live capacity, preserve fresh keys on reuse and
   dispose deep roots/control iteratively. Keep internal failure distinct from
   source cleanup or recoverable allocation. Do not consume referenced native
   owners or restore access revoked by quarantine.
6. Supply runtime evidence for every positive case owned by TASK-0045/0046,
   especially helper/facade aliasing, recursive activations, immutable cycles
   and the stateful snapshot pair. Update dynamic semantics and affected
   execution documentation with the implementation.

Start from baseline `src/eval/machine.rs`, `src/eval/value.rs`,
`src/eval/instantiation.rs`, `src/eval/disposal.rs` and `src/eval/failure.rs`.
Keep the explicit evaluator-machine and typed Core boundaries; shared legacy
implementation is optional and must preserve its behavior.

## Progress

Implementation has not started. All acceptance remains pending.

- [ ] CELL-P07: exact read override, no-other-mutation intercepted write,
  forwarded write and dropped self-capturing replacement have their specified
  results; the discarded replacement creates no retained slot edge.
- [ ] CELL-P12: the unforwarded original write plus the Tick handler's separate
  mutation leaves `99`, not `41` or the original replacement `42`.
- [ ] CELL-C01: capture/resume observes the latest payload without reacquisition;
  nested/same-site activations stay distinct; donor/stale keys fail before access.
- [ ] CELL-C02: owned discard closes once after dependent cleanup; unsafe outside
  or running abandonment rejects; initializer capture creates no premature owner.
- [ ] Runtime observations for all TASK-0045/0046 positive cases are delivered
  to their primary owners, including P05 release counts and P13's result.
- [ ] Runtime charging, preparation, iterative disposal and failure probes are
  connected for TASK-0048's C04/C05/C06 checks.

The primary cases include all CP-0023 variants, not only the summary above.

## Verification

Extend `tests/resource_scope_runtime.rs`, `tests/resource_scope_core.rs` and
the relevant cleanup suites; add owning machine tests for malformed keys,
publication/mutation preflight, shared payloads and iterative disposal. Run:

```sh
CARGO_BUILD_JOBS=1 cargo test \
    --test resource_scope_runtime --test resource_scope_core \
    --test cleanup_abandonment --test cleanup_interactions \
    --test cleanup_partial_acquisition
```

Use the public source pipeline for admitted observations and explicit malformed
Core/machine probes only for internal-failure boundaries. Record exact values,
activation/release counts, source failures and internal failures separately.
Run connected positives through copied/transformed Core with TASK-0048.
Retain inputs, focused results, independent review and retained-commit equality.
TASK-0049 owns the full checkpoint gate.

## Discoveries

None recorded. Interception suppresses only the original builtin replacement;
its surrounding computation can still change both values and dependencies.

## Deviations

None authorized. No native owner is acquired for a generic cell. Region-backed
storage, owner transport, manual release, atomic updates and DN-0054 allocation
work are excluded.
