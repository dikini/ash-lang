# TASK-0038: Ash native-buffer library

- ID: `TASK-0038`
- Status: active
- Related: [CP-0022](../proposals/CP-0022-ash-authored-foreign-interfaces.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md),
  [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [GitHub issue #4](https://github.com/dikini/ash-lang/issues/4)

> This task organizes authorized work. It does not define Ash semantics.

## Dependencies

Verified TASK-0036/TASK-0037 generic source contracts, memory operations, guards,
report codecs and executable build. Cell behavior is outside this migration.

## Work

1. Author a passive Ash library declaring calloc/free, initialization, bounds and
   byte conversion policy, acquisition/completion and associated handlers.
2. Use the checked acquired_only codec to preserve Success/Failure and nested body
   results, positive-length refusal, accounting and pre-mutation checks.
3. Migrate callers explicitly to source imports/resource spellings. Remove builtin
   native-buffer authority and special compiler/evaluator dispatch after parity.
4. Update specification and publish mechanical migration/build/run instructions.

## Progress

Assignment, blockers, live progress and PR status belong to the linked GitHub
issue. This task retains scope, ordered work and durable implementation findings.

## Verification

Reuse native-buffer integration/deep-input cases through the generated executable:
positive and refused lengths, zeroed contents, bounds/byte refusal, pre-mutation
failure, nested/repeated scopes and normal/discard exactly-once release. Verify
unchanged cell behavior and required explicit source migration. Actual native
calls and connected regression evidence precede the retaining-branch merge.

## Discoveries

The ordinary `libraries/native_buffer.ash` module now declares `calloc`/`free`,
positive-length policy, initialized writable bytes, bounds/byte conversion and
associated source handlers. Its `acquired_only` codec preserves nested results.
Public callers use explicit imports and `Buffer.Buffer<R>`; the old builtin
module/designator, special compiler/evaluator dispatch and adapter crate are
removed. Common byte operations and runtime guards remain generic, and cell
semantics are unchanged.

Initialized-byte readiness admits proportional `length + 2` work plus complete
report/guard publication before native entry. Injected exact, one-short,
prefixed and fresh-retry checks establish that accounting boundary; real C
fixtures separately observe allocation, zeroing, refused writes and releases.
No normal-runtime size cap or work/depth/stack increase is introduced.

Source acquired-only restoration needs distinct acquisition, raw body, cleanup,
handler and finish value positions. Mapping every administrative node to the
outer report either rejects a legal restored cut or loses captured cell
lineage. The exact checked graph supplies each position; completed acquisition
freezes once, the raw body stays live through cleanup, and the report wraps it
once. Held-cell capture remains rejected. Independent control discovery also
collects passive cleanup-row records, avoiding a duplicate inference solver;
row authentication, strict payload/focused safety and fresh final Core checks
remain intact. Nonempty-row correspondence and exact refusal/retry tests cover
this sharing without weakening authority.

The matching private image now carries canonical cell origins, cell acquisition,
cleanup and hook/registration contracts used by buffer interactions. Corrupted
original identities, binder/edge metadata and source roles remain refused after
reconstruction. Source access-family kinds come from the original checked
resource headers in exported summaries. Local dictionary duplicate-header
checks reconstruct a source resource's original application instead of asking
it for an experimental forwarding plan.

The inherited local-newtype/ordinary `Read<Token>` witness retains its exact
source/Core identity-free positive and captured-owner refusal. Its existing
`Unsupported(RegistryMetadata)` native-build exclusion remains explicit; general
newtype/non-resource lexical-dictionary image support is not part of this port.
This limit is not reported as passing native parity or complete common support.
See [library migration/build instructions](../../libraries/README.md#native-buffer-migration)
and the current issue/PR receipts for scoped native and injected observations.

Preserving result shape requires the accepted acquired_only codec; wrapping
builtin behavior in Scope would be an unintended semantic change.

## Deviations

None authorized. Return concrete semantic gaps to CP-0022 instead of resolving
them locally. Keep excluded features outside this task.
