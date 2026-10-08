# Provider experiment and adoption plan

> These are bounded experiment steps under
> [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
> Candidate semantics remain informative until accepted through the product
> workflow. This plan records experiment steps and the path to product adoption;
> it does not independently authorize new language semantics.

## Goal and boundary

Extend the existing Ash compiler and runtime to test library-defined SQLite and
scoped arena providers. Compare source descriptions, inferred and explicit
contracts, type checking, Core execution, and native behavior. Develop the
extensions so successful work can become part of Ash and its standard library.

The initial experiment used `.worktree/provider-experiments` on
`codex/provider-experiments`. These are historical source paths; the
[package](README.md#checkout-and-scope) describes reproduction from any checkout
containing the delivery. The
[consolidation record](execution.md#current-consolidation-checkpoint) identifies
the checked source, results and retention status. Retaining a verified bounded
experiment on `main` does not adopt its candidate semantics or architecture.

The user's 2026-10-03 direction prioritizes completed source capabilities over
additional internal test granularity. The immediate integration target is S-01:
an Ash library and client execute a real SQLite session through the public
driver, with checked Core and observed completion. Continue the shared instance
bridge needed for that target; judge each prerequisite by the execution boundary
it removes. Later targets are the remaining SQLite, arena and borrowing cases,
then the authoring blueprint and adoption evidence.

The plan covers the copying SQLite bridge, a fixed-capacity scoped arena, and
their first borrowing comparison. Arena owner transport, foreign callback ABI, concurrency,
native-owner reference counting, tracing, and processes remain outside these slices. A
semantic gap returns to the design documents before implementation continues.

[DN-0037](../DN-0037-ash-authored-foreign-library-interfaces.md) records a separate
program for Ash-authored foreign-library interfaces. These experiments can
supply evidence for that program. Its requirements do not expand this plan's
native-call profile, steps or completion criteria.

## Common support deliveries (2026-10-04)

The common workstream uses `codex/common-resource-support` in
`.worktree/common-resource-support`, starting from unsigned recovery commit
`167bd8c`. That checkpoint is unverified. Each accepted delivery merges with an
unsigned merge commit into `codex/provider-experiments`. This historical
handoff excluded `main`; later experimental retention is recorded separately
in the consolidation record.

1. Restore a coherent tagged owner migration in `types`, `resolved`, `kind`,
   evidence, elaboration and every Core consumer. Check independent owner
   signatures, argument tags, saturation and lexical scope; preserve Type-only
   native ABI mapping and bounded work/disposal. Run the M1 commands below,
   affected deep regressions and architecture checks before review/integration.
2. Connect initializer checking, checked-template specialization, descriptor
   scopes, executable bindings and ownership handoff through the public driver.
   Execute S-01 and observe statement finalization before connection close.
3. Add only arena configuration, acquire, usage and finish through that same
   mechanism. Execute `(64, 4)` usage, repeat/nest scopes, refusal and release.
4. Execute complete rows and control obligations: formal open Delta callback,
   separate same-sigma/same-epsilon different-c witness, resume, structural
   discard, outer cleanup, consumed and retained completion reports. Reject
   malformed source/Core authority and escape. Run integrated `cargo xtask verify`.

Deliveries 1–3 above are integrated. Batch 0 merged at `c38b9d2`, SQLite S-01
at `7c97a45`, and the basic arena lifecycle at `53db4eb`. Independent SQLite
and arena work starts from those original-branch integration commits. Delivery
4 is integrated at `3f9dd75`, with the complete original-branch gate recorded in
[execution](execution.md#current-checkpoint). The separate generic cost delivery
is integrated at `c97e0f3` and verified by receipt 116. The measured common
follow-on consolidates source preparation and capture work while preserving
exact Type/row identities and independent Core checks. Earlier source delivery
`183e9d5` merged at `5991e3d` and passed receipt 186. The subsequent capture and
final-binder delivery `70e97735` merged at `13d2b89` and passed the complete
original-worktree gate in receipt 282; documentation-only merges advance the
original tip to `0d0c2bd`.

The selected delivery tracks completed control-call suffixes, carries
unproved row equations explicitly and borrows immutable replacement Types.
Receipt 284 passes the connected Common normal gate, including independent
Core, public control/row programs, architecture and strict quality checks.
Common commit `1fa1f4f` is integrated by unsigned Original merge `f0a8e59`,
and the complete normal-policy original-worktree gate passes receipt 284.
Dirty-edge, strict-predecessor and global-constructor staging trials increased
measured work and were exactly reversed. At that checkpoint the larger three
SQLite cases still exceeded normal limits; a private fusion study targeted
contextual child expansion. That delivery selected no work or depth limit change.

The follow-on context-extension lookup reuses an exact completed `(parent,
Transition)` witness before the unchanged recurrence walk. It preserves context
identities and adds no carrier. All 60 normal Value tests, 320 public cases,
normal native resume, build, formatting and strict Clippy pass. Four completed
SQLite cost runs show small Source/Core reductions, with all other owner totals
unchanged and the real recurrence-miss tax included. At that checkpoint the
larger three normal refusals remained open. Common commit `478e043` is integrated
through unsigned Original merge `5001156`; the complete Original gate passes. See
[execution](execution.md#value-context-extension-integration-2026-10-07).

The String/TEXT manifest, executable adapter, source library and larger programs
remain preserved SQLite-owned work. The
[SQLite delivery evidence](sqlite-copying-delivery-2026-10-08/README.md) now records
all five packaged programs passing under calibrated public-driver admission,
matched reuse of seventeen original cases, and a fresh supplementary forwarding
regression. Historical default-budget refusals retain their original scope;
calibrated admission does not establish reduced compiler work. At that SQLite
source checkpoint, preserving integration and the final combined gate remained
pending. Consult the consolidation record for later verification and disposition.
Standalone/explicit
budgets, depth and validation remain unchanged; the
[calibrated policy](calibrated-admission-2026-10-08/README.md) records the larger
public-driver phase allowances.

Common owns shared compiler, Core, capture, provider checking and generic runtime
changes after the SQLite handoff. SQLite owns its library, manifest and native
adapter work and supplies executable evidence. Root coordinates serial Cargo
windows, tracking, unsigned commits and real original-branch merges. Independent
reviews and private studies may proceed in parallel without shared-file writes.
An implementation obstacle does not authorize changing the selected semantics.

SQLite-specific work after S-01 includes the remaining copying/API cases.
Arena-specific work after the basic lifecycle includes typed allocation, Layout,
references, containment, borrowing and storage families. Those are excluded from
common support, as are DN-0037 and DN-0038.

## Existing implementation and planned changes

Current [syntax](../../../spec/syntax.md) selects only `cell` or `native_buffer`
in a `resource` expression. Their provider authority is compiler-defined and
sealed. Current capture and completion rules already constrain scoped handles.
The experiment tests how to generalize those boundaries for library-defined
provision and typed arena objects while preserving existing behavior.

Use the current pipeline throughout:

| Existing files | Experimental responsibility |
| --- | --- |
| `src/lexer/`, `src/parser/grammar.rs`, `src/parser/expression.rs`, `src/parser/project.rs`, `src/parser/cst.rs`, `src/surface.rs` | Extend existing parsing and projection for the selected surface additions. |
| `src/module.rs`, `src/resolve.rs`, `src/resolved.rs` | Resolve resource type definitions, associated providers, foreign declarations, fresh binders, imports, and public contracts. |
| `src/types.rs`, `src/kind.rs`, `src/elaborate.rs`, `src/evidence_validation.rs` | Check authority, dependencies, effects, foreign signatures, and module evidence; elaborate the selected contract. |
| `src/core/capture/value.rs`, `src/core/capture/control.rs` | Extend dependency and captured-access analysis where the candidate requires it. |
| `src/core/effect.rs`, `src/core/dialect.rs`, `src/core/validate.rs`, `src/core/transform.rs` | Extend shared typed Core, independent validation, and transforms together. |
| `src/eval/machine.rs`, `src/eval/disposal.rs`, `src/eval/value.rs` | Execute acquisition, contracted calls, arena access, and completion through the existing Effect machine. |
| `src/driver.rs`, `tests/support/mod.rs` | Exercise source cases through the public modular driver and existing integration helpers. |
| Root `Cargo.toml`, `Cargo.lock` | Add only necessary native dependencies and adapter membership. Keep one workspace. |

These are extension points, not a requirement to edit every listed file. Each
slice identifies its actual changes from the selected semantic delta. Reuse
existing effects, handlers, resource completion, and data representations where
their contracts suffice; explain any new primitive or retained Core metadata.

The main crate forbids unsafe Rust. Follow the existing
[native-buffer boundary](../../../native-buffer/README.md) when isolating foreign
calls: private pointers, explicit ABI and layout assumptions, and audited native
operations behind a safe Rust API. Add a small adapter crate to the root
workspace only if needed for that boundary. Its role is foreign calls and native
storage primitives. All Ash parsing, checking, validation, and execution remain
in the existing implementation. Rust borrowing alone does not verify Ash source.

Plan new integration suites under the root `tests/` directory:

| Planned suite | Evidence |
| --- | --- |
| `foreign_provider_syntax.rs` | Resource type definitions, provider associations, instance forms, scopes, imports, and diagnostics. |
| `foreign_provider_typing.rs`, `foreign_provider_core.rs` | Checked foreign contracts, authority, owner relations, Core validation, and transform preservation. |
| `foreign_provider_runtime.rs`, `foreign_provider_modules.rs` | SQLite execution and completion from source, including imported providers and generic helpers. |
| `arena_resource_typing.rs`, `arena_resource_runtime.rs` | Layout, allocation, aliasing, non-escape, nested dependencies, and independent copies. |
| `foreign_memory_interactions.rs`, `provider_control.rs` | Retained access, view invalidation, capture, resume, discard, and combined completion. |

These are planned suite names. Current preparation uses existing suites,
including `resource_provider_syntax`, `resource_provider_resolution`,
`foreign_module_admission` and `provider_sqlite_source`. Their passing
declaration checks do not establish resource-instance execution. Native helper
tests supplement source suites with ABI and storage observations; they cannot
substitute for source-to-Core execution.

## Complete owner row argument follow-on

The [selected complete owner row arguments](semantics.md#selected-complete-owner-row-arguments)
extend DN-0036 experimental P-1 after independent contract and prose approval.
Selection remains informative wherever the experimental implementation is
retained. It does not define current Ash, establish product adoption or supply
a formal proof. The earlier module-publication baseline
was Type-only. Common Batch 0 integrates the complete argument migration, and
Batch 3 moving-source evidence executes the formal open-row callback. The
finite per-request capture witness and required row/control cases pass connected
common verification. The original-branch merge and its fresh final gate are
recorded separately.
[Execution](execution.md#current-consolidation-checkpoint) records the current
consolidation status; earlier receipts retain their named checkpoint scope.
The callback exclusion above means foreign callback ABI; this pressure case executes an ordinary synchronous Ash
function application within a provider clause.

Follow-on evidence must cover the complete tagged syntax and saturated
resource/effect/interface applications, declaration-independent owner signatures,
inherited owner binder roles, exact row-bearing identity and simultaneous
substitution. Check preceding-scope actuals before fresh position-zero identity,
nested row dependencies, occurs/lacks rules and identity escape. Preserve
row-free initializer inference and the native state/ABI vector.

The positive fixture must execute the clause callback, then resume pure
MissingRow. Its client performs H and forwards the callback through the sealed
method: actual body row is closed {E,H}, epsilon={H}, D={|Delta}, with existing
Delta lacks H. Derive Omega={H|Delta}, K empty and rho=Omega without adding
Delta lacks E<C,{|Delta}>. The derivation supplies the comparison contract;
the later public callback receipt is executed evidence for that topology.
Exercise generic open and closed specializations, eligible local generalization,
actual captures, surviving interpreters and linked execution.

Run the amendment's negative cases at parsing, resolution, static checking,
summary authentication, specialization and independent ordinary Core validation.
Include wrong tags/arity, unsaturated mixed owners, invalid binder roles,
nested occurs cycles, incompatible lacks, fresh-identity escape, erased callback
or native demand, forged origins and conflicting association records. Verify
public dependency closure, targeted aliases/reexports and diamond imports with
body-free client checking and separately authenticated executable template
linkage. Specialization must derive real epsilon and c, solve every affected
handler/resume/descendant, and retain no unresolved recipe in ordinary Core.
No new runtime reduction rule follows from type metadata or ordinary application.

The same-sigma/same-epsilon different-c source witness is a separate mandatory
obligation. The finite public witness has passing moving-source evidence; it is
not a general mathematical proof. The open-D callback case does not replace it.
Do not weaken capture,
discard, completion or principal-row rules to admit either case. A separate
native-request clause variant must preserve its known direct native demand
until exact admitted interpretation discharges it.

Independent reviews approve bounded selection and the required common checks
pass. The original-branch merge and verification evidence are recorded separately. Later adoption follows
[Step 7](#step-7-bring-successful-work-into-ash-and-its-standard-library): an
accepted semantic proposal, any justified architectural decision and authorized
tasks precede product implementation, tests and specification changes. Allocate
those artifacts only at that later stage. Candidate representation choices and
parser diagnostics remain implementation preparation, not adopted architecture.

### Execution checkpoints for the common instance bridge

These implementation checkpoints refine Step 2; they do not replace Steps 3
through 7. M1 belongs to common Batch 0. M2 through M4 and the S-01 part of M5
form the connected source-to-runtime delivery in common Batch 1. The complete
row and control cases in M5 belong to common Batch 3. The labels below are not delivery batch
numbers. The [consolidation checkpoint](execution.md#current-consolidation-checkpoint)
records current status and evidence. Each row depends on acceptance of its predecessor.

| Checkpoint | Boundary removed | Required exit evidence |
| --- | --- | --- |
| M1: structural migration | Type-only assumptions in complete owner arguments and their consumers. | Charged, fallible traversal and reconstruction; canonical signatures, kind and scope checks; unchanged deep-disposal regression; frozen contract then quality review. |
| M2: source preparation | Resource instances cannot yet check their preceding-scope actuals and initializer. | Typed initializer checked once, Statement connection inference, body-only fresh identity, complete mixed actuals and attributable refusals. |
| M3: publication and specialization | Complete parent arguments and inherited roles cannot yet cross body-free contracts and executable templates. | One simultaneous substitution, original defining authority, distinct copied occurrence identities, complete catalog relocation and independent linkage refusal. |
| M4: ordinary Core | Instance topology and request-specific continuation demand are not yet reconstructed. | Real body epsilon and per-request c; every handler/resume/descendant solved; independent final Core validation and transforms with no unresolved recipe. |
| M5: runtime | Authenticated declarations have no executable provider dispatch. | Reviewed binding and ownership handoff, public-driver S-01, native release observations, generic callback execution and the separate same-sigma/same-epsilon different-c witness. |

The current M1 gate uses existing targets, after the connected migration is
complete. A development-only compiler check may diagnose the incomplete batch;
it does not close this gate.

```bash
cargo check -p ash --all-targets
cargo test -p ash --lib --test effect_rows --test kinds --test kind_resources
cargo test -p ash --lib eval::machine::tests::owned_deep_drain_success_and_partial_failure_use_the_predecessor_stack_bound -- --exact --nocapture
cargo test -p ash --test provider_sqlite_source --test resource_provider_syntax --test resource_provider_resolution --test foreign_module_admission
```

Retain exact, one-short, cumulative refusal and partial-cleanup evidence. Do not
increase the stack, reduce fixture depth or relax work ceilings. Compilation and
these structural checks do not establish mixed source admission or runtime
behavior. Later checkpoints retain their affected integration checks,
independent reviews and the full verification gates below.

## Step 1: fix the first contract and native inputs

1. Check the worktree revision and carried design inputs against
   [environment.json](environment.json). Record changes before using them.
2. Review [contracts](contracts.md), [cases](cases.md), and
   [semantics](semantics.md) together. Map each admitted case to source scope,
   checking obligations, Core transitions, and native observations.
3. Classify each fact as a foreign assumption, provider obligation, client
   obligation, inferred relationship, runtime check, or open design question.
   Follow the types from a resource type definition to its provider, effect
   interface, checked handlers, and instance. Instantiate the input, state,
   bound resource type, result family, exact operation types, and outward rows
   for the first case using the schema in `semantics.md`. No surface form is an
   implementation target before this mapping is specified.
4. Settle acquisition refusal, publication failure, consumed versus retained
   owners on completion, and body-versus-completion failure order for the first
   slice. Define its rules before implementing those transitions.
5. Specify explicit interpretation of foreign-call effects in the existing
   Effect execution path. Preserve the current empty entry-row contract unless
   the candidate deliberately proposes and tests a change to it.
6. Select the first resource definition, provider assembly, instance form, and
   checked foreign declaration after comparing their typing. Reuse current
   effect and handler conventions. Name every unsupported authoring feature.
7. Resolve missing SQLite headers and link metadata. Use a matching development
   package or an explicitly pinned upstream build with its checksum and config.
   Record ABI widths, headers, linked library, runtime version, and compile
   options. Verify a native smoke call before interpreting database failures.

Discovery commands, from the experiment worktree:

```bash
git rev-parse HEAD
rustc --version
cc --version
pkg-config --modversion sqlite3
pkg-config --cflags --libs sqlite3
```

The last two currently fail. That setup gap is separate from Ash typing and
native allocation failure. Exit evidence is a specified first contract, its
pipeline change map, and a reproducible version-matched native smoke build.

## Step 2: connect one SQLite provider through Ash

1. Add an Ash-source integration case for S-01: acquire an in-memory connection,
   prepare `SELECT ?1`, bind integer `42`, observe a row and completion, and
   return independent `42`. Its expected initial failure must identify missing
   experimental support after native setup has passed.
2. Extend the existing parser and resolver for the selected resource type
   definition, provider association, instance form, and foreign descriptions.
   Config evaluates in the preceding scope; the fresh identity and access value
   bind only in the acquired body. Infer the statement's connection parameter
   from the checked initializer, keeping it distinct from the fresh identity.
3. Extend existing checking and elaboration to retain the provider contract,
   exact operation instance, owner dependencies, and acquisition/completion
   effects. Reject fabricated authority, wrong instances, and escaping handles
   before native access.
4. Extend existing typed Core, its validator, and transforms for the selected
   representation. Use the test pattern in `tests/native_buffer_core.rs` to
   validate linked modules and transformed Core. Mutate an owner, operation
   instance, primitive signature, result relation, and origin separately.
5. Implement the thin foreign boundary for the required initialize/open,
   prepare, integer bind, step, column access, finalize, and close operations.
   Specify and review the executable registration and dispatch interface that
   connects authenticated foreign operation identities to the safe adapter.
   Existing foreign manifests authenticate passive declarations; they contain
   no executable binding. Include missing or mismatched binding refusals and
   the handoff of native state ownership before admitting runtime execution.
   Wire them into the existing Effect machine with guarded publication and
   statement-before-connection completion.
6. Express the provider API and SQLite protocol in Ash library modules as far
   as the checked mechanism permits. Record each remaining compiler privilege
   and its safety reason. A new hardcoded SQLite resource kind is insufficient
   evidence for library-defined provision.
7. Run the source case through `driver::run_path`; compare validated Core traces,
   returned data, and native release observations. Distinguish two independent
   connections and repeated activations.

Exit evidence is the first complete source-to-native path in the existing Ash
implementation, with paired rejection cases and a named trusted foreign
contract. Hand-built Core and Rust-only wrappers cannot close this step.

## Step 3: complete the copying bridge and public contracts

1. Add S-02 through S-05 using the same pipeline: setup failure, malformed and
   empty SQL, copied bytes, protocol/error behavior, persistence, and imports.
2. Use `SQLITE_TRANSIENT` for copied inputs and independent returned bytes.
   Specify the Ash byte representation using or extending existing data and
   heap support. Keep empty BLOB, SQL null, and conversion failure distinct.
3. Preserve whether finalize consumes a statement and whether refused close
   retains a connection. Label deterministic fault injection separately from
   actual native failures.
4. Add a temporary-file persistence test owning its temporary directory and
   cleanup. Add imported provider APIs, facades, and generic helpers. Check
   clients against exported contracts without inspecting provider bodies.
5. Record which properties inference recovers and which require declarations.
   Pair useful source examples with escaping state, hidden capture, wrong-owner,
   and invalid protocol cases. Keep diagnostic causes tied to acquisition and
   the offending operation.

Exit evidence is a useful copying SQLite library with reviewed contracts and
module-boundary checking. Observations distinguish adapter calls from actual
native allocation events; unmeasured costs remain labeled.

## Step 4: implement the scoped arena through the same mechanism

1. Specify capacity units, alignment, arithmetic overflow, zero-sized values,
   initialization failure, cursor rollback, and release obligations before
   adding allocation tests for M-01.
   Specify allocation operand/result types and handler coverage for every
   admitted payload type before heterogeneous cases. Current effect operations
   have no operation-local type binders; a generic allocation method alone
   cannot establish a handler for all its exact instances.
2. Implement stable backing storage and typed allocation through the provider
   mechanism from the SQLite slice. Extend existing value/heap representation
   only where required; keep native addresses private.
3. Publish typed access only after complete initialization. Failed allocation
   preserves earlier objects and the specified cursor state. Object bindings
   and aliases do not own separate storage release.
4. Extend Ash checking and capture analysis for M-02 through M-05: immutable
   aliases, closures, nested owner dependencies, safe outer projections,
   independent copies, scratch scopes, and rejected owner transport.
5. Exercise M-06 through the existing continuation and disposal machinery.
   Preserve owner and access obligations across capture and resume; complete
   them in the specified order on normal return and admitted owned discard.
6. Compare explicit allocation with construction directed to a scoped provider.
   Measure friction, annotations, copying, and retained storage without assuming
   nearest-region construction is the accepted rule.

Exit evidence connects Ash type checking to native storage lifetime for the
admitted objects and control paths. A Rust lifetime or merely enclosing lexical
block cannot substitute for Ash dependency checks. Do not execute stale native
pointers as rejection tests.

## Step 5: compare retained storage and temporary views

1. Define access validity, conflicting operations, branch joins, and captured
   obligations for X-01 through X-04 before extending the implementation.
2. Compare copied input with arena-backed retained input. Relinquish retention
   through rebind, clearing bindings, or finalization according to the contract.
   Show that reset alone does not discharge it.
3. Reject arena completion and incompatible mutation while retention remains.
   Obtain a row view and reject step, reset, conversion, or finalization that
   would invalidate active access. Accept an independent copy followed by those
   operations. Owner lifetime alone does not authorize the view.
4. Exercise handlers with reachable aliases while a conflicting borrow is
   captured. Capture/resume must preserve the obligation; temporary inactivity
   must not grant conflicting access.
5. Compare derived Core transitions, runtime state, native behavior, and
   combined discard order. State which access facts erase after checking and
   which remain for execution or validation.

If the candidate rejects a required useful case, preserve that finding and
compare alternatives. Do not silently copy in the borrowing variant.

## Step 6: evaluate results, blueprint, and developer tools

Create `results.md`, `blueprint.md`, and `tooling.md` here after observations
exist. For each case record admission, inferred and explicit information,
Core/native agreement, diagnostics, completion, assumptions, and measured costs.

Compare provider assembly styles against the same cases. Extract the library
author's actual workflow: ABI and symbol inputs, foreign contracts, provider
definitions, checked handlers and operations, initialization, linking, errors,
tests, and packaging. Repeat the blueprint with the arena to distinguish general
requirements from SQLite-specific policy. Follow DN-0036's transfer requirement
with a walkthrough of one contrasting foreign API. Record which steps transfer
and which contracts need author judgment; a second complete binding is not
required.

Try a small tool for an observed difficulty, such as a binding contract check,
build-input report, or owner/access diagnostic. Compare its output with the
manual workflow. Separate syntax, checking, runtime, and authoring-tool gaps.

The result assessment uses DN-0036's success criteria:

| Result | Branch outcome |
| --- | --- |
| Successful supported design | Retain useful implementation and proceed to product adoption below. |
| Failed design | Do not merge the experiment branch. Record counterexamples and reasons; disposal is optional. |
| Inconclusive or partial result | State the supported fragment and remaining questions. Do not merge unresolved behavior; refine or plan the next bounded comparison. |

Experiment completion means its questions have answers. Retention of a verified
bounded experimental fragment requires attributable evidence and explicit
limitations. Product adoption additionally requires a successful design and the
adoption work below. Retention alone does not complete this broader plan.

## Step 7: bring successful work into Ash and its standard library

1. Produce the adoption report required by DN-0036. Map each proposed general
   mechanism to evidence from both experiments or state its tested scope.
   Identify current behavior, semantic delta, trust assumptions, compatibility,
   supported targets, and remaining limits.
2. Prepare the change proposal for language semantics and architectural
   decisions for converged non-language choices. Retain successful code on this
   branch or another explicitly experimental retained checkpoint while those
   contracts are reviewed; rewriting it from scratch is not a prerequisite for
   adoption.
3. Following acceptance, create product tasks and detailed execution plans for
   coherent checkpoints. Map existing experimental code to each checkpoint's
   requirements: retain conforming parts, revise gaps, and remove failed
   candidate machinery from the proposed product tree.
4. Specify surface grammar, binding and import rules, static checking,
   elaboration, and Core operational transitions with the retained
   implementation and tests. Update the affected `spec/` files in the same
   product checkpoint. Include failure, capture, resume, discard, and completion
   derivations rather than only the successful native call.
5. Place reusable provider, arena, view, conversion, and completion APIs in Ash
   library modules. Decide standard-library organization through the adoption
   review. Keep SQLite policy in its library, with a decision on optional
   standard-library inclusion or separate distribution. Keep both examples
   testing the public mechanism after adoption.
6. Compare with existing cell/native-buffer mechanisms and simplify only where
   evidence supports it. Preserve existing Pure and Effect behavior and add
   compatibility checks. Document supported native builds, authoring workflow,
   developer tools, costs, errors, and explicit foreign assumptions.
7. Run the full product verification and required review. Adopt the successful
   implementation as product behavior only when the accepted contract,
   implementation, specification, library documentation and evidence agree.
   Current language semantics derive from `spec/`; experimental retention on
   `main` does not substitute for this adoption workflow.

An unsuccessful experiment remains unmerged. Useful code need not be discarded;
retention does not waive the successful-design and product-verification gates.

## Verification and pause conditions

Prefer end-to-end and integration tests through the public source pipeline.
Every new test should cover a required experimental observation, a concrete
integration behavior or an observed defect that existing coverage does not
catch. Add a focused internal regression when needed to reproduce or isolate a
bug, or to verify a required boundary that integration cannot observe. Do not
add tests merely for each helper, field or implementation branch. Combine
related scenarios when their observations remain attributable.

Batch connected implementation changes and run the affected integration and
regression suites at useful checkpoints. Broaden verification for a completed
capability, a shared change with unresolved regression risk, or an observed
failure that warrants it. Avoid repeating broad gates after small edits when
affected checks suffice. Required contract evidence, independent validation,
review and final verification still apply. Report completed behavior and the
next blocking boundary first; test counts are supporting evidence.

Run these suites from the root workspace. The following test targets are
planned, not checks already run:

```bash
cargo test --locked --test foreign_provider_syntax --test foreign_provider_typing --test foreign_provider_core
cargo test --locked --test foreign_provider_runtime --test foreign_provider_modules
cargo test --locked --test arena_resource_typing --test arena_resource_runtime
cargo test --locked --test foreign_memory_interactions --test provider_control
```

Use native helper tests for the unsafe boundary and actual ABI behavior. Reuse
the current resource, native-buffer, module, evidence, and Core tests for
affected invariants. At coherent compiler/runtime checkpoints, run the existing
workspace verification:

```bash
cargo xtask verify
```

For applicable proof changes, follow the adopted
[proof-tooling workflow](https://github.com/dikini/ash-lang/blob/a2ced870f491457a60e3131ac613f295ea77e441/docs/project/proof-tooling.md) and
[proof-navigation guide](https://github.com/dikini/ash-lang/blob/a2ced870f491457a60e3131ac613f295ea77e441/docs/project/proof-lsp.md). Use validated module
receipts with their compiler, source, import, option and report pins. Batch
related changes, keep compiler jobs serial by default, and coordinate builds
and language-server use with other tasks within the host's RAM and CPU limits.
Use one Rust workspace and one open Lean file at a time; stop language servers
before heavy builds. Record the tools actually exposed in the task. LSP feedback
and cache receipts alone do not establish proof acceptance. Retain the reviewed
frozen integration gate, including source, compiler, dependency, warning,
report and axiom checks, alongside the Rust verification above.

Documentation checks cover authority labels, case links, Markdown, and formal
notation. Current baseline observations are in the package README. No
experimental test pass is claimed by this plan.

Pause a slice to revise its contracts when execution disagrees with a required
case, checking needs an unstated assumption, or native behavior contradicts the
model. Report setup failure separately. Preserve the copying baseline when a
borrowing candidate fails. Passing checks alone cannot make a failed design
eligible for merge.


## Calibrated public-driver admission, 2026-10-08

The user accepted the completed practical costs and selected finite phase
allowances with explicitly reported deficits up to 10%. This supersedes the
earlier no-limit-change follow-on checkpoints above. Only the public modular
pipeline selects the calibrated source, final-elaborator and independent-Core
budgets; standalone and explicit caller budgets and all depth limits retain
their existing behavior. The four original realistic SQLite cases now pass
with their complete native assertions. See the
[policy and evidence](calibrated-admission-2026-10-08/README.md).

The separate offline assessment is committed on `codex/resource-calibration`
at `ed3764a`; it retains all prior measurements and reports accepted physical
cost deficits as optimization targets. Its library-input snapshot is not
implicitly merged into Common. Common owns the shared driver/Core policy;
SQLite owns the preserved library/native delivery and example-host visibility.
Root retains the serial compiler/integration window until the verified shared
delivery is merged and checked in the original worktree.
