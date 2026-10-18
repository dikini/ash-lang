# TASK-0045: Generic Cell API and Acquisition

- ID: `TASK-0045`
- Status: active
- Related: [CP-0023](../proposals/CP-0023-scoped-generic-cells.md),
  [TASK-0046](TASK-0046-generic-cell-contents-and-dependencies.md),
  [TASK-0047](TASK-0047-generic-cell-execution-and-completion.md),
  [TASK-0049](TASK-0049-close-generic-cell-checkpoint.md)

> This task organizes work. It does not define Ash semantics.

## Dependencies

Use the accepted CP-0023 contract and the ash-ffi baseline `ffi-base`, peeled
commit `354c76b391fe4af665cf6a03479a9874a57cb3e3`. The planning checkout's older
implementation is not the product base. At launch, record the actual descendant
commit, retaining branch, assigned developer and independent reviewer under
TASK-0049. Preserve existing ash-ffi work and legacy integer-cell behavior.

The reviewed foundation from this task enables TASK-0046 and TASK-0047. It is
not final acceptance: positive execution observations await their connected
checking and runtime. Follow TASK-0049's publication boundary throughout.

## Work

1. Add canonical compiler-owned `@builtin.generic_cell` with the five exact
   exports, kinds, sealed relation, method schemes and owned argument position
   specified by CP-0023. Preserve legacy `@builtin.cell` independently.
2. Resolve named-family acquisition, full `R,T` arguments, initializer-before-
   binder scope, fresh identity, monomorphic payload, exact evidence and row
   discharge. Preserve import, renaming and facade provenance; the new named
   family has no legacy lowercase direct-import gate.
3. Retain authenticated family, argument, initializer, body, binder, origin and
   row facts in Effect Core and module preparation. Add independent ordinary
   type/kind/provenance validation alongside construction, including copied and
   transformed carriers. Preserve the canonical builtin module role and complete
   carrier through private program-image capture and restoration, followed by
   the same admission checks. Keep native source-resource declarations bounded.
   TASK-0046 supplies independent contents/dependency validation; neither this
   foundation, a restored image nor a summary may publish unchecked authority
   before that exists.
4. Enforce fixed monotypes, ordinary local generalization, restricted-payload
   prohibitions and diagnostic precedence. Add public source tests for this
   task's cases, including the permitted shadowing companion to CELL-N08.
5. Charge new syntax/module/type/Core work and retained metadata before work or
   publication. Preserve finite limits and iterative failure disposal. Implement
   these obligations here; TASK-0048 verifies the connected budget behavior.
6. Update the affected syntax, name-resolution, acquisition-typing and Core
   specification passages with the implementation on the product branch. Pass
   the exact authenticated carrier and summary boundaries to TASK-0046/0047.

Start from baseline `src/module.rs`, `src/resolve.rs`, `src/resolved.rs`,
`src/elaborate.rs`, `src/core/effect.rs`, `src/core/validate.rs`,
`src/core/transform.rs` and `src/build/image.rs`. Reuse the existing named-resource
grammar and operation family seams; internal file placement is not a semantic
commitment.

## Progress

Implementation is in progress on `codex/generic-cells` from bootstrap
`e605a9453fa1106da3f28a036a50a8909a519929` and product base
`67ba281d4e93dbfad65e5fd1e6a34c3dfb132686`. The task-owned
[execution plan](task-0045-execution-plan.md) records the bounded sequence.
All acceptance remains pending until its complete original observations exist.

The candidate adds canonical metadata, named acquisition and ordinary checking
on the existing Effect Resource carrier. Its handle type and generated evidence
retain complete arguments. Generic acquisitions, operations, method bodies and
computational signatures that retain generic access or indexed operations fail
closed before source helper-summary publication and after independent ordinary
Core validation in both dialects. Import-only metadata and facades can publish.
Copies, transforms and restored images must pass the same gate. This restriction
is the TASK-0049 staging boundary, not a substitute for the required positive
cases.

CELL-P01/P06/P11 source-shape tests expect pending dependency rejection. Their
replacement, sharing, initializer-count, imported-helper and repeated runtime
observations remain assigned to TASK-0046/0047. CELL-N01/N08/N09/N10 tests cover
ordinary diagnostic precedence, fresh scope, valid preceding shadowing, sealing,
exact evidence and monomorphic reads. Restricted-value and native compatibility
acceptance remains open for connected evidence.

- [x] Reviewed foundation receipt names the retained commit, ordinary
  authentication checks, publication restrictions and remaining dependencies.
- [ ] CELL-P01: Int/Bool/tuple/nominal payloads share one slot through aliases;
  replacement is observed and the initializer executes once.
- [ ] CELL-P06: local/imported helpers, facades and alias branches preserve
  behavior and dependency relationships; distinct owner types stay distinct.
- [ ] CELL-P11: fixed function payloads and mixed legacy/generic cells preserve
  repeated calls, exact evidence and exact effect discharge.
- [ ] CELL-N01: wrong payload type, initializer type, kind and arity reject at
  the existing ordinary phase before dependency checking.
- [ ] CELL-N08: fresh binders are unavailable to the initializer and payload
  type; valid preceding same-spelled bindings still resolve correctly.
- [ ] CELL-N09: counterfeit families/providers and missing exact evidence reject.
- [ ] CELL-N10: a read does not generalize its result; schemes and higher-rank
  payloads retain existing rejection.
- [ ] CELL-N11: restricted State, views and continuation capabilities cannot
  enter the payload directly or through wrappers.

The case IDs refer to all variants in CP-0023, not only the descriptions above.
Keep a case unchecked until source, relevant Core and required runtime
observations are retained. Record partial delivery and the next owner here.

## Verification

Extend the existing `tests/resource_scope_syntax.rs`,
`tests/resource_scope_modules.rs`, `tests/resource_scope_typing.rs` and
`tests/resource_scope_core.rs` suites with identifiable CP-0023 cases. Run:

```sh
CARGO_BUILD_JOBS=1 cargo test \
    --test resource_scope_syntax --test resource_scope_modules \
    --test resource_scope_typing --test resource_scope_core
```

### Foundation verification record

The reviewed production implementation is
`21421b373207ca165dac030266c5174ac401b1ac`.
The frozen verification candidate is
`752b69cdb909c66f6810cec4709aa06fde44b2e8`. Its later changes only calibrate one
existing exact-work test and repair the nested-row source fixture. All eight
case criteria above remain open. Independent code and evidence review by
`/root/task0045_reviewer` are clear at the frozen candidate, with no unresolved
findings. The coordinator accepted foundation readiness only; no downstream
dispatch or complete case acceptance follows from this receipt.

The full library receipt was obtained at
`a3562b8f1b6f589388f55274ff76756099c665be` and transfers to the candidate
by exact `src/`, Cargo manifest/lock, toolchain and Cargo configuration equality.
The only intervening change is the integration fixture in
`tests/resource_scope_typing.rs`.
Frozen Git tree identities are:

- `src/`: `602dd80038d490687220e893420f49020319e914`
- `tests/`: `665340514768d029e1865dcdfdf3f9c8c0568457`
- `Cargo.toml`: `28c3994bdc0f60423bb884abb22e60d07bce7f96`
- `Cargo.lock`: `e12d96b05d2bf0e37d5da153ba2672128c60ea3b`
- `rust-toolchain.toml`: `b4d5fb623671bfddb58e622e6a603b1b6b0c9d3e`
- `.cargo/config.toml`: `e8799810d2eafed1a7d59c5eb32874078e0b1b36`

Commands use `CARGO_BUILD_JOBS=1 RUSTC_WRAPPER=`, the product checkout's own
`target` cache, and Rust 1.97.1
(`8bab26f4f68e0e26f0bb7960be334d5b520ea452`, `x86_64-unknown-linux-gnu`,
LLVM 22.1.6). The configured sccache wrapper could not start in the sandbox;
that wrapper refusal is not a product baseline failure. No limits or stack
sizes were raised. Commands below have exit status zero unless marked pending.

```sh
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test --lib -- --test-threads=1
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test \
    --test resource_scope_syntax --test resource_scope_modules \
    --test resource_scope_typing --test resource_scope_core \
    -- --test-threads=1
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test \
    --test source_resource_execution --test source_resource_acquired_only \
    --test native_buffer_typing --test native_buffer_core \
    --test native_buffer_modules --test native_buffer_runtime \
    -- --test-threads=1
```

| Target | Passed | Test time |
| --- | ---: | ---: |
| Library | 1,898 | 178.99 s |
| Resource Core / modules / syntax / typing | 2 / 14 / 5 / 73 | 0.07 / 0.79 / 0.01 / 4.48 s |
| Native buffer Core / modules / runtime / typing | 3 / 6 / 9 / 12 | 0.41 / 215.02 / 27.91 / 1.34 s |
| Source resource acquired-only / execution | 5 / 78 | 5.39 / 153.16 s |

The resource typing suite also passed its one-test child process. Compilation
for the library, resource and affected-caller commands took 45.51 s, 9.47 s and
15.36 s respectively. Exact model runtime is unavailable; these tool timings
do not measure model runtime. The library run covers every Core validation test,
module/publication exact-budget probe and the new deep-copy, Pure admission and
nested-instance scanner regressions. Native caller results are regression
evidence; they do not close the connected generic/native cases in TASK-0048.

Working logs are `/tmp/task0045-lib-a3562b8.log`,
`/tmp/task0045-resource-752b69c.log` and
`/tmp/task0045-affected-752b69c.log`. The earlier `21421b3` library run passed
1,897 tests and failed the old deep-constructor work expectation: the paid
computational scan adds exactly two fixed cells for its single Unit result
(node visit and structural root). The corrected probe preserves depth 16,384,
the production limit, its 256 KiB stack and exact/one-short link assertions.
The initial focused run remains an observation rather than an immutable
baseline receipt because editing began while compilation was running.

Focused all-features Clippy passed in 49.24 s with warnings denied. Formatting
and `git diff --check` passed without source changes. Their exact commands are:

```sh
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo clippy --lib \
    --test resource_scope_syntax --test resource_scope_modules \
    --test resource_scope_typing --test resource_scope_core \
    --test source_resource_execution --test source_resource_acquired_only \
    --test native_buffer_typing --test native_buffer_core \
    --test native_buffer_modules --test native_buffer_runtime \
    --all-features -- -D warnings
cargo fmt --all -- --check
git diff --check
```

Lint and formatting logs are `/tmp/task0045-clippy-752b69c.log` and
`/tmp/task0045-fmt-752b69c.log`. TASK-0049 owns the later full
checkpoint gate; these focused checks do not close it. TASK-0046 owns contents
and dependency proof, TASK-0047 owns connected execution observations, and
TASK-0048 owns integrated case and native/retention evidence. No downstream task
has been advanced. The next checkpoint requires separately authorized
TASK-0046 dependency admission, followed by TASK-0047 execution and TASK-0048
integrated evidence before TASK-0049 can run its fresh full gate.

Run added unit tests for builtin metadata and summary authentication as well.
After TASK-0046/0047 connect, obtain the runtime observations for the positive
cases through TASK-0047's public source path. Retain commands, exact inputs,
diagnostics/results and independent review; compare the actual retained commit.
Check changed specification links, authority and Markdown. TASK-0049 owns the
full checkpoint gate; these focused checks do not close it.

## Discoveries

Independent review identified missing Pure Core staged denial, a known-instance
identity omission in nested Row arguments, and temporary payload copies without
iterative ownership across a later metadata refusal. The repair shares the
computational denial between dialects, scans complete effect instances on the
existing iterative worklist, and retains copied payload ownership until
transfer. These are foundation enforcement repairs, not changes to CP-0023
semantics. Independent code re-review and the refreshed evidence verdict are
clear. A paired private helper with genuine source-resource Row arguments checks
with Tick and rejects known generic Ops before checked-module publication. The
public safe helper instead reached an export-freeze `InvalidState`, including a
control without any generic import. This is a bounded candidate observation, not
a language restriction or a demonstrated baseline defect. The dedicated row
probe stays private; separate public generic-helper tests cover summary denial.

## Deviations

None authorized. Region construction from DN-0054, arbitrary pure-state resource
declarations and legacy API migration remain outside this task.
