# TASK-0068: Top-Level Declaration and Derive Macros

- ID: `TASK-0068`
- Status: implementation complete; retaining acceptance tracked in #206 and #258
- Related: [GitHub parent issue #206](https://github.com/dikini/ash-lang/issues/206),
  [retaining acceptance #258](https://github.com/dikini/ash-lang/issues/258),
  [CP-0034](https://github.com/dikini/ash-lang/blob/79c2d0723baa218a127640903f522694580bfc1e/docs/proposals/CP-0034-top-level-declaration-macros.md),
  [DN-0062](../design/DN-0062-hygienic-surface-macros.md),
  [slice 2 delivery plan](https://github.com/dikini/ash-lang/blob/79c2d0723baa218a127640903f522694580bfc1e/docs/design/macros/slice2-delivery-plan.md),
  [reviewed work structure](https://github.com/dikini/ash-lang/blob/79c2d0723baa218a127640903f522694580bfc1e/docs/design/macros/slice2-work-structure.md),
  [integration corpus](../design/macros/fixtures/README.md).

> This task records delivery of the accepted transition. Current language
> semantics are defined by the specification. Retaining acceptance is tracked
> by the linked issues; Main integration is a separate gate. The related
> CP-0034, plan and work structure links point to their original paths at the
> exact pre-cleanup commit.

## Dependencies

The retained [expression-syntax specification](../../spec/syntax-expansion.md)
is the slice 1 baseline. The accepted CP-0034 and the historical delivery plan
record the C1–C4 contract and corpus checks. The E4 checkpoint was retained by
[PR #298](https://github.com/dikini/ash-lang/pull/298) at
`17788de140a48a1c1d4a1d3aeb1d1ef2878d0a92`, tree
`2a9235f9c52c39376a12c724fbfa18394b04a419`. I19 was retained by
[PR #299](https://github.com/dikini/ash-lang/pull/299) at
`6e089e2e0c299c5ac158301bd132e28dd94f9f2e`, tree
`86e8d1a258e6fc1ea04790dc5d224c33facb10fc`.

The reviewed structure under [issue #206](https://github.com/dikini/ash-lang/issues/206)
records seven workstreams, 45 child issues and 112 original prerequisite links.
The linked issues record criterion acceptance and retaining readback. Development,
QA, review and acceptance checks remain independent: the developer prepares the
record, an independent reviewer checks it, and the developer applies and reads it
back. Main integration remains separate from the retaining branch.

## Work

Deliver imported top-level declaration macros and type/newtype derives,
including declarative templates, checked procedural transformers, quotation,
executable escapes, repetitions and state-threaded generators. Preserve syntax
contexts, protected fragments and source origins through the existing parser,
host and downstream compiler. Establish the early connected declaration path
at D8, the early quote/escape path at E4, and the complete public-driver path
at V3. The linked work structure records each unit's deliverables, acceptance
cases, prerequisites and hard boundaries.

### Do not do

Separately approved downstream repairs have their own reviewed scope and
evidence. They do not relax these boundaries for other work.

- Do not add or change downstream type checking, inference, semantic checking,
  name resolution, elaboration, publication rules or Core validation. Ordinary
  compiler stages check generated code and report its errors. Preserve spans,
  contexts and origins; if a downstream consumer is deficient, record its
  concrete gap separately and stop the affected path.
- Do not add a macro-specific semantic checker, second resolver, per-reference
  grants, automatic conflict repair, new host or new error protocol. Do not
  change slice 1 behavior except for CP-0034's accepted `syntax` reservation
  and syntax-service sum extensions.
- Do not implement local declaration macros, generated imports or generated
  syntax definitions, typed reflection, a generic conversion interface,
  implicit primitive conversion, an ambient compiler input for generator
  helpers, effects redesign, Wasm support or unrelated refactoring.
- Do not cross an individual work item's explicit prohibition because it
  appears convenient. Record the reason, return a contract change to its owner,
  and continue independent work within scope.

## Progress

The reviewed 45-unit delivery prediction remains 142 points, plus 8 points for
C1–C4, for 150 predicted points. These are planning estimates, not an effort or
completion measurement. The 112 native prerequisite links and original issue
criteria remain unchanged.

### Retained baseline

[PR #315](https://github.com/dikini/ash-lang/pull/315) retained the coherent
generator, escape, checked-capture, and separately approved #304/#310 work at
`8862a187894122b00be472b4c6a754422f604cee`, tree
`b345ce18b4fec10ae9d88ef466776c4504131391`. E3
[#246](https://github.com/dikini/ash-lang/issues/246) and checked capture
[#311](https://github.com/dikini/ash-lang/issues/311) were closed on their
original focused criteria after independent acceptance readback. G3
[#236](https://github.com/dikini/ash-lang/issues/236) and E2
[#239](https://github.com/dikini/ash-lang/issues/239) have also closed on their
original focused criteria after independent retained readback. The linked issue
records carry the status of the other original criteria.

### Retained caller-owned quotation

[PR #316](https://github.com/dikini/ash-lang/pull/316) retained the separately
authorized [#312](https://github.com/dikini/ash-lang/issues/312) repair at
`e9ab68f24487db53a04623cd4b38ef5d0d8c840a`, tree
`1476cdc6b3298c33c9574462052b609a88714be6`. It connects the authentic
caller-owned quote to the completed caller's ordinary term, constructor,
nominal type, interface, and effect consumers, and accounts for the first
quote-aware resource preflight. Existing source, owner, module, binder,
checking and resource boundaries are preserved. #312 was closed on its
original criteria after independent retained and live readback.

On the reviewed candidate the original imported-name, literal, and handwritten
controls each return 84. Two distinct quote introductions retain the actual
API-owned nominal, constructor, interface, method, effect, and operation
identities through final linking and host teardown. Ordinary unknown, private,
wrong-kind, wrong-arity, and invalid generated-code cases reject; a local
`Box(Bool)` also shadows an imported `Box(Int)` in both the quoted case and its
handwritten control. The original I17 and I22 matrices match their prior raw
streams. The matching native generator and escape importers execute without
their copied source paths, returning 310 and 246. The original caller-quote
library and importer also build and run source-free, returning 84. A combined
caller-role importer interprets to 84 but its native build reaches a
`RegistryMetadata` image refusal; the handwritten combined control reaches the
same refusal. No image or Core repair is included in this delivery.

The original #312 completion requires authentic caller context, ordinary
imported and private visibility, unchanged module and binder identities,
checking, Core rules, and resource ledgers, plus the original three controls,
two-invocation isolation, teardown, and relevant source/owner mutation checks
on the real final consumer. Those original criteria remain authoritative.
Three later syntax probes currently fail: plain and quoted nested syntax return
`runtime.invalid-control-state`; the syntax bridge reaches `type.internal`.
Their exact internal causes are unproved. They are outside this bounded repair.

### Retained publication and downstream repairs

[PR #318](https://github.com/dikini/ash-lang/pull/318) retained the H4 evidence
and H4 [#233](https://github.com/dikini/ash-lang/issues/233) was accepted. The
original generated and handwritten publication graphs preserve their observed
identities, results and ordinary duplicate refusals.

[PR #323](https://github.com/dikini/ash-lang/pull/323), retained at
`d0a08c6527c9010865228ca6440b4b5fbb73eb5c`, completed H6
[#237](https://github.com/dikini/ash-lang/issues/237) and the separately
authorized bounded downstream repairs in [#303](https://github.com/dikini/ash-lang/issues/303),
[#304](https://github.com/dikini/ash-lang/issues/304),
[#310](https://github.com/dikini/ash-lang/issues/310),
[#314](https://github.com/dikini/ash-lang/issues/314),
[#319](https://github.com/dikini/ash-lang/issues/319) and
[#320](https://github.com/dikini/ash-lang/issues/320). The original H6 matrix
and its corrected supplemental importer controls were independently checked;
the unchanged relation graph and the original method, Global and nested derive
graphs return 42 with their recorded controls. The focused H6 acceptance is
separate from the integrated corpus and verification evidence.

[PR #324](https://github.com/dikini/ash-lang/pull/324), retained at
`3285587c2461ecd9cc3088a70cabaf946dd32a35`, completed V1
[#241](https://github.com/dikini/ash-lang/issues/241) and the separately
authorized diagnostic repairs in [#313](https://github.com/dikini/ash-lang/issues/313),
[#321](https://github.com/dikini/ash-lang/issues/321) and
[#322](https://github.com/dikini/ash-lang/issues/322). The original I01–I08
driver corpus, handwritten controls and prescribed negative variants were
reviewed in human and JSON modes, alongside the focused provenance, locale and
work-budget checks. Independent retained and issue-state readbacks completed.

### Completion evidence

[PR #327](https://github.com/dikini/ash-lang/pull/327) carries the completion
from retaining base `3285587c2461ecd9cc3088a70cabaf946dd32a35`. The reviewed
code checkpoint is `fab27a4242f49921f70843bccfea1a1f4784c73d`, tree
`48932f65435aebd21764acfd1222089fc36e7369`. The actual quote-helper calls and
checked-entry, site, owner and cache reuse are recorded in
[#329](https://github.com/dikini/ash-lang/issues/329); caller-owned quote
identity is tracked in [#328](https://github.com/dikini/ash-lang/issues/328).
The cold and warm resource controls passed on the continuing ledger, with
source and raw evidence reviewed in the handoff at
`evidence/completion-independent-qa/quote-resource-335b4021/receipt.md`
(SHA-256 `679a8818a70223fde0350cbce5c6969bc3c9d4aad4e217544ac79f89c4babfe9`).

On the code checkpoint, 35 individually selected focused cases passed, including
the original early categories result 246, actual captured quotes, resource and
payment boundaries, four native admission controls and the public declaration
service. The focused receipt is `attempt6-controls-receipt.json` (SHA-256
`988a360ccd5b8c437678a0bdf6cb62c0550aae5218f3ff18c600fc887b87279a`).
The unchanged 441-row public union plus Bulgarian presentation passed 442 cases;
its receipt is `attempt6-public/receipt.json` (SHA-256
`893103e1d6ee33cd75c05cf1f0e753c9782e9b31fece84424614452861f0ff7e`).
Both records are under `evidence/adapter-producer-335b-development/` in the
local handoff. The original I16 same-host transfer, foreign-handle refusal and
selected-method Core mutation also passed; their receipt in that directory is
`fab-i16-controls-receipt.json` (SHA-256
`5b49f9728b044af79ab0c53a5e6d93761f957ca36ccdb131597d8efc9c8e4eb1`).
Independent focused and public QA verified the earlier two records.

The two original copied native hosts returned 252 and 42 after their complete
source graphs were moved away. Their receipt is
`evidence/completion-fab27a42/native-execution/receipt.json` (SHA-256
`285c8997e15f467593d86fe1a0eafe6fd92b591a40e8ae8a1dc2d37aabb16bea`). The
receipts identify their exact inputs and are transferred to later
documentation-only trees only when the complete runtime input set remains equal.

The reviewed original graph remains 45 units, 150 predicted points and 112
prerequisite edges. The completion handoff began with 33 closed and 12 pending
units; the linked issue records carry subsequent acceptance. G7
[#245](https://github.com/dikini/ash-lang/issues/245), its G4, G5, G6 and E5
successors, and the original I01–I22 corpus keep their original criteria. The
separately authorized repairs for [#317](https://github.com/dikini/ash-lang/issues/317),
[#325](https://github.com/dikini/ash-lang/issues/325) and
[#326](https://github.com/dikini/ash-lang/issues/326) are recorded in the handoff
at `receipts/user-authorization-317-325-326-retention.json` (SHA-256
`24c2ec674265b58834a8f2d50e8f42b5540e632e95f5d7bff11ef35dfbfebb23`).

The original I16 mutation and native/image evidence, independent final reviews,
fresh full verification, retained input equality and acceptance are tracked by
[the retaining criterion](https://github.com/dikini/ash-lang/issues/258) and
[the parent issue](https://github.com/dikini/ash-lang/issues/206). Before this
completion, the last full workspace checkpoint was E4 at
`17788de140a48a1c1d4a1d3aeb1d1ef2878d0a92`; focused checks do not replace a
fresh full gate. Main integration is separate.

The retained downstream repair carries checked original owner and nominal-pair
facts through validation and the supported image path; the independently
checked issue records preserve the original positive and fixed mutation evidence.
For #303 and #319 the user approved a supported-image proof amendment. The
original concrete method and handwritten control run to 42 and the actual
Core-use mutation remains a refusal. A concrete method implementation remains
unsupported by the existing MethodEvidence image boundary; the supported image
case uses a genuine declaration-only Interface and Method-local owner. No
concrete implementation or adaptor preservation after image restore is claimed.

### Earlier retained acceptances

S5 and R6 were closed on their original focused criteria. Their connected
corpus and verification criteria are recorded separately in the work structure.

- D2 [#216](https://github.com/dikini/ash-lang/issues/216), D7
  [#217](https://github.com/dikini/ash-lang/issues/217) and H1
  [#220](https://github.com/dikini/ash-lang/issues/220) are closed on their
  original focused criteria, supported by the D8 checkpoint in
  [PR #295](https://github.com/dikini/ash-lang/pull/295), retained at
  `ac3a70d3bd2e24fd316d7bee3b98c08458ccdee1`.
- H2 [#224](https://github.com/dikini/ash-lang/issues/224) and H3
  [#229](https://github.com/dikini/ash-lang/issues/229) are closed on their
  original focused context and refusal criteria using retained evidence and D8.
- E4 [#242](https://github.com/dikini/ash-lang/issues/242) is closed after the
  independently reviewed E4 checkpoint and the retained PR #298 tree above.
  E1 [#226](https://github.com/dikini/ash-lang/issues/226) is closed on its
  focused parsing and admission criteria after
  [PR #307](https://github.com/dikini/ash-lang/pull/307), retained at
  `f26860994b947a5899518b9ce9343ecf61b174fe`. E2
  [#239](https://github.com/dikini/ash-lang/issues/239) subsequently closed
  on its original focused quotation criteria after PRs #315 and #316.
- S3 [#221](https://github.com/dikini/ash-lang/issues/221) is closed on its
  original focused host-transfer criteria. The exact I16 mutation and other
  later connected cases remain at their original gates.
- D3 [#218](https://github.com/dikini/ash-lang/issues/218), D4
  [#222](https://github.com/dikini/ash-lang/issues/222), D5
  [#223](https://github.com/dikini/ash-lang/issues/223), and G1
  [#228](https://github.com/dikini/ash-lang/issues/228) are closed on their
  original focused criteria after the I19 delivery and independent readback.
  D6 [#219](https://github.com/dikini/ash-lang/issues/219) and G2
  [#231](https://github.com/dikini/ash-lang/issues/231) subsequently closed
  on their focused criteria after PR #307. Connected declaration, repetition
  and generator graphs retain their original acceptance criteria.

## Verification criteria

The original criteria follow. Their acceptance status is tracked in the linked
issues and is not inferred from this list.

- Exercise I01–I22, including their fixed positive, negative, mutation,
  hygiene, origin and diagnostic cases, through the specified component and
  connected paths. Preserve the supplemental early cases and the full original
  integration graphs.
- Run the retained slice 1 regression cases; exercise the real macro
  library, caller and importer through the public driver, interpreter and
  supported build/image path. Verify existing host bounds, transfer and
  teardown, and I16's specified independent validator and handle controls.
- Update implementation, tests, specification and tool documentation
  together. Check that accepted but unimplemented behavior is not reported as
  current Ash before it is retained.
- Obtain independent QA and review on the pinned integrated candidate;
  repair and re-review findings. Run the agreed fresh full gate and retain its
  receipts for the exact inputs.
- Integrate to the authorized retaining branch, verify retained evidence
  and complete independent acceptance readback. Main integration remains a
  separate gate under the project workflow.

## Durable findings and evidence

The S2 broad expression-admission proposal would change existing allowance
consumption and error ordering. Its reviewed narrow Declaration route retains
the existing expression paths and ledgers; protected or generated consumers
require their own actual accounting and ownership evidence. The original
[reviewed work structure](https://github.com/dikini/ash-lang/blob/79c2d0723baa218a127640903f522694580bfc1e/docs/design/macros/slice2-work-structure.md)
preserves
the individual criteria and prerequisite edges. The S2 analysis and narrow
plan remain in the handoff under `evidence/host-consumer-plan/` with SHA-256
`801df2a0c32307afab3e867786f70ea78cb321d73bad1da5de23095be3013aaf`
and `70907e327c3c50f6232916149c99694efd70c1fec2363f208fa8c99206782da0`.

The caller-quote focused identity and scope receipt is
`312-role-identities-d9f970f2/receipt.json`
(SHA-256 `06d8487ac560aa01b889f019948b734ce716e23825785fb6daf66f952633b994`).
The matching public receipt is `312-final-public-d9f970f2/receipt.json`
(SHA-256 `97146fb507fea302a2df23b6f77b864ec566e6d4c846aeecf4886876a3623b99`);
the unchanged I17 and I22 matrix receipts are
`i17-matrix-d9f970f2/receipt.json` (SHA-256
`63a61e607365a52cd002d5d26dbe2bc1cc0bcea96c9af04a9471b3ddf2501b98`) and
`i22-matrix-d9f970f2/receipt.json` (SHA-256
`2e19d682a526382e78439d180fbdef2d9a9e7476af8e6095ea733a37452fd0f8`).
The native receipt is `312-native-matching-d9f970f2/receipt.json` (SHA-256
`b92ba462f7fea913d76b9c0b5963f7f11c62d2c17ad0c34507699381b738396a`);
the original caller and handwritten controls are in
`312-native-controls-d9f970f2/receipt.json` (SHA-256
`838c8d652a41b367e2d511a899967f1640b025da3673bde615a98f08f9e36b2b`).
These paths are relative to the local task handoff's `evidence/generator-escape/`
unless stated otherwise. Pinned source, tool, fixture, protected-input and
before/after details are in the receipts.

The H4 public receipt is `evidence/h4-h6-retained-e9ab68f2/h4-receipt.json`
(SHA-256 `1a70bcdbd9ad236b8bfb07690a8c4232d2a6c3897e0dccc5f524d4a3f2271ae5`),
and its exact test-only observation is `h4-focused-receipt.json` in that
same directory (SHA-256
`12bf998d82aa2b5d63e8cf161a1e11078e85006b1589fa444c8f7bc385ff0a7d`). The
H6 original and copied-variant matrix is `h6-receipt.json` there (SHA-256
`5096f354d33b55631e97eadfff2b1d73254170b2116ade3861272d9b1bc60bf9`);
the corrected interface-importer control is `h6-interface-v2-receipt.json`
(SHA-256 `336be70489fd2e2867dc9b7fea8370d1f0aa8a8619eb4e01f7b6a2183249eae2`).

The complete superseded chronology, individual historical evidence links,
accepted changes, and prior local findings remain in the
[retained task record at 8862a187](https://github.com/dikini/ash-lang/blob/8862a187894122b00be472b4c6a754422f604cee/docs/tasks/TASK-0068-top-level-declaration-macros.md).
The preserved `ash-lang-task-0068` checkout and its untracked protected test are
not part of the delivery checkout. Main's unrelated work remains separate.

## Deviations

[PR #281](https://github.com/dikini/ash-lang/pull/281) retained the accepted
inline result-expression alternative for escapes. It does not add inline outer
local declarations or change ordinary block grammar. Further semantic changes
require the proposal workflow; separately owned downstream gaps stay with their
owning tasks. The specification defines current semantics, and the original
criteria continue to govern delivery acceptance.
