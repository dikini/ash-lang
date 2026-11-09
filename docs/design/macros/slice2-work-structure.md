# CP-0034: local work structure and issue drafts

This records the reviewed work structure and issue drafts for
[CP-0034](../../proposals/CP-0034-top-level-declaration-macros.md), filed under
[issue #206](https://github.com/dikini/ash-lang/issues/206). The accepted proposal
is partially implemented on the retaining branch;
[TASK-0068](../../tasks/TASK-0068-top-level-declaration-macros.md) owns active
delivery. Use the [delivery plan](slice2-delivery-plan.md) and live issues for
current status. This document preserves the reviewed units and
[predefined integration corpus](fixtures/README.md); it does not itself
authorize implementation or define Ash semantics.

The parent and workstream entries below organize the original 45 delivery units.
They do not carry extra points. C1–C4 are completed planning prerequisites:
their 8 predicted points are recorded in the delivery plan, not assigned to
new work. The original 45 units total **142 points**; together with those
8 historical planning points, the scope prediction is **150 points**. These
are fixed difficulty predictions, not elapsed time or measured actual effort.

## Parent: CP-0034 delivery

**Outcome:** deliver imported top-level declaration macros and type/newtype
derives through the public compiler path, with the accepted syntax, hygiene,
quotation, generator, diagnostic and verification cases.

**Do not do:** do not implement local declaration macros, generated imports,
generated syntax definitions, typed reflection, a new host, additional semantic checks,
effects redesign, or unrelated compiler work. Preserve slice 1 behavior except
for CP-0034's accepted `syntax` reservation and syntax-service sum extensions.
When a required consumer is missing, retain syntax provenance, record a
separate downstream gap, stop the dependent work and continue independent work.

**Acceptance:** the integrated candidate satisfies the linked I01–I22 corpus,
retained slice 1 regression, the public driver and supported consumers,
independent QA and review, the fresh gate and authorized retaining-branch
readback. A fixture or planning result alone does not establish implementation
or acceptance; current partial delivery is recorded in the task and plan.

**Prerequisites:** accepted CP-0034, recorded C1–C4 and active TASK-0068. The
retaining branch, roles, integration owner and delivery permissions are recorded
in the task and delivery plan; recheck their current refs and assignments at
dispatch. Main integration is a separate gate.

## Workstream hierarchy

Each workstream is a child of the parent and contains the listed work units.
The workstream totals are sums of their children, not additional estimates.

| Workstream | Units | Points |
| --- | --- | ---: |
| Declaration entry and output | D1, D2, D3, D4, D5, D7, D6, D8 | 25 |
| Contexts and publication | H1, H2, H3, H4, H5, H6 | 18 |
| Syntax service and checked host | S1, S2, S3, S4, S5 | 17 |
| Quotation and executable escapes | E1, E2, E4, E3, E5 | 18 |
| Derives | R1, R2, R3, R4, R5, R6 | 17 |
| Repetition and generators | G1, G2, G3, G7, G4, G5, G6 | 23 |
| Connected evidence and delivery | V1, V2, V3, V4, V5, V6, V7, V8 | 24 |
| **Original delivery scope** | **45 units** | **142** |

### Workstream drafts

Each workstream inherits the parent boundaries. Its acceptance does not add a
second estimate or replace the connected gates assigned to V1–V8.

#### Declaration entry and output — D1–D8

**Outcome:** import, match and expand top-level declaration syntax into ordinary
structured declarations. **Do not do:** no per-form semantic checker, text
re-lexing, generated imports or changed expression-macro behavior. **Acceptance:**
I01/I07 positive cases return 42 through D8; malformed headers, captures and
output reject as fixed in I14/I15/I21. **Prerequisites:** C3 and the common
launch conditions. D1 and S1 can proceed in parallel.

#### Contexts and publication — H1–H6

**Outcome:** pass generated identifiers and declarations with their contexts
and origins to existing collection, resolution and publication. **Do not do:**
no second resolver, grants, automatic conflict repair or changed visibility
rules. **Acceptance:** I12/I13 caller and definition context graphs work;
duplicate and private-access cases reject downstream. **Prerequisites:** D2 and
D7 for H1. H2 and H5 each need H1, D3 and D6, and can then proceed in parallel.

#### Syntax service and checked host — S1–S5

**Outcome:** extend the existing closed syntax interface and host transfer for
protected declaration data. **Do not do:** no replacement host, open syntax
hierarchy or bypass of authenticated handles and teardown. **Acceptance:**
I16 host transfer and failure cases and I18/I22 migration cases meet their
unit gates. **Prerequisites:** C3 for S1; other inputs are specified per child.
S1 and D1 can proceed in parallel.

#### Quotation and executable escapes — E1–E5

**Outcome:** parse and evaluate accepted quotes and escapes with lexical
captures, nesting, context and existing host limits. **Do not do:** no implicit
conversion, ambient capture access, special type checker or new error protocol.
**Acceptance:** I22 quote, capture, freshness, repetition and failure cases
meet their specified gates; E4 establishes the early public-driver path.
**Prerequisites:** D6 and S1 for E1; remaining handoffs are per child.

#### Derives — R1–R6

**Outcome:** support declarative and procedural derives on top-level types and
newtypes in source order. **Do not do:** no derives on other forms, inferred-type
reflection, new implementation selection or duplicate checker. **Acceptance:**
I09–I11 return their fixed results; unsupported inputs and authored failures
reject with the prescribed origins. **Prerequisites:** D1 and D6 for R1;
R1 and H5 can progress independently after their inputs are ready.

#### Repetition and generators — G1–G7

**Outcome:** match and expand repetitions and thread ordinary state through the
fixed fragment-returning generator paths. **Do not do:** no ambient compiler
input, conversion library, type inference or step per value read.
**Acceptance:** I17/I19 fixed counts, state and nesting results pass; mismatch,
malformed and wrong-type inputs reject through their established checks.
**Prerequisites:** D3 for G1; the generator connection has the E2/S4/G3
prerequisites shown below. D4, D5 and G1 can proceed in parallel after D3.

#### Connected evidence and delivery — V1–V8

**Outcome:** establish integrated behavior, diagnostics, documentation, QA,
review, gates and retaining-branch readback. **Do not do:** no component-only
substitute for a connected test, downstream compiler modifications, or Main
integration without its separate gate. **Acceptance:** I01–I22 and retained
slice 1 cases have pinned evidence; the reviewed candidate passes the fresh gate
and acceptance is read back. **Prerequisites:** V1 starts after D8, D4, D5 and
H3; all V units have their own prerequisites. QA and review begin on available
pinned unit candidates before the final integrated audits.

## Dependencies and parallel work

The prerequisite lists below refer to the exact unit IDs in the
[dependency diagram](slice2-delivery-plan.md#dependency-and-parallelism-overview).
They are blocking producer/consumer prerequisites, not a demand that an entire
workstream finish before another begins. A focused producer-interface check can
unblock a consumer; it does not close a later connected gate.

- D1 and S1 can begin after the common prerequisites. After D3, D4, D5 and G1
  have no dependency on one another. H2 and H5 can proceed after H1, D3 and
  D6. R1 can
  proceed after D1 and D6, independently of H5. Their actual shared files and
  interfaces still need coordinated ownership.
- Agree the syntax-selection, capture, output, module-staging, generator,
  quote/escape and provenance/host boundaries in the
  [delivery plan](slice2-delivery-plan.md#retained-boundaries-and-interfaces)
  before parallel producers and consumers start. Do not infer ownership from
  the issue grouping. Assign one owner for each shared grammar, projection,
  syntax representation and host file; schedule shared integration and heavy
  builds. Separate worktrees do not make conflicting edits independent.
- The integration owner connects the first declaration path at D8, the first
  quote/escape path at E4 and the complete path at V3. QA and independent
  review can assess a pinned candidate for one unit while development proceeds
  on other unblocked units. V5/V6 audit the integrated result rather than
  replacing per-unit checks.
- If implementation reveals a missing dependency, incompatible handoff or
  need to cross a prohibition, stop the affected work, record the reproducer
  and return the contract or downstream gap to its owner. Do not invent a
  compensating semantic checker inside macros.

## Draft child work items

Each entry follows the [bounded-work template](../../../.github/ISSUE_TEMPLATE/bounded-work.md).
The linked corpus gives the full source graphs and expected results; a
component check does not stand in for a connected result explicitly assigned
to a later unit. Every entry includes its specific hard prohibition as well as
the shared parser/transform boundary. New tests may be added during delivery
without weakening the predefined cases.

### Declaration entry and output

#### D1: Parse and project `syntax declaration: (name)` headers and the reserved `syntax` word

**Summary:** Parse and project `syntax declaration: (name)` headers and the reserved `syntax` word.

**Description:** Work at this boundary: module-header parser → syntax definition and keyword classification. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not change expression-macro headers or implement derive clauses.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I21 expression headers still parse except names now prohibited by the reservation; malformed new headers and I22 user-defined `syntax` terms, macro names, module paths and imported aliases reject. `syntax_value`, `declaration` and `@builtin.compiler.syntax` remain usable.
- [ ] Negative or refusal boundary: I22 `reserved_term.ash`, `reserved_macro.ash`, `reserved_module.ash` and `reserved_alias.ash` reject; `reserved_control.ash` remains valid.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** C3. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### D2: Select imported declaration syntax by category and rename

**Summary:** Select imported declaration syntax by category and rename.

**Description:** Work at this boundary: import discovery → locally selected syntax name and category. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not add generated imports or permit a module to use its own macro.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I21 renamed import works; collision and same-module use reject.
- [ ] Negative or refusal boundary: I21 `collision.ash` and `own_definition.ash` reject.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D1. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### D3: Match declaration invocations with identifier and expression captures

**Summary:** Match declaration invocations with identifier and expression captures.

**Description:** Work at this boundary: selected matcher → identifier and expression captures. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not implement repetition or arbitrary parser callbacks.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I01/I07/I19 select the intended captures; missing input fails at the invocation.
- [ ] Negative or refusal boundary: I15 `missing.ash` rejects at invocation; the I07 type-capture variant belongs to D4.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D2. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### D4: Connect type and pattern captures to their ordinary parsers

**Summary:** Connect type and pattern captures to their ordinary parsers.

**Description:** Work at this boundary: ordinary type and pattern parsers → category-preserving captures. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not infer types or perform pattern semantics.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I07/I19 type and binder/body captures retain boundaries; invalid category rejects.
- [ ] Negative or refusal boundary: I07 missing type-capture variant rejects at invocation; wrong-category input rejects through the ordinary parser.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D3. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### D5: Match one complete braced declaration fragment

**Summary:** Match one complete braced declaration fragment.

**Description:** Work at this boundary: ordinary declaration parser → one braced declaration capture. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not accept several declarations as one capture or implement local declaration macros.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I19 multiline signature/equation capture is retained; incomplete or multiple declarations reject.
- [ ] Negative or refusal boundary: In a fresh copy of I19 `main.ash`, remove part of the captured signature/equation declaration or add a second declaration inside its capture; reject the incomplete or multiple-declaration input.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D3. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### D7: Parse structured output for the first declaration path

**Summary:** Parse structured output for the first declaration path.

**Description:** Work at this boundary: structured declaration syntax → ordinary declaration parser and projection. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not re-lex output as text or create a semantic checker for each declaration form.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Parse I01/I07 handwritten target forms; reject incomplete and recovery-bearing declaration input without text re-lexing. Macro-output assertions need D6 and D4 where applicable.
- [ ] Negative or refusal boundary: I01/I07 incomplete or recovery-bearing output is rejected without text re-lexing.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D1. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

#### D6: Parse declaration templates and validate macro notation using D7

**Summary:** Parse declaration templates and validate macro notation using D7.

**Description:** Work at this boundary: template parser → admitted macro notation and structured template. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not resolve free names or type-check unused templates.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I14 `unused_bad.ash` and literal `forbidden_import.ash` reject at definition admission; I15 unused unresolved free name is admitted. Imports produced by procedural output are rejected at output admission after that path is connected.
- [ ] Negative or refusal boundary: I14 `unused_bad.ash` and `forbidden_import.ash` reject at definition while I15 `unused_free.ash` is admitted.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D1, D7. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### D8: Connect a declaration template through the public driver and ordinary checker

**Summary:** Connect a declaration template through the public driver and ordinary checker.

**Description:** Work at this boundary: imported declaration template → public driver → ordinary generated-program checking. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not modify ordinary checking or alter expression-macro behavior to make the path pass.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I01/I07 execute to 42; an ordinary generated type error retains its normal cause and macro origins.
- [ ] Negative or refusal boundary: I15 `type_error.ash` fails in ordinary checking with macro origins.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D3, D4, D6, D7, H1, H2, H3. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

### Contexts and publication

#### H1: Hand generated declarations to the existing module-collection path

**Summary:** Hand generated declarations to the existing module-collection path.

**Description:** Work at this boundary: generated structured declarations → existing module collector. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not change module resolution or publication to accept generated output.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Focused syntax handoff preserves forward references; I20's public-driver recursion assertion also needs H2.
- [ ] Negative or refusal boundary: An incomplete or recovery-bearing declaration must not reach the collector; use the D7 rejection boundary.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D2, D7. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### H2: Preserve caller-selected and introduced term contexts in syntax

**Summary:** Preserve caller-selected and introduced term contexts in syntax.

**Description:** Work at this boundary: matcher and template → term contexts carried to ordinary resolution. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not add a second resolver, rename conflicting declarations, or change global name allocation.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Focused I12 `early_terms.ash` preserves distinct caller-selected helpers and gives 84; `early_terms_duplicate.ash` and `early_terms_handwritten_duplicate.ash` reject in ordinary resolution with both sources and macro origins. A focused handoff to the actual resolver may be used before D8; the public-driver assertion and full I12 graph remain connected gates.
- [ ] Negative or refusal boundary: both isolated duplicate-helper cases reject through ordinary resolution and identify both sources.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** H1, D3, D6. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### H3: Preserve type, constructor, interface and pattern contexts in syntax

**Summary:** Preserve type, constructor, interface and pattern contexts in syntax.

**Description:** Work at this boundary: matcher and template → nominal and pattern contexts carried to ordinary resolution. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not change nominal identity allocation or introduce type analysis.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Focused I12 `private_types.ash` and I19 `binder.ash` handoffs preserve nominal and pattern contexts; duplicate private types and constructors fail in ordinary resolution with both sources and macro origins. Their public-driver results remain connected gates after D8.
- [ ] Negative or refusal boundary: I12 duplicate private types and constructors reject downstream with both sources.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** H1, D4, D6. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### H4: Emit macro-written public names with the agreed spelling and contexts

**Summary:** Emit macro-written public names with the agreed spelling and contexts.

**Description:** Work at this boundary: introduced public declarations → normal lookup in caller and importer. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not add visibility or duplicate checks to macro machinery.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I12 invoking and importing modules use the generated public function, type and constructor; existing duplicate checks reject collisions.
- [ ] Negative or refusal boundary: I12 duplicate public names reject under unchanged ordinary resolution.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** H2, H3. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

#### H5: Preserve definition-context references and their syntax provenance

**Summary:** Preserve definition-context references and their syntax provenance.

**Description:** Work at this boundary: introduced free references → definition-context lookup and origin. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not add per-reference grants or loosen private access.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Focused I13 `early_owner.ash` passes definition-private helper and renamed facade references to the unchanged resolver despite caller shadowing; `early_owner_private.ash` rejects direct private access. Its public-driver result and the full I13/opacity graphs remain connected gates after D8 and at V3.
- [ ] Negative or refusal boundary: `early_owner_private.ash` rejects direct private access; the full opacity graph remains at V3.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** H1, D3, D6. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### H6: Hand generated declarations and implementations to ordinary publication

**Summary:** Hand generated declarations and implementations to ordinary publication.

**Description:** Work at this boundary: module collector → existing declaration and implementation publication. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not change export or visibility rules, implementation selection or duplicate checking.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I03/I04/I12 importer visibility and duplicate implementation checks use unchanged downstream rules.
- [ ] Negative or refusal boundary: I04 duplicate implementation rejects under existing publication and checking.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** H4. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 2 points.

### Syntax service and checked host

#### S1: Extend the agreed closed syntax sums and capture shapes, including `SyntaxKeyword` and `Dollar`; preserve existing fragment cases and origin metadata

**Summary:** Extend the agreed closed syntax sums and capture shapes, including `SyntaxKeyword` and `Dollar`; preserve existing fragment cases and origin metadata.

**Description:** Work at this boundary: closed public syntax sums → existing Ash consumers and token operations. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not replace the closed sum with an open hierarchy or invent interface version selection.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I18 old exhaustive capture match fails for missing cases; explicit migration and fallback are checked. I22 `token_exhaustive.ash` fails ordinary coverage under CP-0034; `token_kinds` recognizes the new tokens and rejects incorrect spellings. Its connected quote round trip also needs E2 and E4.
- [ ] Negative or refusal boundary: I18 old exhaustive capture match and I22 `token_exhaustive.ash` reject under the extended sums; I22 invalid token spellings reject.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** C3. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

#### S2: Expose protected type, pattern and declaration fragments to checked Ash

**Summary:** Expose protected type, pattern and declaration fragments to checked Ash.

**Description:** Work at this boundary: protected fragments → checked Ash syntax service and category admission. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not expose inferred types or unchecked compiler internals.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I11/I19 preserve category, contexts and origins through parse and unwrap, including nested groups and siblings; wrong category and excess depth are refused without a stack abort.
- [ ] Negative or refusal boundary: I14 wrong-category input and I11/I19 excess-depth transfer reject without stack abort.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** S1, D4, D5. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### S3: Transfer structured declaration output through the retained host

**Summary:** Transfer structured declaration output through the retained host.

**Description:** Work at this boundary: checked host syntax handles → structured output before root closure. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not create a second host or bypass handle lifetime and transfer checks.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Focused host transfer rejects a foreign handle and retains valid structured output after root closure. Nested groups and siblings exercise parse-service and final-output transfer; excess depth fails without partial publication. The exact I16 indexed-transformer mutation remains at V3; I14 wrong-category graph also needs S2.
- [ ] Negative or refusal boundary: focused foreign-handle and excess-depth transfers reject without partial output; the exact I16 mutation remains at V3.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** S1, D7. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

#### S4: Connect checked procedural declaration expansion to module staging

**Summary:** Connect checked procedural declaration expansion to module staging.

**Description:** Work at this boundary: checked transformer output → module staging and syntax admission. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not change the host's effect rules or publish partial output after failure.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Supplemental I16 `procedural_declaration/main.ash` uses a real checked declaration transformer through the public driver and returns 42; `rejected.ash` retains its authored rejection and publishes nothing. The exact I16 derive/teardown graphs remain at V3.
- [ ] Negative or refusal boundary: the authored `rejected.ash` transformer publishes no partial module.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** S3, H1, S2. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### S5: Complete closed-sum migration through the production path

**Summary:** Complete closed-sum migration through the production path.

**Description:** Work at this boundary: extended syntax sums → old expression-macro consumer and fallback. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not change existing expression-macro meaning or suppress exhaustive-match failures.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I18 original expression transformation returns 42 after migration; new cases and valid fallback behave as specified.
- [ ] Negative or refusal boundary: I18 old exhaustive match rejects; a fallback is retained only when its behavior is correct.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** S2, S4. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

### Quotation and executable escapes

#### E1: Parse and admit expression quotes, escaped blocks and their nesting with the containing definition

**Summary:** Parse and admit expression quotes, escaped blocks and their nesting with the containing definition.

**Description:** Work at this boundary: quote/escape parser → admitted template and ordinary-code syntax. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not resolve output names, type-check template output or introduce new splice or repetition forms.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I17 `malformed_helper.ash` rejects its unused malformed quote at definition; I22 `unbound_outer.ash` rejects an unknown outer splice. The I17 malformed generator graph remains a G7 gate after its repetition and generator forms exist. Existing `$name` and repetition forms keep their meaning; parsing does not execute an escape.
- [ ] Negative or refusal boundary: I17 `malformed_helper.ash` and I22 `unbound_outer.ash` reject at definition for their specified causes.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D6, S1. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

#### E2: Construct expression fragments from quotes in ordinary checked Ash, with variable holes and protected syntax

**Summary:** Construct expression fragments from quotes in ordinary checked Ash, with variable holes and protected syntax.

**Description:** Work at this boundary: ordinary checked Ash quotation → protected expression fragment and hole insertion. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not add automatic conversions, require a compiler `Input` argument, or change protected-fragment copy rules.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Focused checked-host execution of the I17 ordinary `digit`, `as_subtemplate`, `next_number` and `is_first` helper slice supplies the fixed 0–5 fragments; `wrong_hole.ash` fails ordinary checking. The full I17 module and caller gates remain with G7/G5/G6/V3. Once E4 connects escapes, I22 `freshness.ash` returns 20 and constructions from the same quote source have distinct introductions; the quote round trip checks structure, contexts and origins.
- [ ] Negative or refusal boundary: I22 `wrong_hole.ash` fails ordinary checking; no implicit conversion is introduced.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** E1, S2, S4. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

#### E4: Prepare ordinary escaped code for checking, execute reached escapes through the existing checked host and insert their results through syntax admission

**Summary:** Prepare ordinary escaped code for checking, execute reached escapes through the existing checked host and insert their results through syntax admission.

**Description:** Work at this boundary: template escape → existing checked host → structured syntax admission. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not add a second host, error protocol, special semantic checker or partial publication.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] As the early connected quote path, I22 supplemental `early_nested.ash` returns 44 through the public driver with nested quotes and escapes. The original shared-module `nested.ash` remains required at V3 after repetition and generator support. `atomic.ash` is bounded and publishes nothing; `wrong_category.ash` rejects through syntax admission. `wrong_code_type.ash` and `primitive_escape.ash` fail through ordinary checking or existing syntax admission; no escape-specific type checker.
- [ ] Negative or refusal boundary: I22 `atomic.ash` hits the existing bound without publishing; `wrong_category.ash`, `wrong_code_type.ash` and `primitive_escape.ash` reject through the specified existing checks.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** E1, E2, S4, D8. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

#### E3: Supply lexically scoped captures as syntax values to escaped code

**Summary:** Supply lexically scoped captures as syntax values to escaped code.

**Description:** Work at this boundary: matcher captures → lexical syntax values in escaped ordinary code. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not make capture bindings ambient in ordinary helpers or add access to whole repeated captures.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I22 supplemental `early_categories.ash` returns 246 for all five capture categories and distinguishes capture and local names; `illicit_helper.ash` and `out_of_scope.ash` reject. The original shared-module `categories.ash` and `hygiene.ash` remain required at V3 after repetition and generator support.
- [ ] Negative or refusal boundary: I22 `illicit_helper.ash` and `out_of_scope.ash` reject; helpers cannot read captures implicitly.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** E4, S2, H2, H3, H5, G1. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### E5: Connect escape reads to repetition drivers and cached generator values

**Summary:** Connect escape reads to repetition drivers and cached generator values.

**Description:** Work at this boundary: escape capture reads and generator values → existing repetition driver and cache. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not step generators per read, invent repetition drivers, or add lazy generator execution.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I22 `repetition.ash` returns 44, its mismatch rejects and zero iterations do not execute the escape; `nested_repetition.ash` returns 46420 using the correct capture and cached generator at each depth.
- [ ] Negative or refusal boundary: I22 `mismatched.ash` rejects, and the zero-iteration case does not execute its diverging escape.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** E3, G2, G6. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

### Derives

#### R1: Parse derive definition headers and deriving clauses on top-level types and newtypes, reusing template admission

**Summary:** Parse derive definition headers and deriving clauses on top-level types and newtypes, reusing template admission.

**Description:** Work at this boundary: derive definition and deriving clause parser → admitted derive syntax. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not add attributes or derives on functions, interfaces or local declarations.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I09 nonempty list, trailing comma and rename work; empty and unsupported forms reject. I14 unused malformed derive rejects and I15 unused unresolved derive free name is admitted.
- [ ] Negative or refusal boundary: I09 empty and unsupported deriving clauses and I14 `unused_bad_derive.ash` reject.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D1, D6. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 2 points.

#### R2: Supply the original subject and optional name capture

**Summary:** Supply the original subject and optional name capture.

**Description:** Work at this boundary: original type or newtype declaration → derive subject and optional name. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not supply inferred types or already elaborated declarations.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I09/I10 preserve subject, name, caller context and origin; wrong syntax category rejects.
- [ ] Negative or refusal boundary: I09 `wrong_kind.ash` rejects the wrong syntax category; a wrong-category subject is rejected without type reflection.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** R1, S2. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### R3: Expand the complete parsed derive list in source order and retain the subject once

**Summary:** Expand the complete parsed derive list in source order and retain the subject once.

**Description:** Work at this boundary: derive subject and ordered list → original subject plus ordered generated syntax. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not change the original subject or reorder derives.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Focused staging traverses the whole I09 list and retains the subject once; I20's authored procedural failures also need R5 and S4. R6 owns the stronger ordering, failure and generated-subject evidence.
- [ ] Negative or refusal boundary: I20 first authored derive/declaration failure is preserved once R5 and S4 connect the failure path.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** R2, H1, D7. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### R4: Connect fixed declarative derives to ordinary output checking

**Summary:** Connect fixed declarative derives to ordinary output checking.

**Description:** Work at this boundary: declarative derive output → ordinary declaration checking. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not introduce derive-specific implementation or duplicate checking.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I09 type/newtype and renamed derive cases execute; duplicate implementations fail ordinary checking.
- [ ] Negative or refusal boundary: I09 duplicate implementation rejects in ordinary checking.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** R3, H2, H5. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### R5: Connect procedural derives and an authored structural example

**Summary:** Connect procedural derives and an authored structural example.

**Description:** Work at this boundary: procedural derive syntax → retained checked host and declaration admission. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not add compiler reflection for the authored example or a second procedural host.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I10/I11 one-, two- and three-constructor graphs execute; payload rejection retains its origin.
- [ ] Negative or refusal boundary: I10 `payload.ash` retains its authored rejection and source origin.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** R3, S4, H5. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### R6: Complete multiple and generated-subject derives

**Summary:** Complete multiple and generated-subject derives.

**Description:** Work at this boundary: ordered derives and generated subjects → bounded nested expansion. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not broaden derives to arbitrary declaration categories or semantic queries.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I09 declaration sequence retains each original subject once; `ordered_first.ash`, `ordered_second.ash`, `generated_failure.ash` and `generated_order.ash` reject in the specified order with origins; nested output is bounded.
- [ ] Negative or refusal boundary: I09 `ordered_first.ash`, `ordered_second.ash`, `generated_failure.ash` and `generated_order.ash` reject in the specified order.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** R4, R5, H5, H3. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

### Repetition and generators

#### G1: Parse and match nested `*`/`+` repetitions and separators

**Summary:** Parse and match nested `*`/`+` repetitions and separators.

**Description:** Work at this boundary: repetition matcher → ordered nested capture groups. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not implement unapproved matcher features or semantic checks.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Focused I19 matcher checks capture zero, one and multiple items in source order; `empty_plus.ash`, `trailing_separator.ash` and `ambiguous_definition.ash` reject with their specified syntax causes. The `counts.ash` connected result belongs to G2.
- [ ] Negative or refusal boundary: I19 `empty_plus.ash`, `trailing_separator.ash` and `ambiguous_definition.ash` reject for their fixed syntax causes.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D3. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

#### G2: Expand template repetitions from captured drivers

**Summary:** Expand template repetitions from captured drivers.

**Description:** Work at this boundary: matched capture drivers → repeated template syntax. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not change the step-function signature or infer missing repetition drivers.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I19 ordered equal-length drivers work; `mismatched.ash` and `missing_driver_definition.ash` reject with their specified syntax causes. `counts.ash` returns 42 through the connected path once D8 exists.
- [ ] Negative or refusal boundary: I19 `mismatched.ash` and `missing_driver_definition.ash` reject without partial expansion.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** G1, D6. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### G3: Parse generator clauses, bind names and construct seed/step uses for unchanged ordinary Ash checking

**Summary:** Parse generator clauses, bind names and construct seed/step uses for unchanged ordinary Ash checking.

**Description:** Work at this boundary: generator directive → state and ordinary step call syntax. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not inspect generator bodies or add type inference, evidence selection or global-value access to the macro engine.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I17 clause ownership and duplicate names are checked at definition; generated uses preserve seed and step contexts. Invalid-step and caller-global refusals need the checked execution in G7; inline/imported seed results also need G5.
- [ ] Negative or refusal boundary: I17 duplicate generator binding rejects at definition; invalid step and caller-global cases await G7.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** G2, S1. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### G7: Connect state-only generator calls to both selected fragment-construction paths using C3's I17 inputs

**Summary:** Connect state-only generator calls to both selected fragment-construction paths using C3's I17 inputs.

**Description:** Work at this boundary: state-only generator call → either selected fragment-construction path. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not add a construction API, error protocol, conversion or evidence resolution in the macro engine, restrict ordinary helper types, or expose definition-private values to callers. Do not count quote-backed traversal as raw-syntax construction evidence.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Subtemplate and procedural variants return fixed fragments for states 0–5 with a state-only step. Unused malformed quotes reject at definition. `invalid_step.ash`, `local.ash`, `procedural_local.ash`, `wrong_type.ash` and `procedural_wrong_type.ash` are handed to ordinary checking/staging; correctly typed `diverging.ash` hits the existing bound and publishes nothing. Wrong-category and generated-type-error variants retain existing causes and origins. Whole callers and these connected rejections join G5/G6 and V3.
- [ ] Negative or refusal boundary: the named invalid-step, caller-global, wrong-seed, malformed-quote, divergence, wrong-category and generated-type cases retain their existing causes; no partial output is published.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** G3, S4, E2. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### G4: Initialize independent generator state at the owning scope

**Summary:** Initialize independent generator state at the owning scope.

**Description:** Work at this boundary: generator directive and seed → independent state at owning scope. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not share state between independent generators or add ambient compiler input.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I17 two generators retain separate seeds; zero iterations do not create per-iteration instances.
- [ ] Negative or refusal boundary: I17 zero-iteration case does not create per-iteration generator instances.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** G7. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### G5: Thread `(next state, value)` and cache one value per iteration

**Summary:** Thread `(next state, value)` and cache one value per iteration.

**Description:** Work at this boundary: step result → next state and cached iteration syntax value. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not call a step more than once per owning iteration or independently for each use.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I17 `$number` fragments for three names are 0, 1, 2; repeated reads in an iteration reuse the same value. The subtemplate and procedural `main.ash` callers produce 100, 1, 2 and return 310.
- [ ] Negative or refusal boundary: I17 repeated reads reuse one step result; a per-read step result fails the fixed sequence assertion.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** G4. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### G6: Preserve nested generator lifetime and outer cached values

**Summary:** Preserve nested generator lifetime and outer cached values.

**Description:** Work at this boundary: nested repetition scope → generator lifetime and outer cached values. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not extend generator visibility beyond its declared repetition or introduce lazy evaluation.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I17 global, reset and mixed-depth graphs return 3210, 1010 and 546210.
- [ ] Negative or refusal boundary: I17 `reset.ash` and `mixed_depth.ash` return 1010 and 546210, exposing incorrect generator lifetime or outer cached-value reuse.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** G5. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

### Connected evidence and delivery

#### V1: Exercise all current declaration output forms through the driver

**Summary:** Exercise all current declaration output forms through the driver.

**Description:** Work at this boundary: generated declaration output → public driver and ordinary checker. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not replace driver tests with hand-written controls or add per-form semantic checks.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I01–I08 and handwritten controls, including ordinary malformed/duplicate and opacity failures.
- [ ] Negative or refusal boundary: I01–I08 fixed malformed, duplicate and opacity variants reject with ordinary causes.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D8, D4, D5, H3. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### V2: Verify cross-stage diagnostics, origins and bounded failure

**Summary:** Verify cross-stage diagnostics, origins and bounded failure.

**Description:** Work at this boundary: parser, host and ordinary compiler failures → human and JSON diagnostics. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not change downstream diagnostics or invent a macro-specific checker.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I14–I15 and I22 human/JSON causes, macro and quote frames, recursion and atomic failures; no second type checker.
- [ ] Negative or refusal boundary: I14–I15 and I22 fixed invalid and bounded-failure graphs retain their causes, macro frames and origins.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** D8, R4, R5, G6, G7, H5, E5. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

#### V3: Connect the full macro library, caller, importer and supported consumers

**Summary:** Connect the full macro library, caller, importer and supported consumers.

**Description:** Work at this boundary: macro library → caller → importer → interpreter and supported build/image consumer. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not add downstream compiler validation or quietly waive the I16 requirement.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I16–I22 through the public driver; interpreter, supported build/image and retained-host teardown. Use existing downstream checks without modifying them.
- [ ] Negative or refusal boundary: I16 foreign-handle and Core mutation cases reject under the existing consumers; failed expansions publish no partial module.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** V1, V2, R6, G6, G7, S5, H5, H6, E5. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 4 points.

#### V4: Update language and tool documentation for the implemented delta

**Summary:** Update language and tool documentation for the implemented delta.

**Description:** Work at this boundary: retained implementation and tests → specification and tool documentation. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not describe proposed or unimplemented behavior as current language truth.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Specification and compiler syntax-service documentation describe retained behavior, with links and authority checked.
- [ ] Negative or refusal boundary: Do not describe accepted but unimplemented behavior as current Ash; broken links and mismatched authority fail the documentation check.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** V3. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Developer; independent QA and review of the candidate.

**Difficulty:** 3 points.

#### V5: Perform independent integrated QA against the corpus

**Summary:** Perform independent integrated QA against the corpus.

**Description:** Work at this boundary: pinned integrated candidate and initial corpus → independent QA result. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not count component-only evidence as a passed connected acceptance case.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] I01–I22 and slice 1 regression coverage are mapped to the exact candidate; gaps remain explicit.
- [ ] Negative or refusal boundary: Keep an acceptance case outstanding if its public consumer, negative case, or pinned evidence is missing.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** V3, V4. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Independent QA.

**Difficulty:** 3 points.

#### V6: Perform independent integrated review and address confirmed findings

**Summary:** Perform independent integrated review and address confirmed findings.

**Description:** Work at this boundary: pinned integrated candidate and evidence → independent review result. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not self-approve confirmed findings or expand scope during repair.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Review checks boundaries, real consumers and pinned evidence; affected repairs are re-reviewed.
- [ ] Negative or refusal boundary: A confirmed boundary violation or missing connected evidence remains a finding until repaired and re-reviewed.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** V3, V4. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Independent reviewer, with the developer repairing confirmed findings.

**Difficulty:** 3 points.

#### V7: Run the agreed fresh full gate and retain its receipts

**Summary:** Run the agreed fresh full gate and retain its receipts.

**Description:** Work at this boundary: reviewed integrated candidate → fresh full-gate receipts. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not reuse receipts for different inputs or substitute focused tests for the full gate.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] The exact integrated candidate passes the required workspace gate and its specified native/image evidence.
- [ ] Negative or refusal boundary: A failed gate or a receipt for different inputs cannot pass this gate.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** V5, V6. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Integration owner.

**Difficulty:** 2 points.

#### V8: Integrate to the authorized retaining branch and read back acceptance

**Summary:** Integrate to the authorized retaining branch and read back acceptance.

**Description:** Work at this boundary: verified integration candidate → authorized retaining branch and acceptance readback. Use the accepted
proposal and the corresponding work-unit gate in the delivery plan.

**Goals and deliverables:**

- [ ] Deliver the stated outcome and producer/consumer boundary, with the focused evidence named below.
- [ ] Record the candidate, evidence, unresolved connected checks and next owner.

**Do not do — hard boundaries:**

- Do not add, change or work around downstream type checking, inference,
  semantic checking, resolution, elaboration or Core validation. Preserve
  contexts and origins; report a downstream gap separately.
- Do not change retained slice 1 behavior beyond CP-0034's accepted `syntax`
  reservation and syntax-service sum extensions. Do not implement local
  declaration macros, generated imports, generated syntax definitions or typed
  reflection.
- Do not redesign effects or resources, add Wasm support or refactor unrelated
  compiler code.
- Do not merge to Main or claim acceptance without the specified independent readback.
- Stop any affected work that needs these boundaries crossed; record the
  concrete reason and continue independent work. Do not expand scope locally.

**Acceptance cases:**

- [ ] Retained inputs match evidence; task acceptance and remaining limitations are recorded and independently checked. Main is a separate gate.
- [ ] Negative or refusal boundary: Do not mark acceptance complete if retained inputs differ from the verified candidate or readback is missing.
- [ ] Focused evidence and independent review are recorded; later connected
  assertions remain open until their named consumers are available.

**Prerequisites and parallel work:** V7. Governing artifacts: CP-0034,
the delivery plan and the linked corpus. The owning task and authorized base
are also required. Proceed alongside other unblocked units only after the relevant producer/consumer interface and shared-file
ownership are agreed. Planned role: Integration owner and independent acceptance reviewer.

**Difficulty:** 2 points.
