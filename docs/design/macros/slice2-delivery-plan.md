# Declaration and derive macros: first delivery plan

This is a **local draft**, not an active task, a set of GitHub issues, an
accepted change proposal, or authority to implement. It develops
[CP-0034](../../proposals/CP-0034-top-level-declaration-macros.md) using the
[working planning rules](../../project/issue-planning.md) and the initial
[integration corpus](fixtures/README.md). The units below are planning units;
their eventual issue hierarchy and assignments are not yet selected.

## Baseline and outcome

Produce imported, hygienic top-level declaration macros and type/newtype
derives, including declarative templates, checked Ash transformers, repetition
and state-threaded generators. Generated declarations go through ordinary Ash
parsing, resolution and checking. Include the actual public compiler path,
diagnostics, supported runtime/build consumers and final delivery evidence.

Slice 1 is QA-confirmed and was retained at `e58aea09`; local `main` now
contains it through merge `5852a977`. The current
[syntax expansion specification](../../../spec/syntax-expansion.md) is the
expression-macro baseline. The merge changes no `src/`, `spec/` or `tests/`
content relative to that retained commit. Recheck the actual implementation
base and required gates before delivery. The original
slice 1 task and QA record can be read from Git at
`d0b1bf68:docs/tasks/TASK-0067-expression-macros.md`.

CP-0034 remains proposed. Before product implementation, reconcile and obtain
acceptance of its contract, create the owning Ash task, and agree on the actual
retaining branch and delivery permissions. This plan does not make those
decisions on the user's behalf.

## Hard boundaries

- **Implementation is limited to parsing and syntax transformation.** Carry
  syntax contexts, source spans and expansion origins into the existing
  compiler pipeline. Macros produce code without proving or repairing its
  validity. The ordinary parser and downstream compiler diagnose errors in the
  produced code. Helpers that support parsing or rewriting are in scope; helpers
  that establish the semantic correctness of generated Ash are not.
- Do not add or change type checking, inference, semantic verification,
  elaboration, Core validation or other downstream compiler logic. In
  particular, do not modify resolution or publication rules to make an
  expansion succeed. The ordinary downstream compiler checks generated code
  and reports its errors. Tests may exercise that existing behavior.
- If a downstream subsystem misses a required check or cannot consume the
  transformed syntax, retain its contexts/spans, or report a useful error,
  record a separate issue for that subsystem with a reproducer and expected
  behavior. Stop the dependent path and continue independent work. Do not
  implement a substitute check or patch the downstream subsystem in this slice.
  Return a language-contract change to CP-0034 for a design decision. The local
  plan records findings; it does not create GitHub issues without authorization.
- Do not change expression-macro behavior from slice 1, including its syntax
  imports, context selection, protected fragments, diagnostics or host limits.
- Do not implement local declaration macros, generated imports or syntax
  definitions, derive attributes, arbitrary parser callbacks, inferred-type
  reflection or Core generation by macros.
- The parser checks syntax; macro machinery matches, rewrites and threads
  generator state; ordinary compiler stages resolve and check the result. Do
  not introduce a macro-specific type checker, per-declaration semantic checker
  or a second visibility/duplicate-checking system.
- Do not reintroduce per-reference grant objects or broad Core correspondence
  checks. Preserve issued contexts and use the retained resolver, access rules
  and linking closure. Keep authenticated syntax handles and host boundaries.
- Do not add compiler `Input` to generator step functions or an ambient input
  service to connect their state. An expression-fragment step has the ordinary
  `State -> (State, Syntax.ExpressionFragment)` type. Helpers may have any
  ordinary Ash type; ordinary checking and the retained host rules apply.
- Do not redesign effects or resources, add Wasm support, generalize the
  compiler for hypothetical future macros, or refactor unrelated code.
- A necessary change outside a unit's scope returns to the design owner with a
  concrete example. Stop the affected part; continue independent authorized
  work. Do not silently expand the assignment or invent semantics locally.

## Retained boundaries and interfaces

The intended vertical path is:

```text
entry module -> discover fixed imports -> select imported syntax -> parse
declaration invocation -> match captures -> expand template or checked Ash
transformer -> parse structured declaration output -> expand derives in source
order -> collect module declarations -> ordinary resolve/check -> link/validate
-> interpreter and supported build/image consumer
```

The procedural branch enters the retained checked host, transfers output before
closing its root, and preserves failure and origin information. Declaration
and derive expansion may have different entry forms while following the same
source order. There is one integration owner for this entire path. Component
tests do not replace its acceptance check.

The following are contracts to agree before parallel producers and consumers
start; they are not mandates for particular Rust types or new public APIs.

| Boundary | Producer -> consumer | Required agreement |
| --- | --- | --- |
| Selection | Import discovery -> parser and expander | Local syntax name, category, owner context and rename; expression compatibility and collision behavior. |
| Captures | Matcher -> template or transformer | Category, repetition nesting, source order, contexts and origins; incomplete/recovery-bearing input does not cross projection. |
| Output | Template/host -> declaration parser and collector | Ordered structured syntax and protected fragments; category, origin and failure handling, without text re-lexing or partial publication. |
| Module staging | Collector/derive entry -> ordinary resolver | Source-order expansion, original derive subject, generated declarations, forward references, scope and export spelling. |
| Generator | Matcher/seed/step -> template repetition | Seed environment; `State -> (State, Syntax.ExpressionFragment)` state threading, per-iteration reuse and nesting; both selected construction paths, ordinary Ash checking and retained host rules. |
| Provenance and host | Syntax services -> parser, resolver, diagnostics and linker | Context versus origin, valid handle lifetime, checked-host effects, bounds, output transfer and teardown. |

Likely implementation areas on the retained baseline are `src/parser/grammar.rs`,
`src/parser/project.rs`, `src/surface.rs`, `src/syntax.rs`, `src/driver.rs`,
`src/compiler_syntax.ash`, `src/eval/syntax.rs` and their existing tests. Any
driver or host change is limited to syntax input, transformation and handoff;
it does not authorize changes to downstream compiler logic. Exact file
ownership follows the agreed interfaces and actual diff; these are not
permission to refactor an entire file. Use `tests/surface_macros.rs`, `tests/macro_host.rs`,
`tests/modules_syntax.rs`, `tests/module_loading.rs`, `tests/diagnostic_json.rs`
and the relevant existing image/build tests where they own the boundary.

## Pre-implementation contract checks

These checks are part of planning and can begin before CP-0034 is accepted.
They must not add implementation or silently decide language semantics.

| Unit | Result | Points | Prerequisites | Gate |
| --- | --- | ---: | --- | --- |
| C1 | Reconcile CP-0034 with slice 1's grammar, service, contexts and host. | 2 | Slice 1 on local main | **Planning reconciliation recorded:** see the proposal and [boundary record](declaration-slice.md#slice-1-contract-boundary). I18/I21 connected tests await slice 2; check their inputs against the retained interface before acceptance. |
| C2 | Record the ordinary typed generator contract. | 2 | Retained syntax service | **Decision recorded:** any ordinary function of the required state-to-pair type can be used; normal Ash checking applies. Both subtemplate and procedural construction are selected. C4 owns complete proposed I17 source inputs; G7 owns their implementation and connected evidence. |
| C4 | Transcribe complete I17 source variants from the fixed behavior. | 2 | C1, C2 | Replace obsolete wrapper-based inputs with both selected 0–5 fragment builders, ordinary state-only steps/helpers, callers and negative variants. Preserve the README's results and add unused malformed-subtemplate inputs. Deliver proposed source graphs and their case mapping to C3; do not claim they run before implementation. |
| C3 | Independently review and freeze interfaces, corpus inputs and scope. | 2 | C1, C2, C4 | Review C4's complete I17 inputs, the boundary map, first connected path, exclusions and initial fixtures, including how syntax and origins reach unchanged downstream consumers. G7 must consume those fixed inputs through existing syntax admission, without a new API or error protocol. Check the baseline without claiming unimplemented macro graphs pass; I12's connected checks belong to H2–H4 and V3. Record downstream gaps separately; return contract changes to design. Slice 1 has no selectable interface version; artifact versioning remains a separate concern. |

C3 is the pre-implementation corpus gate. I17's expected values and failures
are fixed in its README, but C4 must first transcribe complete Ash sources:
both bounded 0–5 fragment builders, their ordinary state-only steps and helpers,
the existing callers and mutations, and the unused malformed-subtemplate
cases. Preserve those assertions and the selected approaches; do not invent
grammar or an API to make a source example look complete. Incomplete sources
keep C3 open. The sources are proposed acceptance inputs, not passing tests;
G7 implements and exercises them after this gate rather than defining its own
integration cases during implementation.

Implementation units below require **accepted CP-0034, C3, an owning task and
an authorized implementation base**. C1 and C2 can be investigated in parallel;
one owner reconciles their changes to shared proposal text.

## Planned work units

Points are fixed predictions of relative difficulty, including each unit's
focused verification and review. They are not elapsed time or earned credit.
Each unit is at most four points in this draft; the sum is checked below.
The revised total is 130 points. Preserve the earlier 65-, 95- and 126-point
predictions and the intermediate 128-point revision as historical records.
The calibration below records the changed score and added preparation unit;
this is not a measured result or an arithmetic conversion from slice 1.

The I-identifiers refer to the [initial corpus](fixtures/README.md). A focused
gate may establish an early parser or component assertion, but its connected
driver assertion remains pending until its consumers exist. Negative inputs
and expected results are those specified by the linked fixture README.

### Declaration syntax and the first path

| Unit | Result | Points | Prerequisites | Acceptance gate |
| --- | --- | ---: | --- | --- |
| D1 | Parse and project `syntax declaration: (name)` headers. | 2 | C3 | I21 old expression headers still parse; malformed new header rejects. |
| D2 | Select imported declaration syntax by category and rename. | 3 | D1 | I21 renamed import works; collision and same-module use reject. |
| D3 | Match declaration invocations with identifier and expression captures. | 3 | D2 | I01/I07/I19 select the intended captures; missing input fails at the invocation. |
| D4 | Connect type and pattern captures to their ordinary parsers. | 3 | D3 | I07/I19 type and binder/body captures retain boundaries; invalid category rejects. |
| D5 | Match one complete braced declaration fragment. | 3 | D3 | I19 multiline signature/equation capture is retained; incomplete or multiple declarations reject. |
| D7 | Parse structured output for the first declaration path. | 4 | D1 | Parse I01/I07 handwritten target forms; reject incomplete and recovery-bearing declaration input without text re-lexing. Macro-output assertions need D6 and D4 where applicable. |
| D6 | Parse declaration templates and validate macro notation using D7. | 3 | D1, D7 | I14 unused malformed syntax rejects at definition; I15 unused unresolved free name is admitted. Forbidden generated output is rejected when the output path is connected. |
| D8 | Connect a declaration template through the public driver and ordinary checker. | 3 | D3, D4, D6, D7, H1, H2 | I01/I07 execute to 42; an ordinary generated type error retains its normal cause and macro origins. |

**Boundary:** extend the existing grammar/projection and structured expansion
path. Do not add a parser implementation per declaration form or perform
downstream semantic checking in the expander.

### Module contexts and publication

| Unit | Result | Points | Prerequisites | Acceptance gate |
| --- | --- | ---: | --- | --- |
| H1 | Hand generated declarations to the existing module-collection path. | 3 | D2, D7 | Focused syntax handoff preserves forward references; I20's public-driver recursion assertion also needs H2. |
| H2 | Preserve caller-selected and introduced term contexts in syntax. | 3 | H1 | I12 distinct caller-selected helpers work; duplicate generated and handwritten helper names fail in ordinary resolution with both sources and macro origins. |
| H3 | Preserve type, constructor, interface and pattern contexts in syntax. | 3 | H1, D4 | I12 distinct caller-selected nominal names work; duplicate private types and constructors fail in ordinary resolution with both sources and macro origins; I19 captured binder/body graph. |
| H4 | Emit macro-written public names with the agreed spelling and contexts. | 4 | H2, H3 | I12 invoking and importing modules use the generated public function, type and constructor; existing duplicate checks reject collisions. |
| H5 | Preserve definition-context references and their syntax provenance. | 3 | H1 | I13 existing resolution finds the private helper and renamed facade despite caller shadowing; private and opaque access still reject. |
| H6 | Hand generated declarations and implementations to ordinary publication. | 2 | H4 | I03/I04/I12 importer visibility and duplicate implementation checks use unchanged downstream rules. |

**Boundary:** transform syntax and preserve contexts, then hand the result to
unchanged resolution, visibility, evidence and publication. Do not modify those
stages or introduce per-reference grants or macro duplicate/type analysis.

### Syntax service and procedural host

| Unit | Result | Points | Prerequisites | Acceptance gate |
| --- | --- | ---: | --- | --- |
| S1 | Extend the agreed closed syntax sums and capture shapes; preserve existing fragment cases and origin metadata. | 3 | C3 | I18 old exhaustive source match fails for missing cases; explicit migration and appropriate fallback are checked. |
| S2 | Expose protected type, pattern and declaration fragments to checked Ash. | 3 | S1, D4, D5 | I11/I19 preserve category, contexts and origins through parse and unwrap, including nested groups and siblings; wrong category and excess depth are refused without a stack abort. |
| S3 | Transfer structured declaration output through the retained host. | 4 | S1, D7 | I16 foreign-handle output rejects and valid output survives root closure. Nested groups and siblings exercise both parse-service and final-output transfer; excess depth fails without partial publication. I14 wrong-category graph also needs S2. |
| S4 | Connect checked procedural declaration expansion to module staging. | 3 | S3, H1 | I16 real transformer and nested/failed output use the public driver with no partial result. |
| S5 | Complete closed-sum migration through the production path. | 3 | S2, S4 | I18 original expression transformation returns 42 after migration; new cases and valid fallback behave as specified. |

**Boundary:** reuse the checked Ash host, syntax services, bounds and teardown.
Do not create a second host or assume a selectable syntax-interface version
without a reconciled contract. Preserve the retained stack-safe transfer path.

### Derives

| Unit | Result | Points | Prerequisites | Acceptance gate |
| --- | --- | ---: | --- | --- |
| R1 | Parse derive definition headers and deriving clauses on top-level types and newtypes, reusing template admission. | 2 | D1, D6 | I09 nonempty list, trailing comma and rename work; empty and unsupported forms reject. I14 unused malformed derive rejects and I15 unused unresolved derive free name is admitted. |
| R2 | Supply the original subject and optional name capture. | 3 | R1, S2 | I09/I10 preserve subject, name, caller context and origin; wrong syntax category rejects. |
| R3 | Expand derives in source order and retain the subject once. | 3 | R2, H1, D7 | Focused staging retains the subject once; I20's authored procedural failures also need R5 and S4. |
| R4 | Connect fixed declarative derives to ordinary output checking. | 3 | R3, H2 | I09 type/newtype and renamed derive cases execute; duplicate implementations fail ordinary checking. |
| R5 | Connect procedural derives and an authored structural example. | 3 | R3, S4 | I10/I11 one-, two- and three-constructor graphs execute; payload rejection retains its origin. |
| R6 | Complete multiple and generated-subject derives. | 3 | R4, R5, H5 | I09 declaration sequence retains each original subject once; `ordered_first.ash`, `ordered_second.ash`, `generated_failure.ash` and `generated_order.ash` reject in the specified order with origins; nested output is bounded. |

**Boundary:** derives inspect supplied syntax only. Do not query inferred types,
implementation selection or arbitrary checked declarations; generic behavior
is implemented by the derive author and checked as ordinary output.

### Repetition and generators

| Unit | Result | Points | Prerequisites | Acceptance gate |
| --- | --- | ---: | --- | --- |
| G1 | Parse and match nested `*`/`+` repetitions and separators. | 4 | D3 | Focused I19 matcher checks capture zero, one and multiple items in source order; `empty_plus.ash`, `trailing_separator.ash` and `ambiguous_definition.ash` reject with their specified syntax causes. The `counts.ash` connected result belongs to G2. |
| G2 | Expand template repetitions from captured drivers. | 3 | G1, D6 | I19 ordered equal-length drivers work; `mismatched.ash` and `missing_driver_definition.ash` reject with their specified syntax causes. `counts.ash` returns 42 through the connected path once D8 exists. |
| G3 | Parse generator clauses, bind names and construct seed/step uses for unchanged ordinary Ash checking. | 3 | G2, S1 | I17 clause ownership and duplicate names are checked at definition; generated uses preserve seed and step contexts. Invalid-step and caller-global refusals need the checked execution in G7; inline/imported seed results also need G5. |
| G7 | Implement both selected fragment-construction paths through checked execution using C3's frozen I17 inputs. | 4 | G3, S4 | Subtemplate and procedural variants each return the fixed fragments for states 0–5 with a state-only step and ordinary helpers. A malformed subtemplate in an unused generator or helper rejects at definition. Wrong-category and generated-type-error variants retain the existing syntax or ordinary checking cause and origins. Full caller and nesting results join G5/G6. |
| G4 | Initialize independent generator state at the owning scope. | 3 | G7 | I17 two generators retain separate seeds; zero iterations do not create per-iteration instances. |
| G5 | Thread `(next state, value)` and cache one value per iteration. | 3 | G4 | I17 three names produce 0, 1, 2; repeated `$number` in an iteration uses the same value. |
| G6 | Preserve nested generator lifetime and outer cached values. | 4 | G5 | I17 global, reset and mixed-depth graphs return 3210, 1010 and 546210. |

**Boundary:** state threading and substitution are macro responsibilities.
Type mismatches remain ordinary Ash errors. Do not add compiler input to the
step signature, a conversion interface, or automatic primitive conversion.
G7 delivers the already selected subtemplate and procedural authoring paths;
it does not select another API or error protocol. C3's complete source inputs
preserve the fixed I17 behavior for both variants, including the same seeds,
cache, nesting and failure assertions. The old wrapper-based source is not
complete input for this gate. Intermediate helpers may use any ordinary Ash
types; effects obey ordinary checking and the existing host rules.

### Connected verification and delivery

| Unit | Result | Points | Prerequisites | Acceptance gate |
| --- | --- | ---: | --- | --- |
| V1 | Exercise all current declaration output forms through the driver. | 3 | D8, D4, D5, H3 | I01–I08 and handwritten controls, including ordinary malformed/duplicate and opacity failures. |
| V2 | Verify cross-stage diagnostics, origins and bounded failure. | 3 | D8, R5, G6, G7, H5 | I14–I15 human/JSON causes, macro frames, recursion and atomic failures; no second type checker. |
| V3 | Connect the full macro library, caller, importer and supported consumers. | 4 | V1, V2, R6, G6, G7, S5, H5, H6 | I16–I21 through the public driver; interpreter, supported build/image and retained-host teardown. Use existing downstream checks without modifying them. |
| V4 | Update language and tool documentation for the implemented delta. | 3 | V3 | Specification and compiler syntax-service documentation describe retained behavior, with links and authority checked. |
| V5 | Perform independent integrated QA against the corpus. | 3 | V3, V4 | I01–I21 and slice 1 regression coverage are mapped to the exact candidate; gaps remain explicit. |
| V6 | Perform independent integrated review and address confirmed findings. | 3 | V3, V4 | Review checks boundaries, real consumers and pinned evidence; affected repairs are re-reviewed. |
| V7 | Run the agreed fresh full gate and retain its receipts. | 2 | V5, V6 | The exact integrated candidate passes the required workspace gate and its specified native/image evidence. |
| V8 | Integrate to the authorized retaining branch and read back acceptance. | 2 | V7 | Retained inputs match evidence; task acceptance and remaining limitations are recorded and independently checked. Main is a separate gate. |

**Boundary:** V1–V8 own connected evidence, documentation and delivery; they
do not replace focused checks or independent review performed during each
earlier unit. Tests may confirm that unchanged downstream checking reports
invalid generated programs; do not add or modify downstream compiler logic.
I16 may use a test-only mutation harness and the existing Core validator; it
does not authorize new downstream verification machinery. If its assertion
cannot be tested without changing that machinery, record a downstream
validator issue. Reuse receipts only when their inputs and required gate allow
it.

## Readiness questions before implementation

- Conflicting generated top-level names follow ordinary duplicate rules and
  fail downstream; they are not automatically renamed or resolved by syntax
  transformation. I12 must identify both sources and relevant macro origins.
  C3 reviews the existing resolution and publication boundary and the syntax
  handoff. H4 and V3 establish literal-public access through the connected
  path after implementation. Record any downstream resolver gap separately
  and return a contract change to CP-0034. H2–H4 do not authorize resolver
  changes.
- C2 records the chosen generator type; no separate construction API, type
  checker or error protocol is required by the macro contract. The current I17
  wrapper-based source predates the decision. C4 transcribes the complete
  proposed inputs and C3 independently reviews them before implementation; G7 then
  delivers both selected construction variants and definition-time syntax
  checks. This is remaining corpus and delivery work, not an unresolved choice
  between the two approaches.
- I16's Core mutation assertion may use test-only fixtures and a harness that
  exercises the existing validator. If it requires changing validator behavior,
  record a downstream validator issue; do not silently remove the assertion.
- The initial I19 corpus now fixes positive repetition counts and the
  trailing-separator, ambiguous-matcher and missing-driver failures. I09 and
  I14–I15 also fix derive ordering, generated-subject failure and unused derive
  template cases. These are proposed inputs, not passing implementation tests;
  independent review must check them against the proposal before C3 closes.

## Unit-specific do not do boundaries

Each unit also inherits the slice-wide hard boundaries. These prohibitions are
part of the plan, not optional issue text; stop the affected work if a required
result conflicts with them.

| Unit | Do not do |
| --- | --- |
| C1 | Do not treat the old proposal as implemented truth or change the retained expression contract. |
| C2 | Do not add a new error model, conversion interface, compiler `Input` to the step, general conversion libraries, or macro type checking. |
| C3 | Do not accept CP-0034, count obsolete I17 sources as complete, invent grammar or an API for missing source, or waive unresolved pipeline evidence on behalf of the design owner. |
| C4 | Do not change the fixed I17 behavior or select another construction approach, invent grammar or an API, add a conversion library, implement product support, or describe proposed sources as passing tests. |
| D1 | Do not change expression-macro headers or implement derive clauses. |
| D2 | Do not add generated imports or permit a module to use its own macro. |
| D3 | Do not implement repetition or arbitrary parser callbacks. |
| D4 | Do not infer types or perform pattern semantics. |
| D5 | Do not accept several declarations as one capture or implement local declaration macros. |
| D6 | Do not resolve free names or type-check unused templates. |
| D7 | Do not re-lex output as text or create a semantic checker for each declaration form. |
| D8 | Do not modify ordinary checking or alter expression-macro behavior to make the path pass. |
| H1 | Do not change module resolution or publication to accept generated output. |
| H2 | Do not add a second resolver, rename conflicting declarations, or change global name allocation. |
| H3 | Do not change nominal identity allocation or introduce type analysis. |
| H4 | Do not add visibility or duplicate checks to macro machinery. |
| H5 | Do not add per-reference grants or loosen private access. |
| H6 | Do not change exports, implementation selection or duplicate checking. |
| S1 | Do not replace the closed sum with an open hierarchy or invent interface version selection. |
| S2 | Do not expose inferred types or unchecked compiler internals. |
| S3 | Do not create a second host or bypass handle lifetime and transfer checks. |
| S4 | Do not change the host's effect rules or publish partial output after failure. |
| S5 | Do not change existing expression-macro meaning or suppress exhaustive-match failures. |
| R1 | Do not add attributes or derives on functions, interfaces or local declarations. |
| R2 | Do not supply inferred types or already elaborated declarations. |
| R3 | Do not change the original subject or reorder derives. |
| R4 | Do not introduce derive-specific implementation or duplicate checking. |
| R5 | Do not add compiler reflection for the authored example or a second procedural host. |
| R6 | Do not broaden derives to arbitrary declaration categories or semantic queries. |
| G1 | Do not implement unapproved matcher features or semantic checks. |
| G2 | Do not change the step-function signature or infer missing repetition drivers. |
| G3 | Do not inspect generator bodies or add type inference, evidence selection or global-value access to the macro engine. |
| G4 | Do not share state between independent generators or add ambient compiler input. |
| G5 | Do not call a step more than once per owning iteration or independently for each use. |
| G6 | Do not extend generator visibility beyond its declared repetition or introduce lazy evaluation. |
| G7 | Do not add a construction API, error protocol, conversion or evidence resolution in the macro engine, restrict ordinary helper types, or expose definition-private values to callers. Do not count the old wrapper-based source as revised I17 input. |
| V1 | Do not replace driver tests with hand-written controls or add per-form semantic checks. |
| V2 | Do not change downstream diagnostics or invent a macro-specific checker. |
| V3 | Do not add downstream compiler validation or quietly waive the I16 requirement. |
| V4 | Do not describe proposed or unimplemented behavior as current language truth. |
| V5 | Do not count component-only evidence as a passed connected acceptance case. |
| V6 | Do not self-approve confirmed findings or expand scope during repair. |
| V7 | Do not reuse receipts for different inputs or substitute focused tests for the full gate. |
| V8 | Do not merge to Main or claim acceptance without the specified independent readback. |

## Estimate calibration

This review used both retained Git evidence and the user-authorized Codex chat
**Orchestrate macro-slice delivery**, thread
`01a1abd4-9e53-7792-adab-b49682c7ce1e`. `ROOT` below means its local log:

```text
~/.codex/sessions/2026/11/05/rollout-2026-11-05T15-10-00-01a1abd4-9e53-7792-adab-b49682c7ce1e.jsonl
```

The durable slice 1 record is
`d0b1bf68:docs/tasks/TASK-0067-expression-macros.md`. Its historical ledger
contains fractional progress weights and elapsed-derived estimates of extra
work; those are not observed 1–5 difficulty scores for this plan. The
calibration uses what failed, which boundary was crossed, what was retained
and how it was verified. It does not scale by credits, elapsed time, lines,
test counts or the ledger's final effort index.

| Slice 1 observation and source | Transfer to this plan |
| --- | --- |
| A captured constructor qualifier failed admission; a repeated nullary capture was then mistaken for duplicate binders. The repair preserved refusal of actual duplicate lowercase binders and used ordinary pattern resolution. `ROOT` lines 19733, 19790, 19829 and 20027; reviewed commit `81eefcc9`. | D4, D6 and H3 need category and context cases with real positive and negative consumers. Keep their three-point scores. This does not authorize another pattern representation or downstream resolver repair in slice 2. |
| Nested output transfer overflowed a test-thread stack. Iterative transfer covered groups, siblings, parse-service transfer, final output and bounded refusal. Reverse conversion later failed separately on 100 nested groups at a 1 MiB stack. `ROOT` lines 16746, 16979 and 20012; reviewed commits `50ed262f` and `f106bbe7`. The retained task records unsuccessful active-disposal injections separately from observed failures. | Reuse the retained iterative paths and limits. S2 and S3 explicitly exercise both directions, nested siblings, lifetime and structured failure; their scores remain three and four. Do not infer a passing combined failure from an injection that never reached its hook or rebuild the host. |
| The all-use Core correspondence experiment and per-reference grants checked stronger machinery than the required source behavior. The planner and reviewer found no demonstrated source-level need; the grants were removed while contextual resolution, linking and privacy tests remained. `ROOT` lines 25624, 25691, 25726 and 25850; the retained task's approved amendment. | H1–H6 hand syntax to existing consumers. No grant, census, second resolver or semantic-checking work is in these estimates. The 126-point draft had no separate unit for that removed machinery, so there is no supported numerical subtraction to make a second time. H4 still requires the generated-public-name observation; a downstream gap remains separate work. |
| Late review found missing combined causes at diagnostic handoffs even after examples executed. `ROOT` lines 30718, 30937, 31935, 32898 and 33253; reviewed commits `fcd3325e`, `97a9113f` and `f621d075`. | V2 keeps a three-point connected diagnostic gate. Check retained causes and frames in human and JSON output, including ordinary generated-program errors. Transfer the failure cases, not permission to change downstream checking or diagnostics; report a gap separately if preserved syntax provenance is insufficient. |
| Separate syntax tests did not establish the exact mixed-tree round trip through one Ash identity transformer. QA exposed the missing observation, and `3c024d72` added it through the public driver before a fresh gate. `ROOT` lines 34611, 34660, 34740, 34871 and 34900. Final acceptance at `e58aea09` also retained the supported source-free native result and stated evidence limits (`ROOT` line 35233). | V3 requires an actual transformer, macro library, caller, importer and supported consumer. Keep V3 at four and retain separate V5/V6 independent audits, V7 gate and V8 retained readback. Each owns a distinct result; do not repeat component checks merely to fill these units or infer broader image support. |
| A forecast retired estimated minutes faster than elapsed time because work overlapped or was already underway; that was not an observed work rate. `ROOT` lines 30394 and 30486. | Preserve forecasts and completed planning separately. Reconcile existing evidence before assigning implementation, and record later observed difficulty without rewriting these predictions. No elapsed-to-point conversion is used here. |

The remaining scores have the following bounded rationale. Every score
includes focused verification and independent review of that unit; V5/V6
audit the integrated candidate rather than charging again for those reviews.

| Units and fixed scores | Basis for the prediction |
| --- | --- |
| C1/C2/C3/C4: 2 each | C1/C2 decisions are recorded. C4 produces the missing fixed corpus source; C3 independently reviews the complete boundary map and inputs. Source authorship and review have distinct outputs and owners. The I17 builders cover only the fixed 0–5 mapping, not a conversion library. C1–C3 retain their predictions; C4 is a new preparation estimate. None is measured actual difficulty. |
| D1: 2; D2–D6 and D8: 3 each; D7: 4 | Header syntax adapts a defined entry. Selection, capture categories, template admission and the first driver connection each cross a retained boundary. D7 must project all ordinary declaration forms and preserve protected fragments while refusing incomplete output. The constructor-capture repair is the comparison for category failures, not an estimate for duplicating ordinary parsers. |
| H1/H2/H3/H5: 3 each; H4: 4; H6: 2 | Context propagation crosses collection and ordinary lookup; generated public spelling adds a caller/importer observation. H6 is the narrower publication handoff. Existing expression hygiene reduces the mechanism to preserve and hand off, but does not establish module-binder or export behavior. H4 is not a budget for changing the resolver. |
| S1/S2/S4/S5: 3 each; S3: 4 | Extend closed sums, protected categories and their actual Ash consumers; retain migration failures and expression behavior. Transfer has the larger category, lifetime and bounded-failure surface demonstrated by the two separate stack repairs. These scores reuse the host rather than estimate a new host implementation. |
| R1: 2; R2–R6: 3 each | A bounded header/clause grammar precedes subject capture, ordering, ordinary declaration output and an authored syntax traversal. Multiple and generated subjects join both expansion branches. Slice 1 has no derive delivery to serve as an observed difficulty score; these are predictions from the named interfaces and cases. |
| G1/G6/G7: 4 each; G2–G5: 3 each | Nested matching, nested state and both fragment-construction paths have distinct failure surfaces. The other units each own one repetition or state boundary. Retained host evidence transfers; generator state, caching and the selected authoring paths have not been delivered. G7's correction is detailed below. |
| V1/V2/V4/V5/V6: 3 each; V3: 4; V7/V8: 2 each | Corpus coverage, causal diagnostics, documentation and the two independent audits have separate outputs. The complete library-to-consumer path is larger; pinned gate execution and retained acceptance are narrower bounded units. The late slice 1 mixed-tree case is why these final gates remain explicit. |

G7 changes from **2 to 4 points**. The old row covered fragment/context
preservation but did not explicitly implement both selected construction paths
or definition-time admission of subtemplates inside ordinary functions.
These are connected parts of one
fragment-producing boundary, so the correction keeps one unit. It adds no
new requested functionality, construction API, error protocol or semantic
analysis. C4 owns the missing complete I17 source before implementation, C3
owns independent review, and G7 owns execution; transcription is not charged
twice. Fixed outputs
and handwritten controls are not evidence that either path works. The other
unit scores are unchanged: the log evidence supports their
failure and verification obligations but supplies no measured difficulty that
would justify a numerical rerating.

C4 adds **2 points** for the missing pre-implementation source preparation.
The intermediate 128-point forecast corrected G7 but left transcription inside
C3's two-point review unit. This revision gives the source producer its own
bounded output and leaves independent review with C3. This is an explicit
preparation obligation for the already selected scope, not additional language
functionality or implementation authority.

## Difficulty allocation

| Functionality or delivery area | Unit points |
| --- | ---: |
| Contract and corpus preparation, C1–C4 | 8 |
| Declaration syntax, D1–D8 | 24 |
| Contexts and publication, H1–H6 | 18 |
| Syntax service and host, S1–S5 | 16 |
| Derives, R1–R6 | 17 |
| Repetition and generators, G1–G7 | 24 |
| Connected verification and delivery, V1–V8 | 23 |
| **Revised draft prediction** | **130** |

| Prediction or remaining scope | Points | Meaning |
| --- | ---: | --- |
| First declaration/derive prediction | 65 | Historical allocation retained in the companion. |
| Added generator and deriving scope | 30 | Historical increment; 65 + 30 = 95. |
| First local full-chain prediction | 126 | Historical 43-unit breakdown before this calibration; G7 was 2. |
| G7 coverage correction | 2 | Selected authoring/admission work made explicit; G7 is now 4. |
| Intermediate revised prediction | 128 | G7 correction before separating corpus source preparation from independent review. |
| C4 corpus preparation | 2 | New bounded pre-implementation producer for complete I17 source inputs. |
| Current total-scope prediction | 130 | Sum of the 44 unit estimates and the seven functionality totals above. |
| Recorded C1/C2 planning scope | 4 | Two recorded planning decisions; no product implementation or connected gate is credited. |
| Remaining corpus preparation and contract review, C4/C3 | 4 | Complete I17 source transcription and independent boundary/corpus review remain open. |
| Remaining product and delivery units | 122 | D, H, S, R, G and V; implementation authority and connected evidence remain required. |
| **Current remaining-work forecast** | **126** | **4 + 122**, excluding Main integration and separately owned downstream repairs. |

The earlier totals are predictions for their recorded scopes, not performance
measures. This revision includes the syntax-only restriction and the ordinary
fragment-returning generator contract, without estimating discarded semantic
machinery. C1/C2's recorded decisions do not close C3, accept CP-0034, make I17
complete, or pass any product gate. Record observed difficulty separately after
delivery. If a downstream gap blocks a required case, name that dependency and
its separate estimate before forecasting the whole delivery again; 126 is not
an estimate for unbounded downstream repair.

## Dependency and parallelism overview

```mermaid
flowchart LR
    C1 & C2 --> C4
    C1 & C2 & C4 --> C3
    C3 --> D1 & S1
    D1 --> D2 & D7
    D1 & D7 --> D6
    D1 & D6 --> R1
    D2 --> D3
    D3 --> D4 & D5 & G1
    D2 & D7 --> H1
    H1 --> H2 & H5
    H1 & D4 --> H3
    H2 & H3 --> H4
    H4 --> H6
    D3 & D4 & D6 & D7 & H1 & H2 --> D8
    S1 & D4 & D5 --> S2
    S1 & D7 --> S3
    S3 & H1 --> S4
    S2 & S4 --> S5
    R1 & S2 --> R2
    R2 & H1 & D7 --> R3
    R3 & H2 --> R4
    R3 & S4 --> R5
    R4 & R5 & H5 --> R6
    G1 & D6 --> G2
    G2 & S1 --> G3
    G3 & S4 --> G7
    G7 --> G4
    G4 --> G5
    G5 --> G6
    D8 & D4 & D5 & H3 --> V1
    D8 & R5 & G6 & G7 & H5 --> V2
    V1 & V2 & R6 & G6 & G7 & S5 & H5 & H6 --> V3
    V3 --> V4
    V3 & V4 --> V5 & V6
    V5 & V6 --> V7
    V7 --> V8
```

The tables describe the reason for each edge; the diagram shows every named
unit dependency. All implementation units also require the acceptance, task
and base conditions stated after C3. D4 and D5, S1 and D1, and the R1, H5 and
generator-preparation paths can proceed in
parallel once their actual inputs and owners are agreed. G7 establishes the
state-only fragment-producing call consumed by G4 and G5; G6 adds nesting.

Design, planning, development, QA and review may overlap on different units.
Agree on shared interface contracts first. For simultaneous edits, one owner
controls each shared grammar, projection, syntax representation and host file;
other units deliver against the agreed interface in separate files or wait for
the owning change to land. Separate worktrees alone do not resolve overlapping
diffs. Schedule the shared product integration branch and heavy build/cache
access. A focused check on an agreed producer interface can
unblock a consumer; the producer's connected acceptance remains pending.
The integration owner brings the paths together and runs the first coherent
driver path at D8, then the full path at V3. QA and review begin on each pinned
unit as it becomes available; V5/V6 are the integrated audit, not the first
time either role participates.

The candidate issue/PR hierarchy and exact owner assignments remain for a
later planning decision. The point baseline above is the revised local
forecast; C3 still requires independent review before implementation. No
GitHub issues are created by this document.
