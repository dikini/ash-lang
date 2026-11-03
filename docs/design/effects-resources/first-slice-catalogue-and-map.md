# Effects and Resources: Current Rule Catalogue and Implementation Map

This working record belongs to [DN-0061](../DN-0061-effects-and-resources-first-slice.md).
It catalogues the current rule families and the implementation paths that
touch the selected slice. The [specification](../../../spec/README.md) states
intended current Ash. Code and tests locate implementations and provide
bounded evidence; they do not establish a semantic rule or a general
correspondence proof.

The catalogue follows the rules, not one example. Function and data typing,
Store, regions, registrations, native and network resources remain outside the
slice, but their facts and obligations can cross its boundaries. Effect and
resource rules must account for those inputs without assuming an opaque value
is independent or an opaque computation is pure. The catalogue does not yet
propose replacement judgments or decide the disposition of individual checks.
The companion [facts and obligations catalogue](first-slice-facts-and-obligations.md)
indexes the facts each rule establishes, consumes, preserves or discharges and
distinguishes source expression, inference and Core representation.

The present design question is which facts can be established by the selected
language rules, which premises each rule requires and what its conclusion
expresses. Declarations, including functions, modules, interfaces, effects and
resources, expose in the type language the facts and requirements needed by
their users. Users check compositions against the applicable judgments while
treating hidden implementation details as opaque. Checking an implementation
against its declaration is a separate obligation; the declaration alone does
not prove it. The map of later compiler stages below records current behavior
and reuse pressure. It does not make linking or whole-program optimization part
of the current semantic design.

[CP-0031](../../proposals/CP-0031-remove-legacy-integer-cell.md) proposes
removing the legacy integer-cell facility as part of this work. R1 and its
implementation paths below are the current **before** state, not a requirement
to retain that facility. The intended after state uses R2 instantiated with
`Int`; programs and their tests and documentation migrate to that API. Shared
analysis or runtime code remains where generic cells or other consumers need
it. Per-consumer dispositions and the semantic transition still require the
evidence stated by the proposal.

## Rule catalogue

Each entry names its principal inputs and output or obligation. A listed
operational rule specifies intended behavior, not evidence that the Rust
implementation implements it for every input. `E`, `R` and `T` below are
effect, owner and value-type parameters; they are not proposed new Ash syntax.

### Effect, handler and control rules

| ID | Current rule and inputs | Output, obligation and operational counterpart |
| --- | --- | --- |
| E1 | [Effect declaration](../../../spec/static-semantics.md#effects): defining identity, ordered parameters and operations, each operation's pure outer `P -> Q` signature. | Stable effect and operation identities and checked parameter kinds/signatures; equal spelling does not identify different declarations. |
| E2 | [Instance and row formation](../../../spec/static-semantics.md#computation-types-and-effect-rows): effect identity and complete arguments, kind environment, closed members or an open tail and its lacks facts. | A well-formed exact instance, row and computation type. Written duplicate members reject; an instance is identified by the effect and all instantiated arguments. |
| E3 | [Row equality, substitution and operations](../../../spec/static-semantics.md#computation-types-and-effect-rows): known instances, row tails, substitutions and lacks facts. | Kind-preserving substitution and unification, partial union, weakening and exact removal. Union cannot invent a lacks fact; an unconstrained tail cannot be searched as if it named a specific instance. Preserve constraints through specialization. |
| E4 | `T-Perform` in [effects](../../../spec/static-semantics.md#effects): exact effect operation, substituted input/output types and checked operand with its effects. | The request has operation result type `Q` and the operand row union the exact requested instance. `E-Perform-Operand` evaluates the operand first; runtime selection follows. Typing the request does not select a handler. |
| E5 | `T-Handle`: handled body judgment with the target explicitly present in its row, exact target, complete irrefutable operation clauses, each clause's result and effects. | Removes the target from the body row and checks a common answer type and least output row. Other effects and effects introduced by clauses remain. An absent target or an ambiguous open tail cannot establish the removal. `E-Handle-Enter` installs the boundary; normal return removes it and passes the body value outward. |
| E6 | Handler selection: the evaluated operand and its saved lexical instantiation, active ordered control and exact instantiated effect. | Runtime searches for the nearest accepting source, cell or native boundary. The displayed `E-Request-Select` rule is the source-handler branch: it moves the selected handler and intervening frames into the clause's live owned capture; the clause runs outside that handler. Cell and native interpretation use their own steps. |
| E7 | `T-Resume`: active ordinary clause capability with operation result `Q`, handler answer `A` and output row, plus an operand checked as `Q`. | Produces `A` with the handler output row and consumes the capability. `E-Resume-Operand` evaluates the operand first; `E-Resume-Restore` consumes the owner and reinstalls captured control in order, then the clause suffix continues. |
| E8 | `T-Discard`: an available ordinary owner; recursively owned capture closure; outside and running completion obligations; actual closing actions and compatible interpreter context. | Consumes the owner, yields `Unit` and the least residual close row. `E-Discard` closes owned abandoned control and retains the clause continuation; it does not execute abandoned suffixes. Unproved safety is `effect.discard-unsafe`; discard is not necessarily pure. |
| E9 | Structural continuation use: incoming `available`/`consumed` state, expression sequencing and branch structure. | Each normally completing clause path consumes once; matches join equal outgoing states. Function bodies, recursive members, supplied methods and nested clauses are barriers to an enclosing capability. Zero use, duplicate use and escape reject; divergence does not imply completion. |
| E10 | Capture and handler composition: exact request identities, caller and callee control, live clause owners, possible paths and applicable substitutions. | The selected capture owns recursively contained live captures; outside owners must remain completable. A resumed segment restores crossed boundaries without replaying its prefix. Generic parameters may later coincide, so selection cannot assume distinct instances merely from different parameters. Unknown relevant callees or open rows can make discard unprovable; uncertainty alone does not reject resource-free resume-only code. |

The operational counterparts for E5–E10 are specified together under
[effect handlers and completion](../../../spec/dynamic-semantics.md#effect-handlers-and-completion).
Private Store clauses and `retain` are outside the slice. Their facts, when
encountered, are boundary obligations rather than ordinary-discard permissions.
Discard preparation failure precedes owner consumption. Once closing actions
start, a later internal failure does not roll back earlier effects or guarantee
remaining actions. Closing does not restore captured source handlers or invoke
abandoned publication callbacks.

### Resource and cleanup rules

| ID | Current rule and inputs | Output, obligation and operational counterpart |
| --- | --- | --- |
| R1 | [Legacy cell scope](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies): preceding-scope `Int` initializer, fresh rigid `R`, handle, sealed `Provider<R>` and body. | Body checks with exact `Ops<R>`; result has the body type and the outward row unions initializer effects with body effects after exact `Ops<R>` removal. Result, outward row and evidence must not expose the closing identity. |
| R2 | [Generic cell scope](../../../spec/static-semantics.md#generic-cell-foundation): preceding-scope initializer of a fixed monomorphic payload `T`, fresh `R` and exact `Cell<R,T>`, `Provider<R,T>` and `Ops<R,T>`. | The scope retains the body result and discharges only its exact cell effect. Builtin read/write are ordinary applications under the sealed provider; reading does not generalize a result. Payload `T` may itself be an abstract type from the surrounding context. |
| R3 | Resource acquisition and access: initializer result, authenticated cell operation, lexical instantiation and handle. | [Cell execution](../../../spec/dynamic-semantics.md#scoped-cell-execution) initializes before acquisition, creates a fresh runtime activation, and reads or replaces the selected root. Handles provide duplicable non-owning access; copying one does not duplicate its owner. A nearer exact source handler intercepts the operation; an intercepted write is not itself a builtin replacement. |
| R4 | Resource dependency and escape: actual value dependencies, owner being closed or crossed, operation payload or scope result, and any enclosing owners. | Reject a result or outward payload dependent on the owner it crosses; an independent value may cross. Dependencies can be hidden in closures, selected evidence or operation metadata and must survive aliases, imports and instantiation. A request may cross an unrelated inner owner while remaining inside its own. |
| R5 | Generic-cell contents: target activation, initializer or each actual replacement, payload dependencies and owner-enclosure relation. | Retained resource owners must strictly enclose the target; self-retention, cycles and younger or incomparable retention reject at that operation. Current contents, access handles and previous read snapshots are distinct; later replacement does not change an earlier snapshot. A later clearing write cannot repair a previously invalid retention. |
| R6 | Resource capture and completion: cell activation and current contents, captured segment, normal return or checked owned discard. | Capture and resume move the same owner and preserve its activation and contents. Normal completion releases the scope; admitted discard closes owned cells in structural order without skipping outside completion. Runtime capacity remains charged while the captured cell is live. |
| R7 | [Cleanup scope](../../../spec/static-semantics.md#scoped-cleanup-actions): action evaluated in preceding scope with `Unit -> Unit` and its latent row; body result and effects. | The scope retains the body type and includes initializer, body and action effects. One invocation obligation is acquired independently of callable copies. A body-local handler does not automatically handle the later action. |
| R8 | Cleanup completion: armed action, saved body result or owned close and the surrounding interpretation context. | [Cleanup execution](../../../spec/dynamic-semantics.md#scoped-cleanup-actions) initializes, acquires, starts at most once and finishes the action, preserving the saved normal result. Capture/resume preserve its phase. A running action or unfinished close must not be abandoned; nested owners close inner before outer. |
| R9 | Cleanup interpretation: each actual transitive action request, its structural close position, lexical instantiation and candidate interpreters. | The nearest relevant interpreter must remain compatible. If a removed source or generated handler is the required candidate, reject with `effect.cleanup-context`; an outer same-instance handler cannot substitute for it. Action-local handlers, surviving outer handlers and live unshadowed builtin cells have their specified roles. |
| R10 | Closing effects and dependencies: owned actions, their actual call requirements, retained builtin interpreters, remaining source context and saved values. | Infer the least residual effects of close and preserve dependencies of the saved body result, action captures and operation payloads. `effect.discard-unsafe` or `type.resource-escape` applies where the relevant proof fails. |

Cell ownership and backing storage are distinct. Even an `Int` type alone does
not prove independence from a separate allocation region; preserve such
[construction dependencies](../../../spec/static-semantics.md#lexical-regions-and-construction-dependencies)
as outside facts where they cross the slice. Current static rules also make
resource admission conservative when relevant unknown behavior prevents a
dependency or abandonment proof; that is not proof that the behavior is unsafe.

For R4–R6, the cell's own trusted interpreter is an admitted recipient. Every
possible generic-cell target and payload must satisfy retention; recursive
executions can create different activations at one lexical site. Enclosure is
determined by actual acquisition, not changed by wrapping a restored frame in a
younger scope. An intercepted read carries its actual reply's dependencies;
writes in clauses and resumed computation update the cell in control order.
A read snapshot can itself carry dependencies and only an independent snapshot
can escape its owner. Ordinary type, row and structural checks precede resource
admission; an unproved escape reports `type.resource-escape` and does not
publish a module, helper summary or linked-Core permission.

For R3, exact instantiated `R,T`, the actual handle and operation must match.
Fallible reply, copying and trace preparation precede a builtin replacement;
failed preflight leaves the old root intact while earlier operand effects
remain. A failure disposing a replaced value can be terminal after mutation.
For R8–R10, an action-local discard is permitted when the action, close and
outside owners still complete. Cleanup summaries retain action effects and
interpreter requirements even when a captured handler discharged an effect
from the body's outward row. An unknown necessary interpreter rejects the
relevant abandonment, not every use of the callback.

## Operational observations and failure

Successful [observation](../../../spec/dynamic-semantics.md#observation)
retains no live resource scope, cleanup obligation or captured continuation.
The current specification reports malformed control, invalid locations and
runtime capacity exhaustion as internal failures. Cell and cleanup preparation
can fail before publication; terminal internal failure does not guarantee source
cleanup and does not undo effects already performed. Declared allocation refusal
has its separately specified effect/discard behavior. See
[allocation and failure](../../../spec/dynamic-semantics.md#region-construction-and-close-steps)
and [cleanup execution](../../../spec/dynamic-semantics.md#scoped-cleanup-actions).

The intended no-error guarantee in DN-0060 is a target, not an established
property of the current implementation. For each failure, determine whether a
well-typed program must rule it out, which external event or resource premise
it reflects, and what Ash must do in response. The existing specification does
not by itself classify every such case for that guarantee. Termination is a
separate property.

## Source-to-execution implementation map

The links below identify entry points for following the actual code. Line
anchors are navigation aids in this working tree. A stage may perform checks
for more than one catalogue entry, and an entry may have more than one
producer or consumer.

| ID | Stage and current implementation | Inputs and outputs; downstream consumer |
| --- | --- | --- |
| M1 | [Parser](../../../src/parser/expression.rs), [resolution](../../../src/resolve.rs#L12573), [resource resolution](../../../src/resolve.rs#L10896) | Source syntax and dependency exports become resolved effect/operation, resource, handler and owner identities. Resolution attaches each ordinary clause's resume identity and enforces the appropriate lexical scope. Source elaboration consumes the resolved tree. |
| M2 | [Row representation](../../../src/types.rs), [row union and qualification](../../../src/elaborate.rs#L13845), [row unification](../../../src/elaborate.rs#L10083) | Kinds, exact identities, arguments, rows and lacks facts become checked or inferred rows and substitutions, or a diagnostic. E1–E3 feed request, handler, resource and cleanup typing; linked Core independently checks the represented relationships. |
| M3 | [Request and resume elaboration](../../../src/elaborate.rs#L13966), [handler and clauses](../../../src/elaborate.rs#L14550), [structural usage](../../../src/elaborate.rs#L30759) | Resolved operations, operand/body/clause judgments, patterns and active owners produce typed Request, Handler, Resume and Discard nodes and rows. Structural usage checks E9; E8 and E10 also require capture analysis, not merely this usage check. |
| M4 | [Resource elaboration](../../../src/elaborate.rs#L14218), [resource scheduling](../../../src/elaborate.rs#L16632), [cleanup scheduling](../../../src/elaborate.rs#L16963), [deferred escape](../../../src/elaborate.rs#L13706) | Resolved acquisition, initializer/body types, provider/operation facts, actions and row contexts produce typed resource/cleanup nodes and deferred escape checks. Later solved type and row facts are revisited before publication. R4–R10 also use the shared analysis below. |
| M5 | [Module completion](../../../src/elaborate.rs#L5791), [cleanup-row solver](../../../src/elaborate/cleanup_rows.rs#L392), [capture entry points](../../../src/core/capture.rs#L3174) | Completed Core builder roots, imported global and method summaries, applicable method routes/adapters and a work budget feed `infer_cleanup_rows` and `check_builder`. The physical module path supplies empty routes/adapters after selections are materialized; the nonphysical path collects them explicitly. The former query supplies close requirements to the row fixed point; the latter checks capture/resource obligations and returns callable summaries. The same graph machinery is used, but the queries and premises differ. |
| M6 | [Checked module publication](../../../src/elaborate.rs#L24631), [linking](../../../spec/elaboration.md#module-linking-and-entry-generation), [link implementation](../../../src/elaborate.rs#L25243) | A successfully checked module retains its lowered fragment, schemes, selected evidence, metadata and callable capture summaries. Imports use checked summaries and identities; linking relocates and assembles fragments without repeating defining source-body checks or selecting the same evidence again. A checked fragment is not yet independently validated linked Core. |
| M7 | [Effect Core representation](../../../src/core/effect.rs#L553), [specified lowering](../../../spec/elaboration.md#effect-core-lowering) | Typed nodes retain exact rows, origins, effect/operation identities, handler and resume owners, resource acquisition and cleanup relationships. These are inputs to linked validation and execution; they are not by themselves a general reusable proof certificate. |
| M8 | [Linked Core validator](../../../src/core/validate.rs#L13780), [handler validation](../../../src/core/validate.rs#L16777), [resource validation](../../../src/core/validate.rs#L14413), [cleanup validation](../../../src/core/validate.rs#L13251) | Combined registries, source provenance and actual linked nodes are checked for kinds, types, rows, identities, scopes, clause coverage, owner use, resource and cleanup structure. After ordinary checks, when generic computations, discard or a resource/control owner requires it, `check_nodes` reconstructs capture, dependency and completion relationships from linked nodes with empty imported-summary inputs. It skips this reconstruction when none is present. `check_nodes_with_release` adds Store release checking when required. |
| M9 | [Evaluator dispatch](../../../src/eval/machine.rs#L5711), [request selection/capture](../../../src/eval/machine.rs#L4440), [resume](../../../src/eval/machine.rs#L5019), [discard](../../../src/eval/machine.rs#L5254), [cell](../../../src/eval/machine.rs#L4210), [cleanup](../../../src/eval/machine.rs#L3719) | The evaluator receives validated Effect Core and runtime environments, owners and continuation frames. It performs actual selection, ownership transfer, restoration, closing and resource operations; it does not receive the compiler's capture summaries. Runtime checks and preparation failures still have their specified roles. |

Source-to-Core preservation and execution correspondence across M1–M9 are
requirements to establish, not results proved by this map. In particular,
link relocation, specialization or a changed target can introduce new subjects
or composition obligations. They must not automatically be classified as the
same unchanged fact.

For example, a checked helper's summary can record that it may request an
effect. A caller invokes the helper inside a resource scope and handles that
request outside the scope. Checking this composition needs a new conclusion:
what the selected handler captures, and whether its continuation can be resumed
or discarded while respecting the resource owner. The desired composition uses
the established helper fact and the caller's context; it does not rediscover
the helper's unchanged behavior. Today, module checking uses retained summaries,
while linked Core validation can reconstruct relationships from the assembled
nodes. The map identifies those passes, but does not yet determine which
individual facts the second pass repeats and which are new composition or
changed-subject obligations.

### Rule-to-implementation cross-reference

This index identifies where to start following each catalogue family. The
paths are connected by M1–M9; an implementation entry is not a replacement
for the rule or a claim of complete correspondence.

| Rules | Source-side producer or check | Core or analysis consumer | Runtime or other boundary |
| --- | --- | --- | --- |
| E1–E3 | [Resolution](../../../src/resolve.rs), [row unification](../../../src/elaborate.rs#L10083) and [row union](../../../src/elaborate.rs#L13845) | [Effect registry](../../../src/core/validate.rs#L8054) and [instance/row validation](../../../src/core/validate.rs#L14042) | [Lexical instantiation](../../../src/eval/instantiation.rs) supplies exact runtime identity arguments. |
| E4 | [`schedule_perform` and `finish_perform`](../../../src/elaborate.rs#L13966) | [Effect-node validation](../../../src/core/validate.rs#L15211); request paths in A2 and A4 | [Request dispatch](../../../src/eval/machine.rs#L4440) and cell/native interpretation. |
| E5 | [`finish_handler` and clause checking](../../../src/elaborate.rs#L14550) | [Handler validation](../../../src/core/validate.rs#L16777), [least handler output](../../../src/core/validate.rs#L16414), A4 | [Handler entry and exit](../../../spec/dynamic-semantics.md#effect-handlers-and-completion). |
| E6 | [Clause resolution](../../../src/resolve.rs#L12573) and A4 | [Request boundary analysis](../../../src/core/capture/control.rs#L5966) and [interpreter analysis](../../../src/core/capture/control.rs#L6212) | [Runtime request and capture](../../../src/eval/machine.rs#L4440). |
| E7–E9 | [`synthesize_resume`](../../../src/elaborate.rs#L14147), [`synthesize_discard`](../../../src/elaborate.rs#L14049), A1 | [Core scope analysis](../../../src/core/validate.rs#L12552), [resume contract](../../../src/core/validate.rs#L17059), A4–A6 | [Resume](../../../src/eval/machine.rs#L5019) and [discard](../../../src/eval/machine.rs#L5254). |
| E10 | A2 and A4, including imported callable summaries | [Request continuations](../../../src/core/capture/control.rs#L6156), [clause capture](../../../src/core/capture/control.rs#L6752), [resumed capture](../../../src/core/capture/control.rs#L7458) | [Owned close](../../../spec/dynamic-semantics.md#effect-handlers-and-completion); outside frames retain their own obligations. |
| R1–R3 | [Resource resolution](../../../src/resolve.rs#L10896), [resource body and result](../../../src/elaborate.rs#L14218) | [Resource node validation](../../../src/core/validate.rs#L14413), A3 | [Acquisition](../../../src/eval/machine.rs#L4210), [legacy cell](../../../src/eval/machine.rs#L4836), [generic cell](../../../src/eval/machine.rs#L4902). |
| R4–R6 | [Deferred resource escape](../../../src/elaborate.rs#L13706), A2–A4 | [Value resource checks](../../../src/core/capture/value.rs#L6184), [cell retention](../../../src/core/capture/control.rs#L6644), A6 | [Cell capture and release](../../../spec/dynamic-semantics.md#scoped-cell-execution); allocation dependencies cross an outside boundary. |
| R7–R8 | [Cleanup scheduling and action](../../../src/elaborate.rs#L16963), A4–A5 | [Cleanup owner validation](../../../src/core/validate.rs#L13251), [close-segment analysis](../../../src/core/capture/control.rs#L7032) | [Cleanup acquisition](../../../src/eval/machine.rs#L3719) and [cleanup phases](../../../spec/dynamic-semantics.md#scoped-cleanup-actions). |
| R9–R10 | A3–A5, including actual selected callback and close requirements | [Removed-interpreter check](../../../src/core/capture/control.rs#L6237), [cleanup-row validation](../../../src/core/capture.rs#L3871), A6 | [Discard and owned closing](../../../src/eval/machine.rs#L5254); excluded interpreters enter through boundary contracts. |

## Shared analysis register: current before state

This is one register for analyses shared across the slice, not a copy for each
construct. Inputs and outputs below describe the currently identified paths;
individual fact identity, provenance and every consumer still need tracing at
the granularity necessary to choose a replacement.

| ID | Analysis and producer | Inputs and result | Current consumers and reuse question |
| --- | --- | --- | --- |
| A1 | Structural continuation usage, [source](../../../src/elaborate.rs#L30759) and [Core scope traversal](../../../src/core/validate.rs#L11901) | Clause body, owner identity and available/consumed state; accepted use state or missing, duplicate or captured-owner diagnostic. | E7–E9 source admission and linked validation. Core separately checks retained consumed markers. Determine which established usage fact is preserved and which new Core structure requires a separate check. |
| A2 | Callable/value and control graph, [builder and shared engine](../../../src/core/capture.rs#L3174) | Typed nodes and roots, imported summaries, operation accessor, applicable method routes/adapters and budget; finite value/control graphs and per-global `CaptureValueSummary`, or failure. A missing/default summary is unknown, not proof of independence. | Module publication and later imports; inputs for resource, discard and cleanup queries. With no globals, discard, retained control or resource queries, the graph builder can skip its work. Determine what the graph establishes versus what remains an assumption or a context-specific query. |
| A3 | Resource dependencies, [value queries](../../../src/core/capture/value.rs#L5929) and [control/retention queries](../../../src/core/capture/control.rs#L6427) | Actual value/callable paths, owner activation and containment, cell contents and snapshots, request payloads and possible targets; dependency, retention or escape result. | R3–R6 and R10, including resource checks when no discard occurs. Shared with region, registration, Store and other consumers; do not retire the engine merely because one cell path changes. |
| A4 | Request, handler and completion analysis, [control discovery](../../../src/core/capture/control.rs#L3297) and [request boundaries](../../../src/core/capture/control.rs#L5768) | Possible requests, exact instances and instantiations, active contexts, captures and live completion owners; admission or causal unsafe-discard result. | E6–E10, resource and cleanup completion, including imported calls. A row alone does not currently carry all these relationships. |
| A5 | Cleanup requirements and row equations, [inference](../../../src/core/capture.rs#L3243), [solver](../../../src/elaborate/cleanup_rows.rs#L392) and [strict row checking](../../../src/core/capture.rs#L3871) | Actual owned actions, close positions, interpreters, rows and pending equations; per-discard/action requirements and least finite row solution, followed by strict safety and row agreement. | E8 and R7–R10 in source elaboration and linked validation. Inference and strict checking both use the graph, but same input alone does not prove identical work; compare per subject and context. |
| A6 | Linked-Core reconstruction, [validator call](../../../src/core/validate.rs#L13850) | When its generic-computation, discard or resource/control-owner gate requires it, assembled linked nodes and authenticated registries after ordinary validation, without imported capture summaries; accepted control/resource/cleanup relations or validation failure. | Executable admission and transformed Core validation when that gate applies. It shares the engine with A2–A5 but has a new assembled subject and can rederive overlapping facts. Account for each unchanged fact separately from new composition, changed targets and structural authentication. |
| A7 | Module summary retention, [publication](../../../src/elaborate.rs#L5791) and [summary representation](../../../src/core/capture.rs#L75) | Successfully checked local roots, imported summaries and selected method information; immutable callable graph and selected abstract value for checked globals/methods. | Dependency modules and call composition; [metadata closure authentication](../../../src/resolved.rs#L11602), imported declaration selection and [dialect selection](../../../src/elaborate.rs#L24679) also use summary information. This is existing reuse, not a general proof certificate for all later linked-Core properties. |
| A8 | Shared capture helpers, [region closure preparation](../../../src/core/capture.rs#L1183) and [method selection](../../../src/core/capture.rs#L746) | Closure expressions, selected evidence and lexical captures; physical capture layouts or method-selection targets. | Region elaboration, selected-evidence routing and [Core closure validation](../../../src/core/validate.rs#L15450). These outside-slice consumers also prevent wholesale retirement of shared capture machinery. |

When a source cleanup row needs inference, `solve_cleanup_rows` can first ask
the capture engine for requirements, solve monotone union and exact-removal
equations, then invoke the strict capture check on the builder. When strict
checking encounters potentially nonempty cleanup rows it can collect row
observations during control discovery and check agreement. This is a concrete
place to examine repeated work; it does not by itself prove that the two
queries establish the same fact under the same premises.

[AD-0007](../../decisions/AD-0007-typed-core-dialects.md) requires an
independent validator for each retained Core dialect and validation of new
linked or transformed Core. It also says imported checked modules do not repeat
their source-body proofs, and unchanged validated Core preserves its proof.
The replacement design must reconcile that assurance with DN-0060's no-repeat
requirement; this record does not authorize dropping either requirement.

## Boundary facts to trace

| Boundary | Facts needed by the slice | Current source or status |
| --- | --- | --- |
| Opaque value or type | Type and kind; actual stored-resource and backing dependencies; premises and owner scope. A type variable alone does not imply independence. | Ordinary data checking and the shared dependency analysis; the exact reusable judgment is not yet defined. |
| Opaque function or call frame | Function/argument/result types and row; possible requests, dependencies, context and completion relationships needed by the in-scope rule. | Checked scheme and retained callable summary where available. Unknown behavior remains unknown, and relevant unproved discard or escape is conservatively rejected. |
| Effect and provider | Defining identity, parameter kinds, operation signatures, exact instantiation, sealed cell provider and method selection. | Checked declarations and dependency summaries; `read` and `write` use ordinary application and evidence. Do not invent direct primitive source calls. |
| Enclosing control | Existing handlers, clause and resource owners, selected interpretation, current and outside completion obligations. | Current capture analysis and dynamic control. A prospective type-system judgment and its preservation across calls are open design work. |
| Allocation, native and excluded scopes | Selected allocation context, resource backing/ownership facts, external contracts and any completion obligation crossing the slice. | Established evidence or an explicit outstanding obligation/assumption. Root allocation remains present even if explicit regions are excluded. |
| Module, linking and transformation | Subject identity, checked summary, lexical type/row instantiation, provenance and assumptions; changed subjects or dependencies. | Module summaries, relocated Core and independent validation. The precise interface for reusing individual behavioral facts remains to be designed. |

## Evidence, discrepancies and next work

The following are representative evidence, not an exhaustive test inventory
or a proof of correspondence:

- [Effect typing](../../../tests/effect_typing.rs) covers exact handlers,
  completion usage, known and unknown callees, and nested capture cases;
  [effect modules](../../../tests/effect_modules.rs) covers imported summaries
  and identities; [effect Core](../../../tests/effect_core.rs) challenges
  owner, type and row validation.
- [Resource typing](../../../tests/resource_scope_typing.rs) and
  [resource execution](../../../tests/resource_scope_runtime.rs) cover cell
  escape, captured scopes, snapshots and ownership interactions.
- [Cleanup typing](../../../tests/cleanup_typing.rs) and
  [cleanup interactions](../../../tests/cleanup_interactions.rs) cover close
  effects, running completion and interpretation boundaries. Core validator
  tests include [same-typed callback substitution](../../../src/core/validate.rs#L20205)
  and forged or transformed relationships.
- The [one-shot formalization](../direct-effects/one-shot/README.md) establishes
  results for its stated annotated model and premises. It is not a complete
  theorem for all admitted Ash or a compiler-to-runtime correspondence proof.

One specification wording conflict is already visible: the
[Core-validation list](../../../spec/elaboration.md#validation-boundary) says
that each resource initializer has `Int` type, while the same specification's
[generic-cell lowering](../../../spec/elaboration.md#surface-erasure) and
[static rules](../../../spec/static-semantics.md#generic-cell-foundation)
specify a fixed payload `T`. The [validator](../../../src/core/validate.rs#L14413)
selects the generic payload type and uses `Int` for the legacy case. This is a
documentation consistency issue to resolve through the appropriate
specification workflow, not evidence that generic-cell validation is wrong.

The resource-scope wording says to remove the exact cell effect but does not
explicitly state the known-absent and ambiguous-open-tail cases. Current
[source](../../../src/elaborate.rs#L14309) and
[Core](../../../src/core/validate.rs#L14133) preserve a row when the target is
known absent and reject an ambiguous open tail; they remove the target when it
is present. Clarify the intended resource rule in the specification before
using it as a complete replacement rule. Ordinary handlers separately require
their target to be present.

The [verification audit](first-slice-verification-audit.md) follows individual
checks, their results and the candidate judgments needed to replace them. It
also distinguishes checks that answer different questions using shared
machinery.

The catalogue identifies rule families, main implementation entry points,
shared analyses and known consumers. It does not yet establish a complete
per-fact producer/consumer ledger, prove specification/implementation
correspondence, decide new type-system rules or show which individual repeated
queries can be removed. The next design step is to refine A1–A7 per subject and
premises, including opaque boundary obligations, and record the before/after
disposition for each affected consumer before retiring any check.
