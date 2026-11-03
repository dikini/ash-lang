# Effects and Resources: Facts and Obligations

This record belongs to [DN-0061](../DN-0061-effects-and-resources-first-slice.md).
It identifies the facts and obligations behind the rules in the
[current rule catalogue and implementation map](first-slice-catalogue-and-map.md).
It identifies needed forms and judgments without choosing source syntax or a
compiler implementation.
The [specification](../../../spec/README.md) is the authority for current Ash;
this record identifies what that specification and the existing checks require.
The separate [judgment and composition requirements](first-slice-judgment-requirements.md)
describe the proposed next design boundary.

The question for each entry is: **what must be known, where is it established,
which rule consumes it, and what must survive composition?** A declaration or
subexpression is opaque to its users: they should use its established judgment,
not derive the same fact again from its implementation. Any unproved premise
remains an explicit obligation, and dependent conclusions remain conditional.

The entries describe facts about identified subjects and their premises. A
resource-dependency fact, for example, concerns a particular value and owner;
it does not follow solely from the value's payload type. “Absent” or “unknown”
below refers to the indicated current representation, not a proof that the fact
cannot be expressed by a future type system.

## Surface and Core

For this work, typed Core must carry all types resulting from checking and
inference, including the type-system facts needed for the selected rules.
Surface declarations may state information explicitly or leave it to inference;
the language may increase what it infers. Inference must establish a fact under
the applicable premises, not assume it, and later users must reuse the result.
The complete inferred types must be present in typed Core. How additional
justification is represented as propositions or other checked evidence remains
open; that choice does not permit inferred type information to be omitted.

Successful type checking of Core must certify the checked program or fragment
under its stated premises. Later consumers reuse that certification without
running verification over that verified program or fragment again. A
composition is a new fragment: check the composition using the certifications
of its previously verified constituents, without verifying those constituents
again. The certificate's representation and storage are not selected here.

Current Ash already retains a value type, exact computation row and origin on
each [Effect Core node](../../../spec/elaboration.md#effect-core-lowering),
plus structural effect, owner and resource metadata. Source schemes can carry
types, effects and interface requirements, with some inference subject to
[rank-1 restrictions](../../../spec/static-semantics.md#inference-and-rank-1-restrictions).
Some control and dependency information is currently computed and carried in
private callable summaries or reconstructed by analyses; it is not yet a
general source-expressible behavioral type. A Core node's existing type or a
private summary is not by itself evidence that every target fact below is
already represented in the desired type system. The certification and reuse
boundary above is the target. Current linked Core validation conditionally
reconstructs capture, resource and completion relationships from assembled
Core rather than using source summaries as permissions; see the
[implementation map](first-slice-catalogue-and-map.md#source-to-execution-implementation-map).

In the tables:

- **Surface** identifies what can currently be written or inferred in source
  types, declarations or checking. It does not require explicit annotation.
- **Current checking** identifies structural judgments or analyses that
  establish additional facts; a private summary can retain some results for
  later source checking. It is not an arbitrary user-written proof.
- **Core** identifies retained types, rows or structural data. It is not a
  claim that the current type representation already expresses the complete
  behavior. The detailed consumers and code paths are in the linked map.

The requirements below are about static composition unless explicitly marked
as operational or environmental. Runtime selection or a test observation is
not, by itself, a reusable type-system proof. System-level soundness and
correctness are separate from checking an individual program.

## Effects and computation facts

The current source rules for these facts are
[effect-row formation](../../../spec/static-semantics.md#computation-types-and-effect-rows)
and [effects](../../../spec/static-semantics.md#effects). E1–E10 refer to the
rule IDs in the companion catalogue.

| ID | Subject, fact and establishing premises | Consumer, preservation or discharge | Current representation and boundary need |
| --- | --- | --- | --- |
| F01 | An effect declaration has an authenticated defining identity, ordered parameter kinds and operations with input/output types. Forming an instance requires all arguments with matching kinds. | Requests and handlers use that exact operation and substituted signature; import and instantiation preserve identity and argument positions. E1–E2, E4–E6. | **Surface:** declarations and parameterized instances. **Current checking/Core:** resolved identities and authenticated registry facts. A user needs the declaration's contract, not its implementation. |
| F02 | A computation has a value result type and effect requirements represented by a row of exact effect instances, possibly with a tail. The row is unordered and does not itself describe operation order or multiplicity. | Calls, operands, clauses and scopes compose required rows; a handler can remove only its exact target. Substitution preserves instance arguments and the meaning of the remaining row. E2–E5, R1–R2, R7. | **Surface:** computation types, explicit or inferred rows and permitted polymorphism. **Core:** value types and exact rows. A row is not a complete description of captured control, stored dependencies or completion. |
| F03 | A row member is present, absent under a known lacks condition, or not established. Exact instance equality requires the same identity and equal instantiated arguments; different type variables may later coincide. | Union, weakening and exact removal require the applicable equality and absence facts. A handler cannot claim to remove an instance hidden in an unconstrained tail. Substitution preserves kinds and lacks. E2–E5, E10. | **Surface/checking:** written rows and checked or inferred tail/lacks relationships; schemes do not retain general qualified row-union or membership constraints. **Core:** complete type and row arguments are retained. Missing proof can make row composition ambiguous. |
| F04 | A request's operand satisfies the selected operation's input type; the result has that operation's output type. Its row includes the operand's requirements and the exact requested instance. | `perform` consumes the operand judgment and declaration F01; its result feeds surrounding computation and handler selection. The static request does not itself select the runtime handler. E4, E6. | **Surface/Core:** operand/result types and computed row; **Core:** operation and instance identities. Other value facts cross from the operand's established judgment. |
| F05 | An ordinary handler's target is established in its body row, its operation clauses cover that declaration exactly once, and clause patterns and answers satisfy the required types. | Handling discharges that exact body requirement, preserves other requirements, and incorporates direct clause effects into the least output row. Direct requests in a clause are not interpreted by the selected handler itself. E5–E6. | **Surface:** handler and types/rows. **Current checking/Core:** clause coverage, patterns, result and output row. The rule consumes the body and clause judgments without requiring their concrete data representations. |
| F06 | A callable or opaque computation has an established value/computation type and effect requirements. Its actual control and resource relationships may depend on arguments and the caller's context. | An in-scope handler or scope composes the callable's facts with its surrounding context. Each call can introduce a new obligation; it does not require the callable's unchanged body to be checked again. E4–E10, R4–R10. | **Surface:** schemes and effect rows. **Current checking:** private summaries carry possible calls, requests, handlers and completion control across imports. The general typed contract for all needed contextual control and resource relationships is not yet defined. |

An effect row describes interpretation requirements, not a complete execution
trace. Ordinary source function arrows also carry the specified implicit
`DefaultAlloc` requirement; written or omitted empty rows do not erase it.
See [row expansion](../../../spec/static-semantics.md#computation-types-and-effect-rows).

## Continuation and control facts

The current static and dynamic rules are in
[effects](../../../spec/static-semantics.md#effects) and
[handler execution](../../../spec/dynamic-semantics.md#effect-handlers-and-completion).
The single-use rules below concern ordinary clauses; private Store `retain`
rules are outside this slice.

| ID | Subject, fact and establishing premises | Consumer, preservation or discharge | Current representation and boundary need |
| --- | --- | --- | --- |
| F07 | A selected ordinary clause has a capability associated with its handler and owner, an operation-result input type, handler-answer type and output row. | `resume` requires an input of the operation's result type, with operand effects contained in the shared output row, and produces the handler answer under that row; operand evaluation must leave the capability available. `discard` has `Unit` result and a close row. E5, E7–E8. | **Current checking:** structural active capability; it is not a source value or source-level continuation type. **Core:** explicit handler/owner, input/answer types and rows on control nodes. |
| F08 | The capability is available or consumed along a normally completing path. A clause starts available and every such path must consume it exactly once. | Sequencing passes the state forward; branches must agree; `resume` and `discard` consume it. Function bodies, nested clauses and specified other boundaries cannot capture an enclosing capability. E7–E9. | **Current checking:** structural dataflow and escape barriers; **Core:** owner/use metadata and structural scope validation. A general source type for this usage relationship is not currently exposed. Divergence does not prove completion. |
| F09 | An evaluated request and each candidate boundary have their own saved lexical instantiations; the runtime context has ordered candidate interpreters. | Runtime selects the nearest accepting exact instance using those instantiations. A source clause runs outside its selected handler; nonmatching crossed boundaries form part of captured control. E6, E10. | **Surface:** exact effect identities and rows. **Core/runtime:** handler identities, lexical instantiation and context. A row alone does not determine which dynamic boundary is selected. |
| F10 | The selected capture has a particular delimited segment, including its selected handler and intervening control, and is owned by its live clause. Nested live clauses can own further captures. | `resume` consumes and restores that segment in order, then returns to the clause suffix. `discard` consumes the owner and closes its recursively owned segment without executing the abandoned suffix. E6–E8, E10. | **Current checking:** capture/control analysis and summaries; **Core/runtime:** structural owner IDs and actual frames. The ordinary function type or row alone does not name the segment or its ownership. |
| F11 | For an attempted discard, the owned closure and the completion owners inside, outside and currently running are identified under the actual context. | The owned closure may close; required completion outside it and running actions/unfinished closes must remain reachable. Unproved safety rejects the relevant discard; it is not automatically proof of an unsafe execution. E8, E10, R6, R8. | **Current checking:** capture and completion analysis; **Core:** owner structure plus validation, with contextual relationships reconstructed where required. [Candidate plan and ticket judgments](first-slice-close-derivation-rules.md) expose these obligations for reuse; their coverage and correspondence remain to be justified. |
| F12 | A computation's callable graph can contain latent requests even when its stored value has no resource dependency; conversely a value can store a dependency without immediately requesting an effect. | Calls compose both relationships with the caller's context. Do not use an empty stored dependency set as proof of no request, or an effect row as proof of no stored dependency. E10, R4–R5. | **Current checking:** distinct value and control graphs and imported summaries. **Surface:** ordinary types and rows do not by themselves encode both relationships. |

The logical account of these facts may use introduction, elimination and
structural rules where justified. Whether shift/reset, propositions, effect
rows or other forms express them is an open design question; no translation or
new source form is assumed here. Future multi-shot and broader discardable
control must distinguish permission to repeat, abandon and own resources.

## Resource and cleanup facts

The current rules are in [generic cells](../../../spec/static-semantics.md#generic-cell-foundation),
[scoped cells](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies),
[cleanup](../../../spec/static-semantics.md#scoped-cleanup-actions),
[cell execution](../../../spec/dynamic-semantics.md#scoped-cell-execution) and
[cleanup execution](../../../spec/dynamic-semantics.md#scoped-cleanup-actions). R1–R10
refer to the companion catalogue. R1 describes the current legacy cell; its
removal is proposed in [CP-0031](../../proposals/CP-0031-remove-legacy-integer-cell.md).

| ID | Subject, fact and establishing premises | Consumer, preservation or discharge | Current representation and boundary need |
| --- | --- | --- | --- |
| F13 | An acquisition establishes a fresh rigid lexical resource identity, an access handle, exact sealed provider/operation authority and a scope-owned completion obligation. Each execution creates a fresh runtime activation, including repeated executions of one lexical site. The initializer is checked and evaluated in the preceding scope. | The body can use the provider and exact operations while the owner is live. The initializer cannot use the new identity or handle. R1–R3. | **Surface:** generic `Cell<R,T>`, `Provider<R,T>`, `Ops<R,T>` and acquisition; legacy equivalents remain current. **Core:** authenticated acquisition, binder, handle and provider relations; runtime instantiates an activation. |
| F14 | A handle is reusable non-owning access; the scope or captured control owns completion. Copying access does not create a second owner or release authority. | Calls and values may retain access only while its owner remains valid; normal completion or an admitted owned close discharges the owner. R3–R6. | **Surface:** opaque handle and provider relation. **Current checking:** dependency/escape and completion analyses establish actual ownership relationships; a handle type alone does not encode every retained dependency. |
| F15 | A particular value, callable, selected evidence or operation payload may depend on identified live owners, independently of what its exposed ordinary type reveals. | A result or payload cannot cross the owner it depends on to a context outside that owner. Independent values may cross; an unrelated enclosing owner can remain available. The cell's own trusted interpreter is an admitted recipient. R4, R10. | **Surface:** types may mention some identities and constraints, but an identity-free result type is not proof of independence. **Current checking:** inferred stored dependencies, actual selected fields/calls and imported summaries; missing relevant proof is conservatively rejected. |
| F16 | A generic cell has a fixed payload type for an acquisition and a current payload root with its own dependencies. Each possible target and actual initializer/replacement must retain only resource owners strictly enclosing that activation. | Read/write preserve the payload type. Reject self-retention, cycles or younger/incomparable owner retention at the initializer or actual replacement; clearing later does not repair an earlier invalid write. R2–R5. | **Surface/Core:** payload `T`, exact provider and operation types. **Current checking:** possible target, current contents and enclosure analysis. A polymorphic `T` does not establish the payload's dependencies. |
| F17 | A read snapshot refers to the value and dependencies returned at that point, separately from the cell's later contents and access handle. An intercepted read uses the actual handler reply; an intercepted write does not itself replace the builtin slot. | A later builtin replacement does not change the earlier snapshot or its retained dependencies. The general preservation rule must account for that specified guarantee; other transitions need their own preservation evidence. The snapshot does not freeze mutable state reachable through it. Only a snapshot independent of a closing owner can cross it. Other clause or resumed writes affect the current cell in control order. R3–R5. | **Surface:** read result has type `T`. **Current checking:** value/control analysis connects actual reply, snapshots and replacements. The ordinary result type alone need not express the particular value's retained owners. |
| F18 | A resource scope has an answer type and an outward effect row; its own exact cell operation instance is interpreted within the scope. | Remove only the scope's exact instance, preserve initializer and other body effects, and prohibit the closing identity and dependent result/evidence from escaping. A nearer exact source handler still has ordinary precedence. R1–R4. | **Surface/Core:** exact rows, value type, identity and provider types. **Current checking:** escape and actual-dependency analysis adds obligations not settled solely by row removal. |
| F19 | Capture can contain a particular cell activation, its contents and its completion owner. A live cell's capacity remains in use while captured. | Resume restores the same owner and contents; normal completion releases it. An admissible discard closes owned cells in structural order without skipping outside obligations. R6, E6–E8. | **Current checking:** captured resource and completion relationships; **Core/runtime:** acquisition identity, owner structure and runtime activation. An abstract context must preserve relevant outside facts rather than assume it owns them. |
| F20 | A cleanup action has an established callable type and latent effects. After initialization and successful acquisition, its scope owns one invocation obligation distinct from copies of the callable. | The scope's row includes initializer, body and action requirements. Normal return or admitted close starts the armed action at most once and must complete it before returning the saved result or continuing close. R7–R8. | **Surface/Core:** callback type, effect row and cleanup structure. **Current checking:** callback control, dependencies and completion analysis; the callable's ordinary type does not by itself establish all actual closing relationships. |
| F21 | A cleanup owner is armed, running or finished; a running action and unfinished close have completion obligations. Action-local, retained and surviving interpreters differ by structural position and lexical instantiation. | Capture/resume preserve phase and saved result. Discard may start an armed action, but may not skip running completion. A removed required interpreter cannot be replaced merely by an outer same-instance handler. R8–R9, E8. | **Current checking:** control and interpreter-compatibility analysis, including transitive actual requests and summaries. **Core/runtime:** owner and control structure; the current outward row alone does not name the needed interpreter. |
| F22 | Closing an owned capture has a least residual effect row derived from its actual actions after action-local and still-enclosing retained builtin resource interpretation; it may carry dependencies of saved results, action captures and operation payloads. | `discard` consumes the owned continuation, yields `Unit` with that residual row and preserves outside obligations. Surviving source handlers, including clause-local handlers, check and discharge appropriate residual effects at their own boundaries. R9–R10, E8. | **Surface/Core:** the resulting computation row. **Current checking:** close-requirement inference and strict validation establish action/interpreter relationships not expressed by the row alone. |
| F23 | A value or computation can also carry backing-storage and external assumptions, even when its type is `Int`; resource ownership and storage residency are different facts. | Preserve those established outside facts through values, cells, calls and captured contexts. At failure or close, apply the relevant external and operational premises rather than classifying every internal failure as external. R3–R6, R8. | **Current checking:** region/dependency machinery and boundary contracts; explicit region rules are outside this slice. **Specification:** internal work/capacity failure and external assumptions still require classification against the target guarantee. |

## How the rules compose the facts

This index identifies the required flow, not proposed new inference rules or a
complete per-subject producer/consumer ledger. It uses existing E/R IDs and the
fact IDs above so that a fact serving several rules has one entry rather than
being re-established independently. Runtime completion claims below describe
successful transitions under their applicable premises; they do not assert
termination or promise completion after an internal failure.

| Rule family | Consumes | Establishes, preserves or discharges |
| --- | --- | --- |
| E1–E3: declaration, instance and rows | Parameter kinds, identities and row constraints. | F01–F03; substitution preserves applicable identity, equality and lacks facts. |
| E4: request | F01–F03 and the operand's established judgment and relevant dependencies F15/F23. | Establishes the request judgment F04 and its exact effect requirement; later runtime selection uses F09. |
| E5: handler typing | F01–F03 and the body judgment. Introduce F07 to check each clause, including structural use F08. | Establishes the handler judgment F05; removes the handled exact body requirement and preserves the other row requirements. |
| E6: runtime handler selection | F01, F04 and F09, the evaluated operand and the actual ordered control context. | Selects an interpreter and, for the source-handler branch, moves the delimited segment into owned capture F10. This transition is distinct from E5's static premises. |
| E9: structural capability use | F07–F08 and the checked clause's sequential and branching structure. | Tracks availability and consumption on each normally completing path and rejects prohibited capture; it does not itself restore runtime frames. |
| E7: resume | F07–F08 and the operand judgment; runtime restoration also uses F09–F11 and relevant F19–F23. | Consumes the capability; runtime restores its control and preserves applicable owned and outside obligations. The clause can complete after the resumed computation returns. |
| E8: discard | F07–F12 and relevant owner, dependency, interpreter and cleanup facts F14–F23. | Consumes the capability and yields the static result and row F22. On successful owned close, discharges its close obligations; outside and running obligations must remain valid. |
| E10: contextual capture analysis | F01–F04 and F09–F12, plus relevant resource and cleanup facts F14–F23. | Establishes the relationships needed for a particular request and context. A resume-only composition does not by itself consume a capability by discard or discharge a close obligation. |
| R1–R3: cell acquisition and access | Acquisition consumes the API declaration, preceding initializer judgment, payload type, dependency facts F15 and applicable backing facts F23. Access consumes the resulting F13–F14 and value facts. | Acquisition establishes fresh scope/owner F13–F14 and exact cell authority; access uses that established provider and handle. |
| R4–R6: dependency, state and cell completion | F10–F12 and F14–F19, including facts about actual payloads and owners. | Preserves type, dependencies, activation and snapshot facts as applicable; discharges owned completion at normal return or admitted discard; rejects unproved escape/retention. |
| R7–R10: cleanup and close | Action/body judgments and F11–F12, F15 and F20–F23. | Establishes the cleanup owner and computes the residual close row under the actual interpretation context. On successful completion, discharges that owner while preserving the saved result and outside obligations. |

### Use a complete upper bound

A dependency check is one use of a more general type-level relationship.
For a relation `Rel(subject, x)` and a domain `S`, write
`Upper(subject, Rel, S, U)` when the established proposition guarantees that
every `x` in `S` related to this subject belongs to `U`. `U` may include
additional possibilities; it is not necessarily exact. The subject, relation,
domain, guard and relevant state or activation are part of the fact. A
contract or other common rule must establish completeness over `S`; an
incomplete list is not an upper bound merely because no further item was
found.

```sequent
J-Upper-Exclude :=
  GAMMA; L, phi |- Upper(subject, Rel, S, U) [O_upper]
  GAMMA; L, phi |- x is in S and x is not in U [O_membership]
  the evidence is about the same subject, relation and guarded case
  O_out retains O_upper and O_membership under their original guards and scopes
  ===>
  GAMMA; L, phi |- not Rel(subject, x) [O_out]
```

This is implication elimination and set reasoning over already certified
facts; it does not inspect the subject. For a resource dependency, `Rel` can
describe the actual dependency on an owner; for an effect behavior, a
separately established contract can use a suitable relation over possible
requests. Neither interpretation follows automatically from an ordinary
payload type or from a list of observed operations. A top bound `U = S` is
safe but cannot exclude a member of `S`. Missing completeness, an unresolved
membership or a different actual activation remains an obligation. The
[dependency-cover rules](first-slice-dependency-cover-rules.md#meaning-and-subject)
are a concrete instance of this general form, not a reason for a second
resource-specific proof mechanism.

### Preserve an established fact across a transition

The same preservation rule applies to a request, handler, resource operation
or other in-slice transition. Let `P(subject, s)` be a persistent proposition
about a particular subject at state `s`. Let `T(s, s')` be one correlated
transition case from the applicable certified contract. The proposition
`Stable(T, P, subject)` says that, for every admitted pair of states in this
case, `P(subject, s)` and `T(s, s')` entail `P(subject, s')`. The transition
contract or another established proof must supply this implication; merely
having the same ordinary type at both points does not supply it.

```sequent
J-Preserve-Fact :=
  GAMMA; L, entry, phi |- the same certified case relates subject, s and s' by T [O_case]
  GAMMA; L, entry, phi |- P(subject, s) [O_before]
  GAMMA; L, entry, phi |- Stable(T, P, subject) [O_stable]
  the same subject, witnesses and assumptions are in scope at s'
  the evidence is non-circular, including for any recursive transition contract
  O_out retains O_case, O_before and O_stable under their original guards and scopes
  ===>
  GAMMA; L, entry, phi |- P(subject, s') [O_out]
```

This rule uses the already established transition and preservation facts; it
does not inspect the implementation again. The conclusion is for the same
guarded case. A claim covering the entire composition needs this consequence
for every applicable case, including separately covered failures and unknowns;
a terminal outcome with no post-state cannot be treated as a successful
post-state. `P` describes a fact and does not itself duplicate a capability:
the relevant ownership or usage judgment still governs any authority moved or
consumed by `T`. In particular, preservation of a value's identity or its
declared dependency cover does not automatically freeze mutable state reached
through that value. If a transition's contract does not establish the needed
stability, retain the proposition as an obligation and record any missing
general form or rule in the [rule ledger](first-slice-rule-resolution.md).

### Export a fact from a local scope

The proposition and obligation rules already require local witnesses not to
escape, but they do not by themselves establish what a particular scope may
export. The following candidate schema states that relationship for any
certified local scope. It does not prescribe which declarations may hide or
transfer an identity or authority. `x` is a local type identity, dynamic
owner, value or case witness with its own sort; it need not be a runtime
value. `F_out` is well scoped in the enclosing context or under an explicitly
permitted shared binder.

```sequent
J-Export-Scoped-Fact :=
  GAMMA, x; DELTA_local, phi |- the certified local case establishes F_local [O_local]
  the same actual scope entry establishes the local assumptions and authority under which F_local was derived, or retains their scoped obligations O_entry
  the established scope and crossing contracts admit this actual normal exit and determine its related result, state, outside authority DELTA_out and well-scoped guard phi_out
  the applicable authority protocol accounts for every local and outside capability and completion obligation, including any permitted transfer or discharge, or retains scoped O_authority
  an admissible logical elimination derives F_out from these same local facts without exposing x, or a separately justified scoped interface binds x
  every feasible local exit represented by phi_out is covered by the established case or other certified cases that also entail this F_out, with all remaining obligations retained
  O_out retains O_local, O_entry, O_authority and all exit and derivation obligations under their original guards and local binders
  Out is the tuple (DELTA_out, phi_out, F_out, O_out) when x is absent, or one justified scoped package binding x around that entire tuple
  Out is well scoped in GAMMA, and any permitted hidden x denotes the same witness in all four components
  ===>
  GAMMA |- scoped_export(Out)
```

The exit and derivation establish the same `DELTA_out` and `phi_out` used in
`Out`; they cannot widen the case guard without covering the added
executions, silently discard a linear obligation, duplicate
authority or export an unbound witness. A conditional result remains
conditional on `O_out`. When no `x` is hidden, the tuple carries the ordinary
judgment `GAMMA; DELTA_out, phi_out |- F_out [O_out]`. When an existential or
other scoped interface is allowed, a **single** binder encloses the whole
tuple; unpacking uses that same witness for its guard, fact, authority and
obligations. Four independent existential packages do not establish that
correlation. The binder and scope must be explicit, and the applicable contract must permit
every retained dependency or authority. Hiding an owner behind an existential
does not extend its lifetime or permit access after it has ended. Historical
facts about a completed owner do not themselves recreate its authority.

This rule describes one covered **normal exit**. Requests, abandonment,
failure and non-return retain their own cases and applicable obligations;
they do not manufacture a normal export. It reuses the local certificate and
checks only the new boundary relationship. The available representations for
scoped obligations and permitted existential interfaces, and their
correspondence with existing escape checks, remain design gaps.

## Current gaps and follow-up

### Declarable contracts and the shared rules they need

The following inventory distinguishes current language forms from the
proposed contracts needed by this slice. A **new form or rule** means a
type-system facility must be specified; it does not necessarily mean a
source annotation. Surface inference or an authenticated builtin declaration
may supply a fact, but typed Core must retain the complete resulting type
and the applicable behavioral facts and obligations. These proposals do not
introduce a user-extensible resource facility or a separate verifier for each
effect or resource.

| Needed contract or fact | Current declarable form and precise gap | Producer, consumer and required addition |
| --- | --- | --- |
| **Require an interface of effect parameters.** For example, associate `Error<E>` with `Failure<E>` and specialize it for the same actual `E`. | [Effect declarations](../../../spec/syntax.md#grammar) admit parameters and operations but no declaration-level interface requirement. Existing [interface requirements](../../../spec/static-semantics.md#interfaces-and-constrained-schemes) apply to supported declarations; they do not add an effect-parameter bound. | The general effect declaration states the requirement. Instantiation uses established evidence or carries a scoped obligation; Core retains that relationship for later use. **Needed:** general formation, specialization and evidence-scope rules, not a checker specific to `Failure`. |
| **Attach behavior to an effect operation.** Relate the actual operand, request, admissible replies and their effects, state and dependencies. | An [effect declaration](../../../spec/static-semantics.md#effects) gives exact identity, parameters and one pure `P -> Q` signature per operation; the [syntax](../../../spec/syntax.md#grammar) admits no operation-local requirement or body. A [row](../../../spec/static-semantics.md#computation-types-and-effect-rows) is an unordered effect requirement, not that behavior. | The authenticated effect/operation declaration or a sound producer supplies the contract; shared request, selection and handler composition consume it. **Needed:** a general way to associate behavioral propositions and scoped obligations with an operation and instantiate them. Whether source may write them is undecided. |
| **Attach behavior to a resource and its operations.** State acquisition, authority, access, completion and applicable state/row relations without making every resource a cell. | The [resource grammar](../../../spec/syntax.md#grammar) permits a named nominal form; current resolution and static admission restrict it to the documented builtin and named families, not arbitrary provider instantiation. Current [generic-cell semantics](../../../spec/static-semantics.md#generic-cell-foundation) specifies read, write, retention and completion in the language rules; it does not offer an ordinary source declaration for those behavioral contracts. | The existing authenticated builtin or another established contract producer supplies each applicable fact; common resource-scope, access, crossing, transfer and completion judgments consume it. **Needed:** general contract association and shared introduction/elimination rules. This need does not by itself extend the set of source-declarable resources. |
| **Describe guarded behavior at a boundary.** Relate actual values, source or Core states, request/reply cases, non-return, failure and residual control without inspecting an opaque producer. | [Computation types](../../../spec/static-semantics.md#computation-types-and-effect-rows) retain a result type and row. [Core lowering](../../../spec/elaboration.md#effect-core-lowering) retains types, rows and structural operation identities, while current capture and dependency checking establish additional relationships separately. Those forms are not a general complete behavioral contract. | The first checker of a fragment supplies a guarded case interface; a new call, handler, resource or sequencing composition consumes it. **Needed:** propositions or an equivalent general type-level judgment for correlated behavior and delimited residuals, plus coverage rules. Unknown cases remain obligations. |
| **Name and preserve dynamic ownership and dependency facts.** Relate a specific value and actual owner to applicable authority, resource state, crossing and completion conditions. | Source [types, kinds and schemes](../../../spec/static-semantics.md#kinds-monotypes-and-schemes) and [interface constraints](../../../spec/static-semantics.md#interfaces-and-constrained-schemes) express ordinary type and provider relationships. The [resource rules](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies) require more, including hidden dependencies and separate control obligations; an ordinary payload type alone cannot express them. | Acquisition, selection and certified value producers establish scoped owner, dependency and state relationships; access, capture, crossing and close consume them. **Needed:** general scoped propositions and ownership/usage judgments, including complete dependency bounds when a particular contract requires them. No uniform retention or one-shot policy is assumed for all resources. |
| **Compose a capability and its control.** Preserve an actual selected capture, its one-shot use, outside obligations and the cases after resume or discard. | The [ordinary handler rules](../../../spec/static-semantics.md#effects) and [operational rules](../../../spec/dynamic-semantics.md#effect-handlers-and-completion) specify and check current one-shot use and control, but source function types and rows do not declare a general capture or residual-control relation. | Selection and the certified captured segment supply its case-specific interface; resume, discard and owned-close compositions consume it. **Needed:** general control and capability propositions with introduction, elimination, move and scoped case rules. Future multishot and discardable continuation policies need their own contracts; this inventory does not choose them. |
| **Retain and discharge conditional evidence.** Carry a proof's subject, guards, local witnesses, assumptions and outstanding obligations through instantiation and composition. | Current [schemes and interface requirements](../../../spec/static-semantics.md#interfaces-and-constrained-schemes) are not a general source proposition or proof language. [Module and Core elaboration](../../../spec/elaboration.md) retain specified identities and structural evidence; they do not specify the proposed reusable behavioral-certificate interface. | A fragment's first checker or an authenticated external boundary supplies the judgment; later compositions reuse it and prove only new premises. **Needed:** scoped proposition/evidence and obligation-transport rules, including a separate capability discipline and a non-circular account of discharge. A registry is optional; a verified fragment is not checked again merely because it crosses a boundary. |
| **Relate exact rows and possible failure.** Preserve conditional row relations and the actual failure phases that affect narrow correctness. | Current [row formation and partial operations](../../../spec/static-semantics.md#computation-types-and-effect-rows) provide exact members, tails and lacks; they do not provide a general behavioral contract or establish an unknown tail's contents. The [operational semantics](../../../spec/dynamic-semantics.md#effect-handlers-and-completion) and [Core boundary](../../../spec/elaboration.md#validation-boundary) separately describe applicable execution and validation. | Row composition, resource/handler boundaries and the closed-program check consume the established relationships and failure assumptions. **Needed:** sufficiently expressive row and failure propositions with shared inference/composition rules, or another equivalent checked form. The exact solver, external assumptions and any failure-semantics revision remain design work. |

Existing [interfaces](../../../spec/static-semantics.md#interfaces-and-constrained-schemes)
remain useful for selecting and forwarding ordinary provider evidence; their
existence does not by itself supply these behavioral propositions. Likewise,
the current builtin cell implementation is evidence for its declared contract,
not a reason to create another cell-specific verification algorithm. The
[shared resource schemas](first-slice-resource-rules.md#common-resource-judgments-and-concrete-instances)
and [judgment requirements](first-slice-judgment-requirements.md#candidate-propositions-and-evidence)
develop candidate forms. Their expressiveness, producer/consumer correspondence
and system soundness are still to be established.

1. **Boundary language.** Source types and rows already state part of F01–F06
   and F13–F18. The current private summaries and analyses carry more, but the
   type language does not yet provide a general contract for every contextual
   fact in F07–F12 and F19–F23. Determine the required judgments and where
   inference can supply them; do not assume all facts must be source-written.
2. **Composition.** Specify the premises and conclusions for composing
   previously established facts. Check the new composition without verifying
   its verified constituents again. Do not reconstruct an opaque producer to
   fill an absent contract silently.
3. **Evidence and correctness.** Relate the selected judgments to the intended
   operational rules and failure assumptions. The existing
   [one-shot formalization](../direct-effects/one-shot/README.md) supplies
   bounded model evidence, not a complete Ash implementation theorem.
4. **Before and after.** The companion map records current shared analyses and
   consumers. Decide each fact's eventual producer and every consumer's
   disposition, retaining shared machinery where other slices still use it.
   Account for the current independent-validation requirement in
   [AD-0007](../../decisions/AD-0007-typed-core-dialects.md) when the work reaches
   that implementation boundary. The present design checks compositions using
   the certifications of verified constituent fragments.

Source propositions, laws and general proofs are not implemented as current Ash
facilities; see the [trajectory](../../trajectory.md). Whether they, existing
types or new rules should express a particular missing relationship is a
design question for the next step, not a fact established by this inventory.
