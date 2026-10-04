# Resource definitions, typing, surface forms, and Core

> This study is experimental evidence under
> [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
> The type schemas, grammar, and transitions below are comparison inputs, not
> accepted Ash syntax or normative semantics. Incomplete contracts cannot
> authorize an implementation slice.

## Method and current boundary

Always follow the types. Start with a resource type definition, check its
provider and associated effect interface and handlers, then derive the typing of
a resource instance. A proposed spelling needs that account before becoming an
implementation target.

Current [resource
typing](../../../spec/static-semantics.md#scoped-cells-and-resource-dependencies)
and [syntax](../../../spec/syntax.md) provide the baseline: the initializer is
checked before introducing the fresh identity; the acquired body receives a
handle, exact sealed authority, and an interpreter. Current Ash supports only
`cell` and `native_buffer`, with compiler-defined contracts. This study proposes
library-defined resource types. It must preserve the distinction between
ordinary effect interpretation and authority to create or complete a resource.

Use current [effects and handlers](../../../spec/static-semantics.md#effects)
where their types suffice. Effects declare parameterized operation interfaces;
handlers check implementations against those operation types. A resource type
adds the relationship between that interface, provider state, initialization,
unique identity, access, and completion. A matching set of method names is
insufficient to establish that relationship.

## Selected first execution contract

This section selects candidate P-1 for implementation. The studies below explain
its roles; a previously open choice is resolved only to the extent stated here.
P-1 is experimental, and does not change `spec/`. The
[selected complete owner row arguments](#selected-complete-owner-row-arguments)
extend this experimental contract; their compiler evidence remains pending.
P-1 tests S-01 first, then the
remaining cases in [the execution record](execution.md). A successful scalar
example alone does not establish success for DN-0036.

### Declaration and instance

The first declaration spelling is a module declaration. It creates an opaque
resource family; it is not a data declaration followed by an ordinary `impl`.
Fields and clauses end at line boundaries, following current declarations. The
following is the complete assembly shape, with operation bodies supplied by the
Ash library author:

```text
pub resource Connection<R> {
input OpenConfig
state Native.ConnectionState<R>
result Provider.Scope<OpenError, CloseError, T> for <T>
provider ConnectionProvider<R>
effect ConnectionOps<R>
interpret Native.Connection<R>
acquire config => perform Native.Connection<R>.open config
finish state => perform Native.Connection<R>.close state
handlers state {
diagnostic db => resume (ForeignError (perform Native.Connection<R>.diagnostic state))
}
}

pub resource Statement<S, C> {
input (Connection<C>, SqlText)
state Native.StatementState<S, C>
result Provider.Scope<PrepareError, FinalizeError, T> for <T>
provider StatementProvider<S, C>
effect StatementOps<S, C>
interpret Native.Statement<S, C>
acquire input => match input {
(db, SqlText(sql)) => perform Native.Statement<S, C>.prepare (Provider.state_of db, sql)
}
finish state => perform Native.Statement<S, C>.finalize state
handlers state {
bind_int operand => match operand {
(stmt, index, value) => match (perform Native.Statement<S, C>.bind_int (state, index, value)) {
Native.Ok(()) => resume (Ok ())
Native.Err(error) => resume (Err (ForeignError error))
}
}
step stmt => match (perform Native.Statement<S, C>.step state) {
Native.Row => resume Row
Native.Done => resume Done
Native.StepError(error) => resume (StepError (ForeignError error))
}
column_int operand => match operand {
(stmt, index) => match (perform Native.Statement<S, C>.column_int (state, index)) {
Native.Ok(value) => resume (Ok value)
Native.Err(error) => resume (Err (ForeignError error))
}
}
}
}
```

The associated effects are ordinary Ash effect declarations. For S-01,
`ConnectionOps<R>.diagnostic : Connection<R> -> Error`, and the three statement
operation types are those in the typed-instance table below. `OpenError`,
`CloseError`, `PrepareError` and `FinalizeError` are independent native data
re-exported by the source library. Its protocol and operation results are
separate ordinary source data:

```text
pub type Error = ForeignError(Native.Error)
| MissingRow
| UnexpectedRow
pub type Result<T> = Ok(T)
| Err(Error)
pub type StepResult = Row
| Done
| StepError(Error)
```

The library maps native operation results into these constructors in its checked
handlers; it cannot add constructors to the native error nominal. Thus the S-01
fixture's `MissingRow` and `UnexpectedRow` branches have type `Error`.
`OpenConfig` initially has `InMemory` and `File(Bytes)` cases. `SqlText` wraps
independent `Bytes`. `Bytes` is an ordinary immutable list of integers; native
conversion checks `[0,255]`, length, UTF-8 where required, and embedded zero
rules. No string syntax or silent integer truncation is needed. The malformed
SQL, empty SQL and file paths are real byte inputs, not native operation IDs
standing in for SQL text.

The first registered SQLite module has the following complete ordinary data
shapes. Constructor identities and field order are manifest facts; codec
dispatch uses those identities rather than searching for spellings at each call.

```text
pub type Bytes = EmptyBytes
| MoreBytes(Int, Bytes)
pub type OpenConfig = InMemory
| File(Bytes)
pub type InputFault = BadIndex
| BadInteger
| BadBytes
| BadColumn
| ColumnTypeMismatch
| BadSql
| MultipleStatements
| BadPath
pub type ProtocolFault = NotPrepared
| NotRow
| AfterDone
| ClosedOwner
pub type Error = NativeFailure(Int, Bytes)
| InputFailure(InputFault)
| ProtocolFailure(ProtocolFault)
| ConversionFailure
| AllocationFailure
pub type OpenError = OpenFailure(Error)
pub type CloseError = CloseFailure(Error)
pub type PrepareError = PrepareFailure(Error)
| EmptySql
pub type FinalizeError = FinalizeFailure(Error)
pub type Result<T> = Ok(T)
| Err(Error)
pub type StepResult = Row
| Done
| StepError(Error)
pub type BytesOrNull = NullBytes
| BlobBytes(Bytes)
pub type Acquire<State, E> = Acquired(State)
| Refused(E)
pub type Finish<State, E> = Consumed
| ConsumedFailure(E)
| Retained(State, E)
```

The two state families are public opaque native nominal families of kinds
`ConnectionState : Type -> Type` and `StatementState : Type -> Type -> Type`.
Their internal constructors are absent from every source-visible constructor
channel. Acquired state tokens are made only by registered native operations
under their unpublished guards. `Acquire` and `Finish` constructors are ordinary
data and provide no guard or capability by themselves; controlled template
checking and runtime postcondition tokens are required even if a client
constructs a `Consumed` value.

`NativeFailure` stores the exact native result code and a copied diagnostic as
independent bytes. Input/protocol faults map the safe adapter's structured
failure before native use. Native column-kind rejection is `ColumnTypeMismatch`;
a failed native conversion is `ConversionFailure`; an actual recoverable native
copy-allocation failure is `AllocationFailure`. Internal Ash work/storage
exhaustion remains a terminal runtime failure and is never relabeled by this
codec. Empty SQL maps to `Refused(EmptySql)`; malformed SQL maps to a
`PrepareFailure`. Failed open maps to `OpenFailure`, finalize error to consumed
`FinalizeFailure`, and refused close to retained `CloseFailure` with the same
state token. These wrappers keep the error families distinct without duplicate
constructor names in the registered module.

The codec folds `MoreBytes`/`EmptyBytes` with checked byte/range/length work,
rejects cyclic or malformed byte inputs, and produces the same ordinary list
from copied native diagnostics/output. `File` requires a valid owned UTF-8 path
with no embedded zero; `InMemory` supplies the native `:memory:` filename.
`SqlText` remains a source newtype over these bytes; preparation passes their
checked explicit length and rejects multiple statements. Empty `BlobBytes` is a
BLOB and `NullBytes` is SQL null. Neither turns into the other through a null
host slice pointer. Source error mapping adds only the library protocol cases
shown above.

Registered native modules define canonical `OpenConfig`, `Bytes`, error,
`Result`, `StepResult`, `Acquire` and `Finish` families independently of the
resource library. The SQLite source module re-exports configuration, bytes and
lifecycle-error families, maps native operation results into source result
families, and wraps SQL bytes in its own `SqlText`. The native module does not
import the SQLite source module. Exact first signatures are:

```text
Native.Connection<R>.open:
  Native.OpenConfig -> Native.Acquire<Native.ConnectionState<R>, Native.OpenError>
Native.Connection<R>.diagnostic:
  Native.ConnectionState<R> -> Native.Error
Native.Connection<R>.close:
  Native.ConnectionState<R> -> Native.Finish<Native.ConnectionState<R>, Native.CloseError>
Native.Statement<S,C>.prepare:
  (Native.ConnectionState<C>, Native.Bytes) -> Native.Acquire<Native.StatementState<S,C>, Native.PrepareError>
Native.Statement<S,C>.bind_int:
  (Native.StatementState<S,C>, Int, Int) -> Native.Result<Unit>
Native.Statement<S,C>.step:
  Native.StatementState<S,C> -> Native.StepResult
Native.Statement<S,C>.column_int:
  (Native.StatementState<S,C>, Int) -> Native.Result<Int>
Native.Statement<S,C>.finalize:
  Native.StatementState<S,C> -> Native.Finish<Native.StatementState<S,C>, Native.FinalizeError>
Native.Statement<S,C>.bind_bytes:
  (Native.StatementState<S,C>, Int, Native.BytesOrNull) -> Native.Result<Unit>
Native.Statement<S,C>.column_bytes:
  (Native.StatementState<S,C>, Int) -> Native.Result<Native.BytesOrNull>
Native.Statement<S,C>.reset:
  Native.StatementState<S,C> -> Native.Result<Unit>
Native.Statement<S,C>.clear_bindings:
  Native.StatementState<S,C> -> Native.Result<Unit>
```

These are pure operation arrows inside their respective parameterized native
effects; a request adds that exact native instance. None refers to the source
`Connection` or `Statement` nominal family. The open/prepare operations have
acquiring roles, close/finalize have finishing roles, and the others borrow.
Native preparation retains the actual connection state's C dependency and copies
SQL before returning. It does not retain the SQL input.

The manifest records relational results, not only value types: `diagnostic`
returns independent `Native.Error`; bind returns independent `Ok(Unit)` or
`Err(Error)`; step returns independent `Row`, `Done` or `StepError(Error)`;
column access returns independent copied `Ok(Int)` or `Err(Error)`. Those
nominal constructor alternatives contain no state/owner dependency. The source
mapping clauses preserve that fact in their own constructors. A default
opaque/unknown external-result summary is insufficient to prove their matches
and resumes safe. Preparation retains C in its successful state branch and
returns independent failure data; acquire/finish success and refusal branches
retain their controlled state/capability relation separately from these copied
borrowed results.

The copying additions borrow statement state and return independent constructor
shapes as well. `bind_bytes` uses the adapter's transient/copy operation;
`column_bytes` returns a fresh copied `BlobBytes` list or `NullBytes`. Reset and
clear-bindings return copied unit/error results. They are distinct operations:
reset alone makes no retention-release claim. Their later retained/view variants
need separate declared relations, not a changed meaning for these copying calls.

`Provider.state_of` is a general controlled primitive. Descriptor admission
supplies a sealed determination relation `StateAccess<Q,State>` from an exact
resource access type to its exact associated state type. Its method has type `Q
-> State`, using current determined-interface typing. Thus in the statement
acquire template `Provider.state_of db : Native.ConnectionState<C>`. The
primitive can run only in provider contexts, borrows a live scope's state, and
cannot complete or transfer that owner. Its result retains C and cannot leave
the provider context. Runtime dispatch uses the admitted resource definition and
activation IDs, never nominal spellings. A new library receives this relation
from its own resource descriptor without changes to the primitive's code.
Finisher capability checks still permit completion of the current owned state
only, excluding an outer state obtained this way.

Generated provider handler entry independently authenticates the resource access
operands against its instance before executing the source clause. It retains
typed operand positions from the associated signature, including tuple fields;
ordinary source handler overrides retain existing checking and precedence.
Native borrowed calls then need only the state token and raw operands. This
avoids a cyclic native signature mentioning library handles and avoids passing
redundant client handles to the adapter.

`ConnectionProvider<R>` and `StatementProvider<S,C>` are source-declared
interfaces. Their methods have the associated operation names and value types,
with the exact associated effect row on the result arrow. For example,
`StatementProvider<S,C>.bind_int` has value type `(Statement<S,C>, Int, Int) ->
Result<Unit> ! {StatementOps<S,C>}`. The resource association seals these
interfaces against ordinary `impl` and `with` construction. Declaration
admission rejects an existing implementation, another resource association or a
missing/mismatched method. The association generates checked forwarding evidence
at acquisition, following the current cell convention, rather than requiring the
library to implement construction authority in an ordinary interface equation.

Methods enter the module's existing term namespace. A collision uses ordinary
duplicate-name rejection, including two associated interfaces with the same
method spelling in one module. Authors can use distinct operation names or
separate modules; targeted imports already permit term aliases. No special
type-qualified method lookup is added. The first SQLite module's `diagnostic`,
`bind_int`, `step` and `column_int` are distinct.

`resource Sqlite.Connection<C> db = config { body }` and `resource
Sqlite.Statement<S> stmt = (db, sql) { body }` are expression positions. Only
`C` or `S` after the resource type reference introduces a fresh binder. In the
statement expression the input unifies its second formal parameter with the
already live connection identity. Unresolved remaining parameters reject as
ambiguous. The initial comparison uses an explicit body; a remainder-of-block
binding is a later spelling comparison with the same contract.

The grammar addition is separate from the existing builtin resource expressions:

```ebnf
resource_declaration ::=
  [ "pub" ] "resource" upper_identifier type_parameters "{" line_end
  "input" type line_end
  "state" type line_end
  "result" type "for" type_parameters line_end
  "provider" interface_application line_end
  "effect" effect_instance line_end
  "interpret" effect_instance line_end
  "acquire" identifier "=>" expression line_end
  "finish" identifier "=>" expression line_end
  "handlers" identifier "{" line_end
  handler_clause { line_end handler_clause } [ line_end ]
  "}" [ line_end ] "}" ;
```

The first formal parameter is the resource identity and has kind `Type`. The
result field binds exactly one kind-`Type` answer parameter. The state binder is
available to handler clauses and the distinct finish clause only; the
initializer binder is available to acquire only. Types, expressions and handler
clauses reuse current grammar. Declaration checking supplies hidden answer-type
and row parameters to the clause templates. Their row-instantiation relation
is defined below; the full client continuation row and its normalized residual
are distinct. These parameters are not source
handler values or rank-2 functions. Definition checking compiles each template
once to typed generic Core under hidden rigid answer and row binders, identified
by a `ProviderTemplateId`. An instance instantiates the admitted
type/effect/dependency/control contracts with its actual answer type and checked
continuation context using that relation; it
does not recheck the provider's raw source or resolved body. Linked modules
supply the already checked executable template Core by descriptor/template ID.
Specialization substitutes checked arguments into that Core and independently
validates the resulting ordinary exact handlers. Body-free authenticated public
summaries suffice for client checking and must retain every relevant contract
and defining origin; executable linkage separately requires the template code.
Ordinary source handlers retain their lexical precedence.

P-1 supplies sealed forwarding evidence for the declared provider relation. Its
construction origin is the resource declaration identity. Public summaries
preserve that defining origin; neither copied declarations nor a matching
ordinary `impl` creates construction or completion authority.

### Handler template answer and row instantiation

Declaration checking allocates a fresh hidden answer binder A of kind Type and
a distinct hidden row binder rho of kind EffectRow before checking the actual
operation clauses. These identities belong to the defining ProviderTemplateId
and cannot alias a source answer parameter, a formal resource parameter, or
another template's hidden binders. The canonical associated operation
op_i : P_i -> Q_i determines the pattern type P_i and resume input Q_i. Every
clause produces A; its owned resume produces A with the shared handler output
Omega. The declared resource operand type is not A.

A template retains its checked direct clause-demand relation D(sigma,c) and
its relation to the full client continuation row epsilon as separate facts.
Here sigma is the authenticated kind-preserving substitution of formal
arguments and selected evidence. The input c is independently reconstructed
from the actual owned captures, their completion obligations and the surviving
interpreter context, using current capture, discard and completion rules. A
scalar epsilon and sigma alone do not determine discard's close demands. When
c is not yet known, the template retains authenticated conditional equations
for those demands; it does not assert a concrete close row. D_sigma is shorthand
only for capture-independent cases.

D(sigma,c) includes resume argument evaluation and all other direct clause work,
including native requests, checked helper latent demands and admitted close
execution. Its derivation suppresses shared outputs of the properly owned
internal resumes within the relevant direct-demand analysis, preserves their
argument demands, and applies ordinary exact nested-handler removals. It does
not replace nested handlers' own output checks. The full epsilon is the actual
handled body's outward remainder at the generated ordinary exact handler
boundary, derived by current exact removal, not an arbitrary row supplied by
the provider. The outer shared output must satisfy the least ordinary principal
union Omega = D(sigma,c) union epsilon and agree with the independently
reconstructed ordinary least-output equations of the actual handler graph.
This equality is checked, not assumed to linearize every nested row equation.
All known members, tail identities and lacks constraints follow current row
algebra.

The hidden rho may occur as an ordinary Core tail only in a recorded residual
realization of that relation. Let K be the exact known-member set of D(sigma,c)
after substitution and canonical coalescing. After deriving Omega, derive r by
exact removal from Omega of every member of K; no removal searches an
unconstrained tail. The instantiation relation is rho -> r, with
r = Omega remove K and Omega = K union r. Thus rho denotes this normalized
residual, not epsilon. An open r retains Omega's exact tail identity and every
existing lacks fact, including the justified exclusions of K. For a closed r
there is no tail constraint to retain. Recomposition uses ordinary row
formation/substitution and must equal Omega, including tail identity and
accumulated lacks facts. Replacing rho with epsilon without deriving and
checking this relation is invalid; kind agreement alone is insufficient. If
the authenticated relation establishes epsilon = r, the same row value is a
valid replacement. This occurs, for example, when D is empty, or when D is
closed and its known members are disjoint from epsilon. Replacement validity depends on the
row equations and constraints, not on the row value's origin.

The exclusions of K in the residual template's own tail describe this internal
normalization relation; they assert nothing about absence of K from the full
client continuation. Authority for D comes from checked actual clause Core,
authenticated operation, helper and evidence facts, and independently
reconstructed c where completion depends on capture. Authority for epsilon
comes from the checked actual body and exact handler boundary. Authority for r
and its lacks facts comes from the independently checked union and exact
removals. Neither EffectRow construction, draft metadata, matching names, nor a
public-summary assertion supplies those proofs. Ordinary instantiation must
still check all additional retained template lacks constraints, occurs checks,
kinds and scope identities.

A single ordinary open row does not encode an unresolved equation between
distinct direct-demand and continuation tails. Until the existing algebra can
establish their relationship, the generic template retains the
D(sigma,c)/epsilon/Omega relation and the actual clause row-replay inputs as an
authenticated internal recipe. This recipe is conditional template validation, not a new source row
syntax, a qualified ordinary type scheme, or proof that provisional Core already
satisfies ordinary handler row equations. Specialization resolves that recipe
with checked actual arguments and reconstructed c, computes the existing
principal union and any residual realization, and solves and checks each
handler's distinct shared-output equations through the retained typed graph.
It instantiates admitted Core and its authenticated facts;
it does not re-elaborate provider source or resolved bodies. Every resulting
ordinary exact Handler then undergoes ordinary independent validation,
including least output, resume argument/result/row, structural scope, capture
and completion. If the current union is nonprincipal, specialization reports
that ordinary ambiguity without adding lacks facts. A representation that
cannot yet retain an otherwise principal recipe is an explicit implementation
frontier, not a new language rejection or a global closed-row requirement.

The authenticated body-free summary must preserve the defining template
identity, formal kinds and hidden-binder roles/identities, exact operation and
resume contracts, D(sigma,c) or its checked demand recipe, the
full-continuation-to-output relation, residual normalization and any additional
row constraints, and relevant evidence, owner, capture/control and origin
facts. Conditional completion contracts must identify the actual capture and
surviving-interpreter facts needed to establish c; scalar effect rows cannot
stand in for them. Executable linkage separately supplies the corresponding
checked template graph, per-handler output and owner/root relations, and
row-replay inputs. Independent admission compares these contracts with the
defining checked context; copies or invented summaries cannot create authority. Native
demands in D remain present in Omega until the separately admitted
interpretation discharges the exact native instance. This row normalization
neither authorizes native interpretation nor removes capture/control obligations.

#### Handler row recipe authentication

The retained recipe is an equation graph reconstructed from the actual typed
clause graph, not caller-authored equations or a D/Omega match claim. Each real
HandlerId, including nested handlers, has a distinct internal shared-output
unknown Omega_h. Its actual owned ResumeIds refer to that unknown only through
their authenticated handler/owner and clause-root relation. Unknowns with equal
row values remain distinct identities. Ordinary child equations preserve resume
arguments, callable/request demands, exact handler removal and all other
current row operations. Direct-demand analysis suppresses only resume outputs
whose handlers belong to the relevant analysis root's owned-handler set, as
current least-output reconstruction does. An enclosing resume occurring in a
nested handler's body remains an input from its enclosing Omega_h when checking
that nested handler; it is not globally suppressed or treated as that nested
handler's resume.

Independent template checking reconstructs those handler sets, actual clause
roots and structural pattern/resume scopes. It checks canonical signatures,
ordinary stored callable/request rows and authenticated imported selections,
all non-row metadata, answer/input types, single consumption and phase
authority. It reconstructs c-dependent demand equations and verifies that every
deferred row position belongs to these actual equations. Builder ranges only
delimit replay; they do not authorize deferred positions, handler identities
or capture assumptions. Any row relation not independently derivable from the
actual graph and canonical context rejects. D may therefore be a checked
expression over formal row arguments and c, rather than an asserted literal.

At specialization, substitute authenticated kinded formal/evidence facts into
those reconstructed equations and independently reconstruct c from the actual
capture/completion and surviving-interpreter facts. Derive epsilon from the
real outer handler body, and compute the outer candidate Omega using existing
union/removal. Evaluate and check every retained node equation and every
Omega_h against that handler's ordinary least-output reconstruction, with each
actual ResumeId receiving its own handler's solved output. Recompute all
affected resumes and descendants, including nested handler clauses; an outer
range replay that keeps other resumes unchanged is insufficient. Check the
outer candidate against the reconstructed outer least output rather than
assuming the D(sigma,c) union epsilon form replaces those equations. Unresolved
c-dependent obligations remain conditional until the actual facts establish
them; none may survive admission to ordinary Core. No unresolved recipe,
unchecked row hole or added tail exclusion survives that boundary. Ordinary
independent handler validation is final: every handler result row equals its
reconstructed least output, and all resume, scope, capture/completion and
metadata checks pass.

Public summary retains authenticated conditional row contracts/known inputs
for client checking; linked code carries the exact equation/root
correspondence and must authenticate against that defining summary/context.
An unpublished source draft may retain this information without Core
admission. Independent generic template admission must prove this
correspondence, not just construct the recipe. Closed D is an initial
realization, not a P-1/source admission rule.

#### Required handler row evidence

- D={H}, epsilon={H,K}: Omega={H,K}, r={K}.
- D={H}, epsilon={H,K|eta}, with existing eta lacks H,K: Omega is unchanged;
  r={K|eta} retains both exclusions.
- D={H}, epsilon={K|eta}, with an existing H exclusion: add H and preserve eta.
  Without H in epsilon's known set or eta's established exclusions, this is
  ordinary ambiguous union, not a new candidate rejection.
- D={|delta}, epsilon={H}, with delta already lacking H: Omega={H|delta}.
  Refusal merely because D is open remains an implementation frontier.
- With D empty, authenticated epsilon = r is a valid rho replacement. Also
  check a closed disjoint D/epsilon pair for which epsilon = r. Reject unchecked
  epsilon-to-rho replacement when overlap makes epsilon differ from r; do not
  reject an authenticated equal row value based on its origin.
- A provider clause can contain the ordinary nested handler:

  ```ash
  handle({ let ignored = perform H.op (); resume () }) with H {
    op x => resume ()
  }
  ```

  The first resume belongs to the outer provider clause and the second to H's
  clause. With outer epsilon={H,J} and D={}, outer output and its resume row are
  {H,J}; the nested handler output and its own resume row are {J}. Check both
  least-output equations and every node row. Keeping the nested resume's
  provisional empty row during outer replay is stale, not evidence that the
  nested handler has no outward demand.
- Distinct actual owned captures or surviving interpreter contexts with the
  same sigma and scalar epsilon must derive their own c and close rows under
  existing rules. Reject forged c, erased close demands or asserted independent
  discard rows; unknown c remains conditional until specialized facts settle it.
- Reject distinct unsolved tails, unjustified or forged exclusions, wrong exact
  effect arguments, hidden row identity collisions/occurs checks, mutated
  D/r/Omega with coherent row
  metadata, mismatched nested handler/resume/root identities, stale nested
  resume or descendant rows, and dropped native demand.
- Specialization must work without provider-body replay. Preserve caller work
  and reject without publication on any failed relation.

### State and native authority

The machine owns a nonduplicable native guard separately from source values.
`Native.ConnectionState<R>` and `Native.StatementState<S,C>` are opaque,
non-owning state tokens usable only in checked provider contexts.
`Connection<R>` and `Statement<S,C>` are different opaque client access tokens.
Neither token contains a source address or owns release. State tokens cannot
become ordinary client results, captures, evidence fields or stored data.
Provider templates may capture the state token for their owned handler and
completion code; their scope and authority remain tied to that resource
instance.

Ordinary local aliases of a state token inside its direct controlled computation
preserve the same lineage. For example, `let held = state` followed by the
permitted finisher on `held` does not create a second owner. Each alias remains
subject to the phase's operation roles and the same completion capability;
consuming that capability prevents subsequent native access through every
alias, including after a retained outcome. This permits non-owning token aliases,
not callable or storage transport of state or duplication of the native guard.

Acquisition has a controlled `Acquire<State, InitError>` result. Native code
places a successful owner under the machine's unpublished guard before a state
token can be delivered to the acquire template. A terminal successful branch
publishes that guard once; a terminal failed branch publishes no access. There
is no source `publish` function. Pure data preparation, error mapping and total
matches are permitted, but each successful acquire path must return exactly the
guarded state produced by its registered acquiring operation. Duplicating,
discarding, replacing or fabricating native ownership rejects at declaration
checking; local aliases do not alter which guard the returning path publishes.

The finish context has one controlled completion capability, analogous to the
single-use resume capability. Every returning path must invoke exactly one
registered finisher for its state. Finisher replies authenticate `Consumed` or
`Retained`; returning an independently constructed report cannot manufacture
that postcondition. The guard remains machine-owned until consumption or
quarantine. Calling a finisher twice, calling it from an ordinary client, or
using a state token after consumption rejects. Handler clauses may invoke only
borrowed state operations, never acquiring or finishing ones. These are new
provider checking obligations, not consequences of an ordinary function arrow.

Native registration is a reusable boundary, not a resource-kind switch. The
driver admits a table of `NativeLibraryId`, opaque state type identities,
effect/operation identities, exact signatures, state roles, independent error
constructors, retention/postcondition contracts and safe Rust dispatch
functions. The registered module, imported for example as `Native`, supplies
authenticated foreign declarations. Module admission checks its signatures
against that table; Core retains the registered operation identity and role.
Another foreign library adds a safe adapter and a registration table, then
writes its resource definitions and policy in Ash. It does not add a parser
case, resource enum alternative, checker spelling test or library-specific owner
transition. Arbitrary dynamic symbols, unregistered source ABI declarations,
callbacks and general C layouts remain unsupported authoring features of P-1.

The selected import is `import @foreign.sqlite as Native`. The driver's
registration map owns the full `@foreign` module path. `@foreign.provider` is
the general registration supplying the authenticated `StateAccess<Q,State>`
interface with determination `Q -> State` and its `state_of : Q -> State`
method. An ordinary source `provider.ash` defines `Scope` and `Completion` and
re-exports that interface and method; the examples' `Provider` alias refers to
this source module. Re-exports preserve the defining method/interface identity.
Missing registrations reject; no filesystem module with the same spelling can
replace them. The reserved path admission is a candidate loader extension, not
current import behavior.

Each registered module receives an ordinary graph-local admitted `ModuleId`,
plus immutable `ForeignModuleAdmission(module_id, registration_id,
manifest_digest, origin)` metadata in the loaded/checked registry. Resource
checking authenticates its state families, effect/operation identities and
privileged methods against that admission. It does not add a SQLite-specific
`ModuleId` namespace or privilege a module alias. `StateAccess` rejects ordinary
source `impl`/`with`; only an admitted resource descriptor supplies its exact
state relation. Public/linked summaries retain admission and defining origin,
and independently verify re-exports against the admitted defining registry.

P-1 has a deliberate callable-authority boundary. Ordinary lambda bodies, global
bodies and evidence-method bodies clear the controlled provider phase. Only the
declaration's direct acquire, handler and finish computation inherits that phase
through blocks, matches, local data bindings and direct operand evaluation.
`state_of` must appear as a direct, fully applied authenticated method
occurrence; selecting it as a first-class method value, aliasing it or retaining
it in a closure/evidence value rejects. The same restriction applies through
imports and targeted aliases. Native acquiring/borrowing/finishing requests in
ordinary callable bodies reject even if the callable was defined inside a
provider template. Ordinary pure helpers and generic helpers requesting public
associated effects remain supported. Privileged higher-order helpers require
phase requirements in callable/public summaries and are unsupported in P-1.

For example, a provider `get_reader` clause cannot resume with `fn(()) { let
ignored = Provider.state_of db; 42 }`. The closure retains only legal client
access but would manufacture provider state when called by a client. The lambda
phase barrier rejects that occurrence; owner non-escape alone would miss it.
Native-request wrappers and imported methods laundering `state_of` are paired
negative fixtures at checking and independent Core validation.

The first lifecycle profile is synchronous: acquire and finish have empty
outward rows after their declared registered-native interpretation. They permit
effect-free data preparation/mapping and their direct controlled native calls,
but no source handlers, resume, discard, hooks, cleanup or nested resource
forms. An unrelated source request before or after acquiring the unpublished
guard therefore rejects. This avoids granting an unspecified capture/discard
transition to unpublished native ownership. Ordinary initializers still run in
the preceding scope with their inferred outward effects; they own no new guard.
Source cleanup actions around the acquired body remain supported and complete
structurally before its synchronous native finisher. Later source-effectful
lifecycle templates need a separate unpublished/running-completion capture
contract.

`interpret Native.Connection<R>` explicitly interprets this registered native
effect inside acquire, provider handlers and finish only. A declaration cannot
interpret an ordinary source effect by listing it here. Its provider templates
retain their native requests in checked Core; a general foreign interpreter
boundary discharges precisely the admitted registered instances. It does not
discharge a client's native request or an unrelated outward provider effect.
Thus a client `main` still needs the current empty entry row. Imports remain
passive. Adapter initialization is host-owned and idempotent; a connection never
owns SQLite-wide shutdown. No global resource rule is implied.

### Report algebra and failure order

The library report is ordinary data with this candidate algebra:

```text
type Completion<E> = Closed | ConsumedError(E) | RetainedError(E)
type Scope<I, E, T> = NotAcquired(I) | Completed(T, Completion<E>)
```

P-1 selects a positional source report codec. In the defining nominal
declaration, `Completion<E>` has ordered roles 0: closed with no payload,
1: consumed error with payload E, and 2: retained error with payload E.
`Scope<I,E,T>` has ordered roles 0: not acquired with payload I and
1: completed with payload `(T, Completion<E>)`. The displayed names are library
spellings; roles come from this explicit codec contract and defining constructor
order. Export-name order and aliases cannot change them.

Admission checks these canonical generic payload templates and ordered formal
parameter positions before substituting actual types. It retains the defining
Scope and Completion nominal identities and each exact constructor identity and
ordinal. Equal instantiated types, such as I equal to T or E equal to Unit,
cannot supply or alter the roles. Reordering the two same-typed completion
constructors changes their codec mapping even though the result type is
unchanged. This is an explicit P-1 authoring convention, not an inferred meaning
of a constructor name. An explicit role-association syntax remains a later
comparison if the positional convention creates observed friction.

The declaration's result field must instantiate this checked shape with its
actual independent initialization and completion error families. Constructor
identities, not their spellings, are retained in the descriptor. A normally
returning body preserves its exact value as `T`; an ordinary body `Result`
remains nested and is never flattened. Completion follows the body and all
structurally inner actions. `Completed(body, ConsumedError(error))` preserves
both a body error and a finalization error. Nested reports preserve their
structural order; the observation trace records actual completion order.

Ordinary construction of these source reports grants no lifecycle authority.
The authenticated native Acquire/Finish result, current guard lineage and
controlled capability establish publication, consumption or quarantine. The
machine maps that established outcome into the selected source report codec.

Open failure and malformed/empty preparation are initialization outcomes. Empty
SQL is `NotAcquired(EmptySql)` and never enters a statement body. Partial open
or prepare state stays guarded and is disposed before failure delivery. Internal
capacity/work exhaustion and publication failure remain terminal runtime
failures, with original cause and teardown status; they are not `NotAcquired`
constructors. Publication preparation reserves activation, handler, result and
disposal storage before native acquisition. Failure after acquisition disposes
the unpublished guard once, records whether disposal completed, and never
evaluates the body.

Finalize consumes the statement even when its report is an error. Close refusal
retains the connection; the machine removes all source access and quarantines
the owner together with every native dependency until host teardown. It reports
`RetainedError` without pretending that close succeeded. Quarantined owners are
unreachable from source and count in native live-storage observations. Their
safe host destruction is recorded separately from source completion; no
automatic source retry or deferred-close substitution is promised. Ordinary
admitted statement nesting finishes before connection completion, so actual
busy-close refusal is tested in the native reference harness and separately
injected in the report path, rather than deliberately leaking an Ash statement.

Owned discard invokes the same finish templates in structural order while their
outer state remains available. It emits completion observations but supplies no
abandoned body value or fabricated `Scope` result. The discarding clause
receives its ordinary result. A running finish cannot be abandoned, and a
required interpreter outside the owned capture cannot be skipped. Internal
teardown uses safe native destruction and never executes source finish code as
recovery.

### Core and runtime map

Generalize the existing resource carrier; retain ordinary handler, application,
match and cleanup nodes for Ash provider policy. The carrier owns the resolved
definition, instantiated parameters, fresh identity, typed access binder,
initializer, acquisition template, exact instantiated handler templates,
completion template, result relation, retained-state summary and origins. The
existing builtin descriptors remain compatible; SQLite is not a new
`ResourcePayload` alternative selected from source syntax.

The independently validated declaration descriptor contains:

| Field | Checked meaning |
| --- | --- |
| Definition and family identities | Resource declaration origin and opaque nominal Q, parameter kinds and first identity position. |
| Input and state templates | Exact initializer type; opaque state role; retained dependency relation. |
| Provider identity and methods | Sealed relation and forwarding operation identities, owned by this definition. |
| Acquisition/finish templates | Typed Core, lifecycle capabilities and admissible registered operation roles. |
| Provided instances | Associated exact effects, operation signatures and checked handler templates. |
| Interpreted native instances | Authenticated registration identities and explicit provider-only interpretation. |
| Result template | Answer binder, error families, native lifecycle constructor identities and ordered source report codec. |
| Summaries and origins | Actual captures, retained state, operation results, completion requirements and defining/import origins. |

P-1 selects a unary effect-dialect operation for the direct controlled
`state_of` occurrence. This is a representation target, not implemented public
authority. Its retained fields are:

```text
ProviderStateAccess {
  method: MethodId,
  definition: ResourceDefinitionId,
  arguments: [KindedArgument],
  operand: NodeId
}
```

The method's owner supplies its canonical `InterfaceId`. The independently
checked resource association supplies the client type `Q<r, alpha>` and
substituted state template; those determine the operand and result types.
Ordered arguments follow the resource declaration's binders and retain the
TypeArg or RowArg tag selected by the complete-owner amendment below. Native
ABI vectors remain Type-only and use the separately authenticated interpret
mapping. Ordinary node
metadata already retains the result type and origin. The operation contributes
no intrinsic outward effect; its operand's effects remain in the result row.
It is not an ordinary method application or a foreign request with an invented
`OperationId`.

Validation derives `Enclosing(definition, r)` from that association and the
operand's live resource access. No payload permission or lineage flag supplies
that proof. Statement acquisition can borrow `ConnectionState<C>` through
Connection's descriptor while interpreting `Native.Statement<S,C>`; the
accessed resource's native effect need not equal the current template's effect.
The borrow creates neither a guard nor a completion capability. Runtime lookup
also authenticates the exact live activation represented by the operand.

Checked header associations suffice only for unpublished draft checking. Public
summaries, imported templates and final linkage require the independently
admitted descriptor. Direct source recognition precedes ordinary method-value
synthesis and uses the canonical method identity through import renaming.
First-class method values, callable wrappers and ordinary `impl` evidence
remain unavailable for this operation. Its traversal, type substitution,
transform remapping, phase/scope validation and captured owner dependencies
must be implemented together before Core admission. An empty outward row does
not make the returned state independent of its owner.

The checked template descriptor explicitly retains hidden rigid answer
`TypeVariableId` and continuation `EffectRowVariable` binders, their kinds,
formal resource-parameter binders, the state/input `BinderId`, operation-clause
`OperationId` and operand binder, each clause's owned `ResumeId`, and distinct
acquire/finish capability IDs. Each expression is validated in its reconstructed
phase context: ordinary, acquire with unpublished capability, handler with
borrowed current-state access and clause resume, or finish with single-use
completion. Callable barriers clear the phase independently of where their
syntax is nested. The public descriptor retains substituted
input/state/operation/result types, provided/interpreted rows, dependency and
control relations, capability/lineage contract and executable template IDs.
Hidden row/type binder identity is part of the contract; the source `result ...
for <T>` binder does not replace it.

Generic template validation receives the authenticated declaration context:
canonical local declarations and formal binders, imported checked facts and
their hidden kind closure, and the checked schemes, capture/control relations,
evidence requirements and origins of referenced globals. External declarations
keep their defining identities; they are not converted into invented local
parameters. A mutable elaborator environment or the template's own registry
cannot authenticate this context. Templates referencing local globals remain
unpublished until whole-module checking succeeds. This contextual entry checks
ordinary Core graph, type, effect, scope and origin obligations as well as the
provider phase and lifecycle relations. Specialization and final linking still
require independent validation in the complete linked environment.

#### Evidence occurrence retention and specialization

The publication experiment selects explicit occurrence relocation into the
existing single final catalog. Current evidence slots use allocation identity;
ordinary checked bodies keep those allocations alive through final synthesis.
Provider templates retain the exact original owners after those bodies are
removed. Repeated specialization can give one original occurrence different
type/row facts, so each copied occurrence also needs a fresh final identity.

The proposed private carriers separate those roles:

| Carrier | Retained relationship |
| --- | --- |
| Checked provider template | Generic typed Core, kinded formal/hidden binders, admitted defining context and source-occurrence records. Each record pins its exact original evidence slots and retains checked roots, arguments, types, rows, scope and origin. |
| Prepared specialization | Exact template reference and source-occurrence ordinal, authenticated kinded substitution, validated source-plan to specialized-plan node relation, and one fresh final occurrence owner per copied occurrence. |
| Final evidence catalog | Fresh target identities, their owners and source-template references, plus canonically derived expectations and relocated indexes. |

A final occurrence owner holds allocation identity only, with no selection or
fill capability. It stays alive with every catalog referencing its key.
Templates retain no final catalog or specialization that refers back to them;
registry and Core ownership must also avoid an indirect cycle. Source records
survive the atomic module publication without retaining resolved source bodies.

Specialization substitutes resource parameters and hidden answer/continuation
rows into already checked relationships. It preserves selected implementations,
roots, ordered methods and prerequisites, defining producer authority, scope
relations and causal origins. It does not search for implementations again.
Independently validate that full relation against the retained source plan and
admitted defining context before lowering and canonical reconstruction borrow
the same specialized plan. Sharing a plan alone proves no authenticity.

Freshen copied local graph, term, type, row, resume and capability identities;
preserve canonical external declarations. Relocate occurrence keys and every
catalog-local owner, domain, adapter, producer, expectation and selection-node
reference as required. Prepare the complete derived catalog before sizing the
final builder. Final linked validation remains a separate boundary.

Authenticated abstract and lexical dictionary scopes are required alongside
concrete implementation selections. Retain their requirement owners, dictionary
positions, lexical identities, captured binders and enclosing envelopes.
The current closed imported-selection checkpoint does not establish that
mapping. Absent source evidence cannot be supplied by implicit specialization
search or an invented header requirement.

Evidence must cover distinct substitutions and same-argument repeats,
different answers/rows, alias diamonds, source disposal and allocator churn,
abstract/lexical scopes and independent mutations of source provenance,
substitution, plan edges, producer authority, local capabilities and catalog
indexes. Work refusal must leave no partial publication; fresh retries and
iterative disposal must preserve ownership. This is a reviewed experimental
representation direction, not implemented publication or current Ash semantics.

Native state and effect metadata declare the owned identity argument position
and every borrowed/retained owner position. Connection has owned position 0 (R);
statement has owned position 0 (S) and retained connection position 1 (C).
Resource admission requires the native owned argument to equal the resource's
fresh formal identity, and acquisition to produce that exact state's guarded
lineage. A declaration `Q<R,C>` with `state Native.ConnectionState<C>` therefore
cannot own C merely because an input or return type unifies. Its native owned
argument differs from R, so declaration checking rejects it.

State access carries reconstructed lineage, not merely a type: current acquired
state is `Current(definition, identity, acquire-capability)`, while `state_of`
borrows `Enclosing(definition, identity)` from its exact accessed scope. A
finisher must consume the current state's completion capability and current
lineage. An enclosing token with a matching abstract state type is insufficient;
the machine also checks its concrete activation. Retained finish replies
preserve that same current lineage for quarantine. Public summaries and
independent Core validation retain/reconstruct these facts, including under type
substitution and imported templates; they cannot rely on a lexical source
permission flag.

Resolved instances refer to that descriptor and retain the instantiated
parameters, fresh identity, handle binder and body. Validation reconstructs
types, effects, controlled authority, result construction and dependencies from
the registry and actual Core; a source permission bit is insufficient. Transform
traversal includes every retained template and type. Mutation tests change each
relation separately, including a finisher role and report constructor.

An initializer evaluates once in the preceding environment. Acquisition executes
its checked Ash template under the foreign interpreter; success moves the same
guard to the resource owner frame and binds fresh activation-backed access.
Ordinary exact handlers execute the Ash operation clauses using the provider
state token. Normal completion saves the body value, runs the checked finish
template with its single-use capability, then publishes the reserved report.
Capture moves the owner, handlers, state and pending completion together. Resume
restores them without reacquisition. Discard runs admitted owned completion
using the existing cleanup/disposal ordering, extended with the template's
actual captures and interpreter requirements.

### Heterogeneous arena contract required after S-01

P-1 does not infer general allocation from a monomorphic node handler. The arena
slice adds declaration-level quantified handler templates. A template covers
`Allocate<A,T>` uniformly for `T` requiring sealed `Layout<T>` evidence, while
each demand and generated Core handler remains an exact effect instance. The
template has independent answer-type and row parameters as above. Ordinary
source values remain rank-1, and no operation-local polymorphism is introduced.

The resource body and authenticated helper summaries determine a finite set of
demanded exact instances. Specialization accepts abstract `T` only with a
checked layout dictionary; concrete dictionaries derive from the admitted
structural layout rules. Source `impl` cannot forge `Layout`. Unrelated open row
tails pass outward unchanged. An unresolved tail that could contain a required
provided instance is not silently discharged; the experiment must report the
unresolved coverage obligation. No universal closed-row restriction is added.
Specialization, summary storage and traversal charge the existing finite work
ledgers.

The first layouts admit `Unit` (size zero), checked signed-64-bit `Int`
payloads, byte sequences, immutable tuples, acyclic nominal data and scoped
references. Arena capacity counts payload bytes plus alignment padding.
References encode owner and object identities in private stable storage, not
exposed addresses. Arbitrary-precision integers outside the selected layout
return `InvalidPayload` rather than truncate. Zero capacity is a valid empty
arena; zero-sized objects still receive fresh object metadata but consume no
payload bytes. Metadata is measured separately. Alignment and overflow checks
precede reservation; complete initialization and metadata reservation precede
publication. Failure rolls the cursor back and preserves earlier objects.
Closures stored as arena payloads and cyclic construction require another
layout/construction contract; closure capture of allocated references remains
admitted.

Allocation records the actual payload's relational value summary. Dereferencing
recovers that shape in an ordinary shallow value: copied scalar fields are
independent, and embedded references keep their own owners. In M-03 the tuple
object depends on B and its contents retain A/B references; loading and
selecting the A field yields an A dependency only. Neither `load : Ref<B,T> ->
T` alone nor a blanket B dependency proves that projection. Deep copying
recursively copies admitted acyclic data into independent ordinary storage or a
specified live recipient arena; the first comparison duplicates shared payloads
and records that cost. Shallow copying is separately typed and never called
independent.

Before X-01 through X-04, extend this contract with explicit retained-access and
view intervals, invalidation conflicts and branch/capture joins. Those rules are
still open here; owner dependencies and native Rust guards cannot substitute for
them. Their task cannot start by silently selecting a runtime-only borrow rule.

### Front-end schema and initializer inference

The selected surface declaration retains `name`, visibility, ordered formal
parameters, input/state types, result type and its answer binder, provider
application, provided and interpreted effect instances, acquire input binder and
body, finish state binder and body, handler state binder and clauses, and spans.
Each clause remains ordinary source syntax with its original origin. The module
resolver predeclares the resource nominal family and resource definition ID
alongside ordinary type/effect/interface declarations before resolving bodies.
It resolves these fields under the formal-parameter scope and resolves the
result under its extra answer binder. Lifecycle binders and resume capability
ownership are distinct; a state binder spelling cannot authenticate a controlled
phase.

The resolved declaration retains those identities, checked-kinded type
templates, provider/effect occurrences, resolved acquire/finish expressions and
handler templates. It is not yet a checked descriptor. The checking/elaboration
stage authenticates native registration and lifecycle roles, checks the
associated interface and clause templates, then publishes a checked registry
descriptor. An incomplete declaration cannot be imported as admitted authority.

The resolved instance refers to its resource definition and resolves the
initializer in the preceding term/type scope before extending the body with the
fresh identity and handle binders. It retains outer parameter metavariables or
equivalent deferred instantiation, rather than guessing them from surface names.
Elaboration checks the initializer and unifies its type with `I<alpha>`. For
`(db,sql)` this determines `C` from `db : Connection<C>`. Kind or name
resolution alone does not establish that fact. Remaining ambiguous parameters
reject before checking a body under unjustified authority. The new identity does
not appear in the initializer type, inferred outer parameters or preceding
evidence.

Native acquire and finish replies are separate from the ordinary client report:
`Acquire<State,I>` has guarded success or independent refusal; `Finish<State,E>`
has consumed success, consumed error or retained-state refusal. Their defining
constructors, state positions and operation postconditions belong to the
authenticated manifest. Template checking preserves the guard/capability on
every branch, and the resource machine converts the authorized result into the
declared `Scope`/`Completion` constructors. Constructing a native reply data
constructor without the corresponding controlled operation is not authority.

## Selected complete owner row arguments

Status: selected amendment to DN-0036 experimental P-1. Independent contract
and prose reviews approve bounded experimental selection. It remains informative
and off `main`: selection is neither current Ash, product adoption nor executed
source proof. The recorded module-publication checkpoint was Type-only. The
common-support workstream now implements the row-aware slice; its
[execution record](execution.md#current-checkpoint) distinguishes source
progress from verified delivery.
Revision-2 review approved the design for evidence work; the later attribution
correction identifies associated EffectId uniqueness as a new bounded rule.
The frozen amendment SHA-256 is
`34d6302a773cee409e38a5cbc0db9fc4a380ccb7593e794417a31046365296c2`; review
SHA-256 is `caa0392fb371dbac14d46b0079f25fc3547b6b4b799399bcf242f344212d0edc`.
The [plan](plan.md#complete-owner-row-argument-follow-on) records review and
follow-on evidence. These hashes identify external design evidence, not source
or runtime results.

Current implementation evidence includes public declaration checking and module
publication with mixed owner arguments, imported row payloads and original
owner signatures. Independent Core and evidence checks reject wrong argument
tags, unsaturated applications, missing owner records and out-of-scope variables
or tails. These are checked boundary properties, not a proof of the amendment.
They do not establish generic provider-scope execution, lifecycle completion,
captured-control specialization or the open-row callback witness. The execution
record identifies the tested source and remaining obligations.

Current [row and kind
rules](../../../spec/static-semantics.md#computation-types-and-effect-rows)
admit complete scheme rows and Type-only owner arguments. This candidate adds
complete saturated row arguments to independent resource, effect and interface
owner signatures. It tests whether actual synchronous Ash callback application
can give owner-formal open direct demand without higher-rank ordinary values.
Ordinary data, nominal and implementation owners, operation/method-local row
quantification, partial mixed constructors and EffectRow kind arrows remain
excluded. An owner may have several complete row slots.

One owner specialization fixes the callback row across handle, operation,
evidence and demand relation. Operation/method-local row quantification is a
separate unselected alternative: it requires per-request instantiation,
universal clause/evidence checking and aggregation absent from P-1. An unused
relay or conventionally callable Type variable cannot establish outward demand.
Owner kind eligibility depends on its declaration, not visible associations;
association checking separately establishes sealed resource authority.

The selected row-free P-1 declaration, initializer inference, native state and
ABI contracts remain unchanged. The [handler
recipe](#handler-template-answer-and-row-instantiation), including answer/resume
ownership, conditional capture input c, principal union, residual normalization
and independent final validation, remains authoritative within this design
package. This amendment supplies a row-argument route only for its complete
owner applications. Selection does not claim the current compiler admits them.

### First source pressure case

The following is a proposed complete source module against the already
registered `@foreign.sqlite` and `provider` modules in P-1. Those imports
declare every external name used here; their native data and manifest remain
unchanged. `Rows` and `Delta` are source identifiers; lowercase delta elsewhere
is a metavariable. This is a purpose-built diagnostic callback, not a claim that
a useful SQL diagnostic API needs callbacks.

```ash
import @foreign.sqlite as Native
import provider as Provider

pub type Error = MissingRow
pub effect H {
op : Unit -> Unit
}

pub effect ConnectionOps<R : Type, Rows : EffectRow> {
diagnostic : (Connection<R, {| Rows}>, Unit -> Unit ! {| Rows}) -> Error
}
pub interface ConnectionProvider<R : Type, Rows : EffectRow> {
diagnostic : (Connection<R, {| Rows}>, Unit -> Unit ! {| Rows}) -> Error ! {ConnectionOps<R, {| Rows}>}
}

pub resource Connection<R : Type, Rows : EffectRow> {
input Native.OpenConfig
state Native.ConnectionState<R>
result Provider.Scope<Native.OpenError, Native.CloseError, T> for <T : Type>
provider ConnectionProvider<R, {| Rows}>
effect ConnectionOps<R, {| Rows}>
interpret Native.Connection<R>
acquire config => perform Native.Connection<R>.open config
finish state => perform Native.Connection<R>.close state
handlers state {
diagnostic (db, callback) => {
let ignored = callback ()
resume MissingRow
}
}
}

pub client<Delta : EffectRow> : (Unit -> Unit ! {| Delta}) -> Provider.Scope<Native.OpenError, Native.CloseError, Error> ! {H | Delta}
client callback = resource Connection<C, {| Delta}> db = Native.InMemory {
let ignored = perform H.op ()
diagnostic (db, callback)
}
```

The method `diagnostic` enters the ordinary term namespace; no type-qualified
method lookup is invented. The source callback is a monomorphic function in the
operation domain. It executes in the clause before resume. No native function
invokes Ash, no callback is stored in resource state, and no callback escapes
this operation. The enclosing lexical callback may live outside the resource;
only an escaping value dependent on the fresh identity is forbidden. General
effect operands' existing capture and dependency rules still apply.

Native open and close execute under the sealed interpreter at the existing
lifecycle points. The native state remains live throughout the operation and
finishes after the body. The callback is Ash code running inside that lifetime.
Its ordinary effects are not silently handled by the native interpreter.
Existing lifecycle refusal, retention, exceptional completion and postcondition
token rules are unchanged. This witness introduces no foreign callback ABI.

### Concrete syntax delta

Current `type_arguments ::= "<" type { "," type } ">"` changes to a context-free
tagged argument list in every existing application position. The parser
recognizes braces as RowArg without resolving the preceding name. It recognizes
other type syntax as TypeArg. Resolution then classifies the resolved
declaration and checks whether that category admits each tag. Ordinary Type-only
constructors reject RowArg semantically and otherwise preserve their existing
application and residual-kind rules. This is an explicit syntax delta; it is not
lookup-dependent parsing.

The following replacements use existing `type`, `effect_row`,
`nominal_type_reference`, `effect_reference`, `interface_reference`,
`identifier` and P-1 `resource_type_reference`. Those reference productions
retain unqualified and qualified imported names. The resource expression
production schematizes existing initializer/body delimiters; its block contents
reuse existing block grammar.

```ebnf
application_argument ::= type | effect_row ;
type_arguments ::= "<" application_argument { "," application_argument } ">" ;
resource_type_application ::= resource_type_reference type_arguments ;
provider_interface_application ::= interface_reference type_arguments ;
effect_instance ::= effect_reference [ type_arguments ] ;
operation_reference ::= effect_reference [ type_arguments ] "." identifier ;
resource_instance_parameters ::= "<" upper_identifier { "," application_argument } ">" ;
row_resource_expression ::=
  "resource" resource_type_reference resource_instance_parameters identifier
  "=" expression "{" expression "}" ;
```

Existing `atomic_type ::= ... | nominal_type_reference [type_arguments] | ...`
now parses these tagged lists without adding RowArg as an atomic type.
Resolution distinguishes ordinary TypeApply from saturated ResourceApply using
the resolved owner identity. A bare `{|Rows}` cannot occupy an ordinary
value-type position. Interface constraints use the same argument production,
including qualified imported interfaces. Explicit operation references such as
`perform Library.E<C,{|Delta}>.op operand` parse independently of whether
Library.E exists; resolution checks the owner and operation, then kinds.
Ordinary effects with no row slots still reject row tags. Parenthesized and
higher-kinded ordinary Type arguments keep their existing meanings.

Existing `type_parameter` already parses `Rows : EffectRow`; owner admission
changes, not the binder grammar. A bare `Rows` argument parses as TypeArg and
rejects in a row slot: write `{| Rows}`. No implicit Type-to-row coercion. `{}`,
`{H}`, and `{H | Delta}` are complete RowArgs, subject to existing
well-formed-row rules. Malformed braces fail parsing; a tagged row AST
containing a Type payload fails validation.

For row-bearing resources the instance list supplies the fresh identity binder
followed by every remaining actual, in declaration order. No silent partial
application or omitted mixed slot inference. Existing row-free P-1 instance
forms, including remaining Type inference from an initializer, keep their
contract; fully explicit row-free forms need no new meaning. Consequently
`Connection<C>` rejects when Connection also declares Rows. `Connection<C,
{|Delta}>` is not an ordinary explicit term type application.

### Kinds, metadata and saturation

A resource owner registry entry records defining identity, ordered parameter
identities and fixed kinds, identity role at position zero, association origins
and result category. Its complete application yields Type. Its associated effect
yields an exact effect instance; its interface yields a constraint, neither an
ordinary monotype kind. An owner with a row slot has no denotation as an
unsaturated ordinary constructor and no residual kind. Never assign `Type ->
EffectRow -> Type`.

In these rules `J` abbreviates current type/row environments, `O` is the
authenticated owner registry, and `arg_i` is tagged TypeArg or RowArg. Arity
precedes positional checks. `k_i` is a fixed parameter kind. Ordinary TypeArg
may use already admitted ordinary higher-kinded Type-only kinds where the
existing owner position allows them; no new kinds are inferred. The row rule
uses current well-formed-row checking.

```sequent
Arg-Type :=
  J |- t => k
  k is admitted ordinary kind
  ===>
  J |- TypeArg(t) argument : k

Arg-Row :=
  J |- e row ok
  ===>
  J |- RowArg(e) argument : EffectRow

Resource-Saturated :=
  O(F) = resource(parameters, origin)
  length(args) = length(parameters)
  for each i, J |- args_i argument : kind(parameters_i)
  ===>
  J; O |- ResourceApply(F, args) => Type

Effect-Saturated :=
  O(E) = effect(parameters, origin)
  length(args) = length(parameters)
  for each i, J |- args_i argument : kind(parameters_i)
  ===>
  J; O |- EffectApply(E, args) instance ok

Interface-Saturated :=
  O(I) = interface(parameters, origin)
  length(args) = length(parameters)
  for each i, J |- args_i argument : kind(parameters_i)
  ===>
  J; O |- InterfaceApply(I, args) constraint ok
```

Association admission checks the canonical positional substitution relating all
three telescopes, rather than matching strings. It grants sealed authority; it
does not determine any owner's kind eligibility. Type-only arguments reuse
current resolution, kind synthesis, unification and provenance. Ordinary generic
Type construction and unary Type application remain unchanged. Row-bearing
families cannot be supplied to ordinary higher-kinded constructor parameters. If
broader owner applications or partial row application become necessary, return
to design.

### Defining signatures and sealed associations

Each defining effect/interface/resource declaration independently assigns one
stable owner ID and an ordered parameter signature `(BinderId, fixed kind,
parent-owner role)`. The record is fixed before body checking, independent of
which resources or imports are visible. Global owner signature discovery can
collect these declaration records without loading resource bodies. An owner with
both Type and row parameters checks the same signature whether associated or
unassociated.

A resource association record is separate: defining ResourceId, exact provider
InterfaceId and EffectId, positional formal substitution, operation/method
correspondence, native interpret mapping and sealed construction origin. It is
authenticated by the defining resource declaration. Preserve P-1's
provider-interface sealing rule: a provider interface may be claimed by at most
one distinct resource declaration, and a second resource association rejects.
Separately, this candidate proposes the bounded restriction that an associated
EffectId may be claimed by at most one distinct resource declaration, even when
another claim would be type-compatible. EffectId uniqueness is a new candidate
restriction, not existing P-1 truth. It bounds association and evidence
validation for this experiment; shared-effect resource associations would need a
separately reviewed rule. This candidate adds no shared-resource authority.
Repeated imports of the same defining resource record are not new claims.
Conflicting telescopes, argument tags, slot order or canonical operation types
reject before any authority is published. A row-free owner can still be
associated where all mapped argument types agree; every row-bearing position
requires a row actual, with no inference of a new slot or implicit row
parameter.

The selected same-defining-module resource assembly remains the association
boundary. Unassociated effect/interface imports may freely expose their
independent signatures. This amendment does not add cross-module construction of
a new sealed association to an imported owner; any such future extension
requires a reviewed sealing rule. Thus generic owner applications across module
boundaries are admitted, while association authority has the existing
defining-module origin.

Body-free public summaries export complete owner signatures and a closed
dependency graph of every referenced owner, row member, type, binder role and
association fact required to check exported uses. A public resource cannot
expose an unavailable private effect/interface/type needed by that graph; reject
rather than replacing it with a spelling or opaque missing entry. A private
association still seals its exported owner against ordinary impl/with
construction; the summary retains the sealed origin and required checking facts
without exposing executable resource bodies. Imported clients need authenticated
signatures and association contracts, not handler source. Targeted imports and
reexports change lookup names only and preserve defining IDs, canonical
signatures, sealing records and authenticated dependency closure. Diamond
imports coalesce identical origins and reject inconsistent records claiming the
same defining ID.

### Inherited owner rows in generated evidence

Owner row binders are rigid in effect operations, interface method declarations
and resource-generated forwarding evidence. They are not operation-local or
method-local forall binders. A generated method type is formed under its
parent's complete rigid environment, including Rows and its lacks facts.
Method-local explicit binders retain their present exclusion of EffectRow. An
ordinary monomorphic field containing `Unit -> Unit ! {|Rows}` references the
inherited row; it is not a nested scheme or polymorphic field.

Registry method schemes must distinguish parent instantiation from independent
method-local instantiation. At a method occurrence the parent owner vector is
checked/instantiated as one complete vector, yielding substitution sigma for
Type and row slots; sigma is then applied to the method type, constraints and
field types. Any already admitted method-local binders instantiate afterward
under their existing rules. Compiler-generated parent quantification in a
body-free method scheme has role `InheritedOwner(owner-id, slot-index,
binder-id)`, even if represented by an outer binder list; it must not be
classified as a new source method-local row binder. Generated resource
forwarding evidence uses the resource's checked parent substitution and sealed
origin, not a fresh independent Rows.

In this rule `Delta_O` is the rigid environment from the authenticated owner
signature, `Delta_M` contains only existing admitted method-local binders, and
`tau` is the method's ordinary value type. Its latent rows may mention Delta_O.
The conclusion creates a registry fact, not a first-class source scheme.

```sequent
Method-Inherited-Owner :=
  signature(O) authenticates Delta_O and inherited roles
  Delta_M contains no method-local EffectRow binder
  Delta_O, Delta_M; remaining environments |- tau => Type
  constraints are well formed under Delta_O, Delta_M
  ===>
  registry-method(O, name, inherited Delta_O, local Delta_M, tau, constraints) ok
```

Imported evidence authenticates parent ID, slot kinds, role mapping, binder
scope and simultaneous substitution. A summary that relabels inherited Rows as
method-local forall, omits its argument, aliases hidden rho, or freshens it
independently of the handle/effect identity rejects. Ordinary implementation
owner row parameters are not introduced. Existing impl/with forms may consume
fully saturated ordinary row-bearing interface obligations only where their
already admitted binders and constraints can supply the actual row; they gain no
implicit EffectRow binders and cannot implement sealed resource interfaces.

### Scope and complete derivation

At resource definition, all formal binders are rigid and distinct. The first is
`R:Type`; `Rows:EffectRow` is a source owner formal. The lifecycle answer
`T:Type`, hidden clause `A:Type`, and hidden residual `rho:EffectRow` have
distinct allocation roles and identities. A reused spelling never aliases them.
Operation pattern and resume input come from authenticated instantiated
operation types.

At instance checking, resolve and check remaining row actuals and the
initializer in the preceding scope, before allocating fresh `C:Type`. Thus
`{|Delta}` cannot mention C. Then allocate C, substitute position zero with C,
and install the handle and sealed evidence only in the body. No `Delta lacks
E<C,{|Delta}>` is added because C is fresh. Input/state/answer type agreement
and identity escape checks remain mandatory.

For the positive case, the global signature checks under rigid Delta with the
existing written-row fact `Delta lacks H`. The actual substitution sigma maps R
to C and Rows to `{|Delta}`. The callback operand has `Unit -> Unit ! {|Delta}`.
The sealed diagnostic evidence method forwards a request with closed row `{E}`
where `E=ConnectionOps<C,{|Delta}>`; it does not execute the callback. `perform
H.op ()` has closed row `{H}`. Their body union is closed `{E,H}`. Exact removal
of E gives real `epsilon={H}`. This is actual body typing, not a descriptor's
claimed epsilon.

In the generic provider clause, callback application contributes `{|Rows}`.
`MissingRow` is pure Error and the owned resume consumes Error and produces
hidden A with shared output Omega. Suppressing only that resume's shared output
in direct-demand analysis leaves `D_sigma={|Delta}`. There is no native request
in this diagnostic clause. Native lifecycle effects are still interpreted at
their selected boundary, independently of this direct clause calculation. The
hidden answer is obtained by resume, not manufactured by discard.

Current principal union now gives `Omega = {|Delta} union {H} = {H|Delta}`
because Delta already lacks H. Known D members `K` are empty. Exact removal of K
leaves `r=Omega`. Specialize hidden `rho -> {H|Delta}`, not `rho -> {H}`. The
resource result wrapper is independent of C, so the result does not leak C. At a
global occurrence Delta is freshly instantiated with its preserved lack; global
definition checking remains rigid, and ordinary eligible local generalization
retains current rules.

This derivation needs no open row `{E|Delta}`. Forming that row would require
the additional fact `Delta lacks E<C,{|Delta}>`. That fact mentions Delta inside
its own exact-instance argument. Fresh C supplies no such fact. Ordinary
substitution/occurs checking must traverse it and may reject cyclic constraint
dependency. This draft does not loosen occurs checks, assume a primitive effect
has zero arguments, or create recursive lacks constraints. The positive case
avoids the intermediate row entirely. If a lowering algorithm insists on it,
that algorithm cannot implement this candidate by inventing the exclusion;
redesign lowering or return to semantic review. The independent final ordinary
exact-handler equations still must validate the proposed placement of the closed
request row and substituted clause row.

### Identity, substitution and dependency traversal

Exact effect identity is defining EffectId plus the entire ordered kinded
vector. Row slots use existing normalized row equality: known members, tail
identity and accumulated lacks facts. Hence `E<C,{H}>` and `E<C,{J}>` differ
when H and J differ; `{H,J}` and `{J,H}` compare equal after normalization. No
covariance, subtyping, argument erasure or string matching. Tail aliasing must
preserve shared identity; incompatible lacks facts cannot be discarded to make
two instances equal.

Simultaneous substitution maps every owner Type formal to a same-kind type and
each row formal to a well-formed complete row. It traverses function
domain/codomain, callback latent rows, tuple components, owner applications,
effect arguments, constraints, state/result metadata, summaries, retained demand
equations and nested lacks instances. Row-tail replacement applies existing
union, exact removal, occurs and lacks rules. Dependency traversal includes Type
variables buried inside row members' arguments and recursively nested RowArg
members. A callback type or exported result containing `E<C,{}>` depends on C
even if it mentions C only inside a row. An actual substituted row cannot
contain a forbidden exact instance; a constraint containing its own binder
through nested arguments must face the ordinary occurs check. Traversal requires
cycle-safe implementation but no new recursive type feature.

Row arguments are type metadata, not runtime states or codecs. State remains
`Native.ConnectionState<R>`; native association remains `Native.Connection<R>`
with Type argument R. Native position-zero ownership, native manifest guards and
ABI vectors do not acquire Rows. Resource/source arguments and native arguments
are related by the checked interpret mapping, not equal-length guessing.

### Elaboration, retention and authentication

Implementation requirements are consequences to review, not language authority.
A minimal representation is `KindedArgument = TypeArg(Type) |
RowArg(EffectRow)`, with a saturated ResourceApply form distinct from ordinary
Type::Application. Equivalent representations are possible if they enforce the
rules. Encoding rows as an arbitrary Type variant without an argument category
invites rows into ordinary monotypes and must prove that cannot happen.
Type-only EffectInstance argument arrays and ordinary unary Type::Application
cannot be repaired by a Boolean admission flag.

Resolution supplies canonical owner IDs, slot kinds and binder roles.
Declaration checking compiles actual clauses once. A retained body-free contract
records owner substitutions, associated operation/evidence correspondence,
hidden template roles, actual callback-demand roots, conditional D equations and
origins. Public import authentication checks complete vectors, normalization,
kinds, scopes, binder freshness, sealed declaration origin and every exported
nested dependency. A forged summary must fail even if its duplicated scalar
fields agree. Code linkage remains separately authenticated by template ID.

Specialization substitutes sigma into checked generic Core, independently
reconstructs actual captures c and real epsilon, derives principal Omega and
residual r, then solves all actual handlers, resumes and affected descendants.
No source-body replay, unresolved recipes, row holes or erased callback work may
reach final ordinary Core validation. The callback is an ordinary Core function
application; no new runtime reduction is needed. Core types and exact
request/handler descriptors must retain row-bearing identity. Closure capture,
cleanup, completion, discard ownership and interpreter topology remain
operationally unchanged.

### Required negative evidence

Each case must reject at the governing boundary, with no invented facts:

- Union ambiguity: the same executed callback and H body with Delta lacking no
  H. An annotation ending `{|Delta}` cannot justify adding H; union fails rather
  than strengthening Delta.
- Wrong slot kind: `Connection<C,Unit>` and `ConnectionOps<C,Unit>`; malformed
  RowArg includes a Type payload or an invalid/nested unbound row tail.
- Saturation: missing row actual, extra argument, unsaturated row family used as
  an ordinary constructor, EffectRow beneath a kind arrow.
- Scope: `Connection<C,{Native.Connection<C>}>` at an instance mentions C before
  its binder. Returning db or a function whose latent row contains an exact
  effect with C rejects identity escape.
- Binder roles: source Rows aliases hidden rho, hidden A aliases T, reused
  template binder, generalized fresh C, forged slot-zero identity kind.
- Identity: change only a row actual in a request or summary; equal EffectId
  does not preserve exact instance. Reject incompatible lacks, nested occurs
  cycles and inconsistent shared tail substitution.
- Demand integrity: erase actual callback demand, replace rho with epsilon,
  retain an unused relay as alleged D, or forge a demand origin. Independent
  reconstruction rejects.
- Known native work: if a variant clause performs native diagnostic, retain its
  known direct native demand before exact native interpretation removes it. No
  manifest/string flag may silently erase that demand. Such a variant is
  separate from the deliberately native-free open-D clause above.
- Summary authority: copied association, conflicting association record,
  ordinary impl of a sealed interface or fabricated evidence cannot create
  sealed resource construction/completion authority.

Also retain closed specialization cases and generic open cases, nested effect
RowArgs, Type variables inside those arguments, eligible local generalization,
callback captures and real linked execution under surviving interpreters. A
closed-only witness cannot replace the generic formal witness.

### Selected choices and remaining evidence

This amendment selects explicit complete instance actuals for mixed resource
owners, independent complete row signatures on resource/effect/interface owners,
and inherited-parent row roles in generated evidence. Association authority
retains original P-1 provider-interface sealing and adds the bounded
single-resource EffectId association rule; no association-dependent kind
admission remains. The row-aware
representation is an implementation decision still open; the semantic
tag/arity/saturation obligations are not open. The context-free tagged argument
grammar above is the proposed syntax contract. Parser diagnostics and a concrete
specification patch remain subsequent implementation preparation.

The positive derivation is a source/type design witness, not a run or accepted
test. Design and integration reviews found no contradiction in the ordinary
handler equations. Implementation evidence must still validate every final
handler-output equation for the closed-input/open-output topology without
self-containing lacks. Failure is a semantic blocker, not permission to weaken
row algebra.

Actual capture-dependent close demand `D(sigma,c)` remains conditional until
actual specialization proves c. No P-1-valid same-sigma/same-epsilon different-c
source witness is established here. Hidden-answer typing, discard consumption
and surviving interpreter topology make that a separate mandatory obligation.
The candidate does not claim this callback witness satisfies it, and it does not
allow unknown higher-order close demands to pass discard checks.

Useful SQL behavior, foreign callbacks, arenas and owner transport, general
higher-rank monotypes, partial mixed owners, row kind arrows and general
row-bearing nominals remain outside this amendment. Selection retains all
remaining evidence obligations and the later product adoption workflow.

## Selected arena contract A-0

A-0 extends the same admitted resource assembly and registration path. Its
question is whether a fixed-capacity immutable arena can admit M-01 through M-06
with actual typed native payloads, sharing, selected outer projections, explicit
copying and structural completion. It does not select retained foreign input,
mutable objects, row views, counting or tracing. X-01 through X-04 still need
their separate access contract.

### Types and evidence before syntax

The source library defines `Arena<R> : Type -> Type` through a resource
declaration and re-exports canonical `@foreign.memory` configuration, error,
reference and layout-witness families. `ArenaState<R>` is opaque provider state;
`Ref<R,T> : Type -> Type -> Type` is opaque duplicable immutable object access.
Neither exposes a constructor. `Ref` is not an arena owner and has no release
method. The instance's first parameter is fresh, and ordinary capture/evidence
facts retain every actually stored owner relationship.

The selected initializer is `ArenaConfig(payload_bytes, object_slots)`, with
both fields `Int`. This refines the earlier capacity-only input: object metadata
has an explicit bound rather than an implicit unbounded auxiliary heap. Both
counts admit zero and must fit host size/pointer-offset limits; all size
products are checked. Acquisition reserves one stable payload block aligned to
64 bytes and a fixed object-record table. A zero-capacity arena has no
dereferenceable payload but can publish zero-sized objects up to its metadata
bound.

`Layout<T>` is a sealed native interface with `witness : Unit ->
LayoutWitness<T>`. Its opaque witness is immutable independent metadata and may
be used by ordinary rank-1 helpers. This is different from provider-only state
access. The checker derives its evidence from the registered structural layout
policy and admitted nominal definitions; ordinary source `impl`/`with` cannot
forge it. An abstract T requires explicit `Layout<T>` evidence. An opaque
imported nominal needs authenticated exported layout facts/dictionary identity,
not inspection of its provider/helper body.

`ArenaOps<R>` has `usage : Arena<R> -> (Int, Int, Int, Int)`, returning used
bytes, capacity bytes, object count and object-slot limit. The following family
has ordinary fixed-kinded effect parameters, rather than operation-local
binders:

```text
StorageOps<R,T>:
  allocate_checked : (Arena<R>, LayoutWitness<T>, Int, T) -> AllocResult<Ref<R,T>>
  load_checked     : (Arena<R>, LayoutWitness<T>, Ref<R,T>) -> T

StorageProvider<R,T>:
  allocate_checked : (Arena<R>, LayoutWitness<T>, Int, T) -> AllocResult<Ref<R,T>> ! {StorageOps<R,T>}
  load_checked     : (Arena<R>, LayoutWitness<T>, Ref<R,T>) -> T ! {StorageOps<R,T>}

allocate<R,T> : (Arena<R>, T) -> AllocResult<Ref<R,T>> ! {StorageOps<R,T>}
  where StorageProvider<R,T>, Layout<T>
allocate_aligned<R,T> : (Arena<R>, Int, T) -> AllocResult<Ref<R,T>> ! {StorageOps<R,T>}
  where StorageProvider<R,T>, Layout<T>
load<R,T> : (Arena<R>, Ref<R,T>) -> T ! {StorageOps<R,T>}
  where StorageProvider<R,T>, Layout<T>
```

The library's ordinary helper bodies obtain the witness from `Layout<T>` and
call the exact associated methods. `allocate` passes alignment zero, meaning the
natural layout alignment; `allocate_aligned` passes its checked request. The
interface's methods exactly match the operation value types, adding only the
associated result row, so current forwarding evidence applies. There is no
method-local constraint syntax, universal `ArenaOps<R>` allocator, inferred
nearest-arena construction or rank-2 source callable hidden in these schemes.

Native lifecycle effect `Native.Arena<R>` has `acquire : ArenaConfig ->
Acquire<ArenaState<R>, ArenaInitError>`, `usage : ArenaState<R> ->
(Int,Int,Int,Int)` and `finish : ArenaState<R> -> Finish<ArenaState<R>,
ArenaFinishError>`. Its owner argument is position 0. `Native.Storage<R,T>` has
borrowed operations `store : (ArenaState<R>, LayoutWitness<T>, Int, T) ->
AllocResult<Ref<R,T>>` and `load : (ArenaState<R>, LayoutWitness<T>, Ref<R,T>)
-> T`. Native signatures do not mention source `Arena<R>`. The first arena
finisher always consumes the block/table and returns consumed success; a
violated internal invariant is terminal, not an invented refused-free outcome.

Canonical independent data shapes are:

```text
type ArenaConfig = ArenaConfig(Int, Int)
type ArenaInitError = InvalidArenaConfig
| ArenaAllocationFailed
type ArenaFinishError = ArenaFinishInvariant
type AllocError = OutOfPayload
| OutOfObjects
| InvalidAlignment
| InvalidPayload
type AllocResult<T> = Allocated(T)
| AllocationRefused(AllocError)
```

The impossible source finish error family remains a kind-`Type` argument of the
shared report; its constructor is never emitted by the admitted finisher.
Recoverable payload/object-limit refusal returns prepared independent error
data. Internal runtime work/heap/activation exhaustion remains terminal.
Capacity is not increased and operations are not retried implicitly.

### Layout and publication

Witnesses describe a private native serialization, not a C ABI for arbitrary Ash
data. Admitted rules are:

| Payload | Encoding and natural alignment |
| --- | --- |
| `Unit` | Zero bytes, alignment 1. |
| `Bool` | One byte 0/1, alignment 1. |
| `Int` | Eight-byte signed integer, alignment 8; values outside signed-64-bit range refuse allocation. Ash integers elsewhere retain arbitrary precision. |
| Registered byte data | Checked length header and bytes, alignment 8; all byte values fit `[0,255]`. |
| `Ref<A,T>` | Two private 64-bit owner/object identities, alignment 8; the target payload T is not recursively inlined. |
| Tuple | Fields in source order with checked alignment padding; maximum field alignment. |
| Ordinary nominal data | Sole-constructor payload may omit a tag; multiple constructors store a checked tag then the selected fields with padding. The by-value nominal layout graph must be acyclic. |

Layout dictionaries are finite graphs keyed by type/layout IDs; a reference edge
does not expand its target layout. By-value recursive nominal types are
unsupported, even when one input value happens to be acyclic. Registered byte
data has a dedicated dynamic-length codec, so its ordinary list representation
is the explicit exception. Acyclic admitted ordinary values encode recursively,
duplicating ordinary shared inline fields. Arena reference fields preserve their
object identities and never copy target payloads. State tokens, resource access
families, functions, evidence and arbitrary native opaque families have no
derived payload layout. A capturing closure may still live in ordinary storage
and retain an arena reference. A closure-as-payload rejection is a layout
limitation, not evidence of owner-escape checking.

The alignment operand is zero or a power of two at least the natural alignment
and no greater than 64. Unsupported alignment, value conversion and all
arithmetic checks precede reservation. For cursor c, size n and admitted
alignment a, compute `start = align_up(c,a)` and `end = start+n` with checked
arithmetic; require `end <= payload_bytes` and an available object record.
Padding counts against payload capacity. Metadata does not count as payload
bytes.

Native initialization and reserved reference/result metadata complete before
publication. A failed conversion, initializer or runtime admission publishes no
reference and leaves the cursor/object count unchanged. Writes to an unpublished
reservation cannot touch earlier objects. If initialization fails after writing
the reservation, roll back its cursor/record and dispose partial temporary
state; do not publish a partially initialized object. Published objects never
move or mutate. Zero-sized allocations still get distinct object IDs/records,
preventing address coincidence from becoming identity.

The native table stores offset, extent and authenticated layout identity for
each object; payload bytes hold the actual encoded fields. Holding an ordinary
heap copy while returning a fabricated immediate is not allocation evidence.
Encoding and decoding scratch uses existing finite runtime work/storage budgets
and is measured separately; A-0 promises a bounded arena block/table, not an
allocation-free codec or fixed capacity for every ordinary Ash heap allocation.

### Family coverage and module contracts

While checking the arena body, admit a provisional descriptor-backed
`ScopedEvidenceFamily` with the rule `forall U. Layout<U> =>
StorageProvider<R,U>`, tied to this exact live R and the checked family template
ID. This is a new evidence-selection branch; current exact lexical evidence
alone cannot solve that universal family goal. After the existing
determination/unification gate makes a goal complete and inference-free,
selection tries current abstract requirements, exact current evidence and exact
lexical evidence in their current order, then the unique eligible scoped family,
then ordinary concrete implementations. Source concrete implementations for this
sealed interface remain prohibited.

Family matching may instantiate only its bound U from the fixed goal; it cannot
solve/refine goal variables or guess a layout. Solve `Layout<U>` from an
explicit abstract requirement or the admitted structural layout derivation.
Record the exact provider goal, effect instance, witness proof, template ID and
current owner in the finite demand collector before constructing provisional
forwarding evidence. An absent/ambiguous layout or multiple eligible family
sources rejects; there is no fallback fabrication. Ordinary aliases/imported
helpers preserve the selected evidence-family origin and demanded instance in
their summaries.

After body checking, close the demand set from evidence selections, exact rows
and contextual callable/request summaries; discharge/instantiate exactly those
handlers and validate every layout and authority relation before publishing
checked Core. Failure or work exhaustion drops the entire provisional result.
Thus provider evidence is available when `allocate (arena,42)` is checked, while
final executable handlers remain finite. Scanning already published Core to
discover evidence required to check that same Core would be a circular algorithm
and is not A-0.

Arena assembly adds a declaration-level family template under rigid payload T
and a `Layout<T>` requirement. It covers the exact `StorageProvider<R,T>`,
`StorageOps<R,T>` and `Native.Storage<R,T>` association uniformly. The family
handlers are checked once with those rigid parameters, layout evidence and the
same hidden answer/continuation-row binders as P-1. The result remains typed
generic template Core, not a source polymorphic handler value. A requested
specialization supplies type arguments and its authenticated layout dictionary,
then instantiates ordinary exact handlers and forwarding evidence. No individual
operation acquires a type binder.

Known effect members, selected provider evidence and authenticated helper
summaries give a finite demand set. After unification, each `StorageOps<R,U>`
demand is covered by exactly one family and a justified `Layout<U>` witness.
Abstract U is valid with its caller-supplied dictionary; no concrete layout is
guessed. Demand discovery includes captured callable/evidence operation
metadata, not only the body's immediate outward row. Distinct specializations
retain exact effect arguments and lexical activation substitution through
generic/imported helpers. Ambiguous/overlapping families reject. All family
matching, retained demands, dictionary construction and specialization charge
existing finite work ledgers.

Only explicitly established exact instances discharge from the body's row.
Unrelated open tails pass outward unchanged with their existing lacks facts.
Each retained tail/demand contract records either a finite exact demand set, a
justified exclusion for this owner/family, or unknown coverage. Freshness may
justify exclusion for a tail fixed in the preceding scope; it does not justify
excluding a tail created inside the arena body. An unresolved tail or unknown
higher-order demand that could require an uncovered instance produces a coverage
ambiguity; the checker never removes an entire family by name or invents row
exclusions. These are authenticated demand/owner facts, not a new assumption
that the current row algebra already has universal family lacks constraints. A
generic helper with explicit `StorageOps<R,T>` and `Layout<T>` contracts remains
usable. Public body-free summaries preserve demand templates, layout
requirements, result relations, retained-owner preconditions and control
obligations; linked executable template code is a separate requirement.

The spelling comparison adds one `family<T> where Native.Layout<T>` block to the
resource declaration, containing provider/effect/interpret fields and handler
templates. The exact ordinary family contracts above govern it. The same
resource has its non-family `ArenaProvider<R>`/`ArenaOps<R>` usage handler and
`Native.Arena<R>` lifecycle interpretation. Multiple associated groups are an
explicit A-0 declaration extension; P-1's single-group grammar does not already
express them. Implement that grammar only after the family contract is reviewed.

The selected family-block production is inserted between the outer declaration's
`interpret` field and its acquire clause. A-0 permits one kind-`Type` payload
parameter and its exact sealed layout requirement; the hidden answer/row binders
remain distinct even when a source answer binder has the same spelling.

```ebnf
provider_family ::=
  "family" type_parameters where_clause "{" line_end
  "provider" interface_application line_end
  "effect" effect_instance line_end
  "interpret" effect_instance line_end
  "handlers" identifier "{" line_end
  handler_clause { line_end handler_clause } [ line_end ]
  "}" [ line_end ] "}" ;
```

The corresponding typed arena assembly is:

```text
pub resource Arena<R> {
input Native.ArenaConfig
state Native.ArenaState<R>
result Provider.Scope<Native.ArenaInitError, Native.ArenaFinishError, T> for <T>
provider ArenaProvider<R>
effect ArenaOps<R>
interpret Native.Arena<R>
family<T> where Native.Layout<T> {
provider StorageProvider<R,T>
effect StorageOps<R,T>
interpret Native.Storage<R,T>
handlers state {
allocate_checked operand => match operand {
(arena, layout, alignment, value) => resume (perform Native.Storage<R,T>.store (state, layout, alignment, value))
}
load_checked operand => match operand {
(arena, layout, reference) => resume (perform Native.Storage<R,T>.load (state, layout, reference))
}
}
}
acquire config => perform Native.Arena<R>.acquire config
finish state => perform Native.Arena<R>.finish state
handlers state {
usage arena => resume (perform Native.Arena<R>.usage state)
}
}
```

Generated handler entry authenticates each `arena` access operand against the
current R before the clause uses its native state. Witness T and reference R/T
must match the exact demanded instance and the object's registered layout. Store
maps its ordinary canonical `AllocResult` unchanged. Usage returns an
independent copied tuple. Load retains its payload relation rather than
declaring all generic results independent. A source library may add explicit
policy/error mapping without altering those authority and dependency facts.

### Payload relations, storage and copying

For a successful store, retain the relational summary `ObjectRef(owner R,
allocation site, payload shape S)`. S is the actual input value's shape,
including selected aggregate fields, aliases, reference targets, callable
dependencies where supported and symbolic argument relationships. Failed store
branches contain independent `AllocError` and no object access. Generic helpers
preserve this relation as a substituted public value contract. An opaque
external-result `Unknown` summary loses the relation and cannot prove M-03.
Concrete runtime object IDs remain distinct even when static summaries join
repeated activations of one allocation site.

The store/load relation belongs to the selected checked provider/native
interpretation, not to an operation spelling or value type universally. Ordinary
exact source overrides retain lexical precedence. Their actual clause results
determine the relation: an override returning an earlier Ref preserves that
earlier object's payload summary rather than pretending to store its new
operand. Public generic helper summaries therefore retain contextual request
relations and exact interpreter requirements until handler selection is known.
An unknown override is conservative unknown behavior, not permission to use the
native result contract. Independent validation checks this selection as well as
the operand/result relation. Source overriding does not authorize native storage
publication or reference fabrication.

An actual native store requires every retained payload owner to be the
destination owner or an
owner whose lifetime encloses the destination's lifetime. Thus B may hold refs
to enclosing A, and B may hold earlier B refs; A cannot store B-dependent data.
This precondition is checked from actual value/capture summaries, not inferred
from a nominal type alone. A generic store helper retains the conditional owner
precondition for checking at each actual call; it does not assume unknown T is
independent. The helper retains a contextual pending
`NativeStoreSafety(destination, payload)` obligation, discharged when selection
chooses the native family interpretation and supplies the actual payload owners.
A source override that ignores its argument and returns an earlier reference
uses its actual clause obligations; it does not inherit a native-store
precondition for a value it never retains. An override invoking another native
store inherits that actual store's containment obligation. With immutable
storage there is no later remove/mutate operation
that could justify temporary inward references.

Load verifies exact owner/object/layout identity and copies encoded inline data
into an ordinary value of T, recovering S. It does not automatically attach the
container owner's dependency to every field. Scalars copied from B are
independent; embedded `Ref<A,T>` remains dependent on A; embedded B refs keep B.
For M-03, a B object containing `(refA, refB)` loads to an ordinary tuple with
field-sensitive summaries. Selecting `refA` yields A only, so it can survive B
while A remains live. Returning the entire tuple, B ref, or a closure capturing
B still rejects. Independent Core validation rederives store/load relations from
the registered contracts and checked operands.

Ref tokens retain owner/object identity and no ownership keepalive; they cannot
extend their source arena's lifetime. Aliases preserve object identity and
allocate no payload. Immutable persistent structures may share refs arbitrarily
while their owners remain live. Unbinding an alias performs no individual free.
Bulk completion frees the arena once, including unreachable objects; it does not
trace roots or scan destructors. Immutable construction has no forward-reference
publication, so cyclic shared graphs remain a named construction question rather
than an admitted test result.

Deep copy is explicit source code with an explicit output type. For example,
`copy_node<A> : (Arena<A>, Ref<A,Node>) -> Node ! {StorageOps<A,Node>}` loads
the reference-free node. A shared pair of A-node refs can become a pair of
ordinary Nodes through two loads, or two independently allocated B nodes plus a
B pair. Its output type names Node/recipient-B references rather than A
references. Source signatures retain every exact source/read and recipient/store
effect and provider/layout requirement. This avoids assuming a nonexistent
`EraseRefs<T>` type function or calling a shallow `T -> T` conversion
independent. The first deep-copy routines duplicate shared payloads and record
allocations, bytes copied and duplicate work. General cyclic copying and
preserving sharing through an identity map require another bounded contract.
Shallow load/copy continues to retain any reference fields and fails the
corresponding escape test.

### Completion and M-01 through M-06

No object/ref binding owns a completion action. `cleanup` supplies separately
checked ordinary actions, which may capture refs and request the exact storage
instances. Their contracts and interpreter requirements follow current cleanup
analysis, extended to the generated family handlers. All such inner actions run
while their arena storage and selected interpreter remain live, before the
synchronous arena finisher reclaims payload/table storage.

Capture moves the arena owner, native state, exact instantiated handlers, layout
dictionaries and pending action obligations together. Resume restores them
without reallocation or duplication. Owned discard runs admitted inner actions,
then consumes the arena state once; it cannot skip an outside required action or
discard a running action/finisher. Internal teardown uses safe native
destruction without executing source cleanup as recovery. Divergence retains its
ordinary lack of eventual-release guarantee.

M-01 records exact layouts, payload/object limits, alignment and rollback. M-02
observes one node payload through aliases, a shared persistent structure and a
capturing closure called twice; escaping that closure rejects. M-03 uses the
store/load relation for its safe outer projection and inward-store rejection.
M-04 compares explicit independent and shallow copies, including recipient-B
storage and declared sharing duplication. M-05 repeats scratch scopes and checks
payload/table reclamation, while owner-plus-object packaging and counting an
owner past scope reject. M-06 retains an action reading arena-backed data and
checks normal/capture/resume/owned-discard order against actual native events.
None of these checks runs stale pointers as a negative test.

## Resource type definition

This general schema explains the candidate roles. P-1 selects controlled
publication without a source `publish` function and controlled lifecycle replies
as specified above; alternatives in this study are not additional authoring
features admitted by that slice.

The declaration and instance occupy different source positions. A resource type
definition introduces a family `Q<r, alpha>`. Its formal identity parameter `r`
has kind `Type`; `alpha` denotes any other ordered parameters with declared
kinds. The family has the corresponding function kind ending in `Type`. At an
instance, `r` is replaced by a fresh rigid identity `R`. Other parameters come
from the surrounding typing environment and ordinary inference.

The proposed value type of a bound resource access is `Q<R, alpha>`. Its values
are non-owning handles; the lexical scope owns completion. A declaration must
identify its provider implementation `P` and connect the following types and
contracts under the same parameter environment:

| Component | Required typed relationship |
| --- | --- |
| Initializer | A value type `I<alpha>` known before the new identity exists. |
| Provider state | A private representation `State<r, alpha>` with declared retained dependencies and owned completion. |
| Acquisition | Code accepting `I<alpha>` and producing either guarded `State<r, alpha>` or an initialization error. Failed acquisition publishes no handle or authority. |
| Publication | Controlled construction of `Q<r, alpha>` from acquired state, with its exact authority. The handle is access, not ownership of the state. |
| Effect interface | Declared operation types whose resource operands and results refer to the appropriate `Q<r, alpha>` and associated types. |
| Handlers | Clauses checked against those instantiated operation types under the provider state and current resume rules. Their outward effects remain explicit. |
| Completion | Code consuming owned state or retaining it with a failed-completion report, according to its declared postcondition. It cannot silently duplicate ownership. |
| Scope result | A specified type family `F<T, alpha>` for a body result `T` and acquisition/completion reports, with no reference to the closing identity. |

`I`, `State`, and `F` are type templates in the definition, not identifiers
injected into client code. The definition must resolve actual declarations and
check their kinds and signatures. Initializer, acquisition, publication,
handler, and completion effects also belong to that contract.

For example, the following are internal provider contract shapes at one fresh
identity, written as type notation rather than proposed declaration syntax:

```text
acquire : I<alpha> -> AcquireResult<State<R, alpha>, InitError<alpha>> ! epsilon_acquire
publish : State<R, alpha> -> Q<R, alpha> ! epsilon_publish
finish  : State<R, alpha> -> FinishResult<State<R, alpha>, CloseError<alpha>> ! epsilon_finish
```

`AcquireResult` distinguishes acquired state from failure; unpublished partial
state remains guarded. `FinishResult` distinguishes consumed state from retained
state after refusal. These owned states belong to establishment and completion,
not transportable client results. Publication borrows the owned state to
construct access; it does not consume or transfer the scope's owner.

These signatures do not by themselves prove ownership or foreign memory safety.
Their controlled calling positions, construction authority, state usage, and
postconditions require checking rules. Current ordinary rank-1 functions and
interface evidence do not establish them. A declaration with an arbitrary
`publish` function cannot claim authority merely because its result type
matches. The experiment must specify which obligations Ash checks, which need
trusted primitives, and which remain explicit assumptions about foreign code.

A handler also has a precise checking context. For an associated operation `op :
D<R, alpha> -> B<R, alpha>`, its clause pattern binds `D<R, alpha>` and its
resume capability accepts `B<R, alpha>`. The clause must produce the shared
handled result type with the declared outward row, following current handler
checking. `Q<R, alpha>` is the resource operand type, not the handler's type.

Imports must preserve the resource family's defining identity, parameter kinds,
provider association, operation identities, construction authority, and result
contract. Copying a type or effect declaration cannot recreate resource
construction authority. Provider declaration syntax and public-summary encoding
remain to be designed around these obligations.

## Typed instances for the two experiments

The following names denote candidate library declarations, not current builtins.
They must be supplied by actual resource, data, effect, and provider definitions
before source fixtures can use them.

| Resource family and kind | Initializer type | Bound value type | Required owner relationship |
| --- | --- | --- | --- |
| `Sqlite.Connection : Type -> Type` | `Sqlite.OpenConfig : Type` | `db : Sqlite.Connection<C>` | Fresh `C`; state owned by the connection scope. |
| `Sqlite.Statement : Type -> Type -> Type` | `(Sqlite.Connection<C>, Sqlite.SqlText)` | `stmt : Sqlite.Statement<S, C>` | Fresh `S`, existing live `C`; statement state retains `C`. |
| `Memory.Arena : Type -> Type` | `Memory.ArenaConfig`, with byte capacity and object slots | `arena : Memory.Arena<A>` | Fresh `A`; its backing storage remains owned by the arena scope. |

For the statement definition the formal parameters are its own identity and its
connection identity. An initializer containing `db : Sqlite.Connection<C>` fixes
the second parameter to `C`. Only the first parameter is freshly introduced as
`S`. The provider cannot substitute another connection or infer ownership from a
raw address. SQL input retention and copying need their own operation contracts;
nesting does not establish those facts.

A candidate statement effect interface can use current operation-type shapes:

```text
StatementOps<S, C>:
  bind_int   : (Sqlite.Statement<S, C>, Int, Int) -> Sqlite.Result<Unit>
  step       : Sqlite.Statement<S, C> -> Sqlite.StepResult
  column_int : (Sqlite.Statement<S, C>, Int) -> Sqlite.Result<Int>
```

Here `Sqlite.Result<T>` is an ordinary success/error data family and
`Sqlite.StepResult` distinguishes a row, completion, and failure. Each operation
has one outer pure arrow, as required by current effect declarations; a request
adds the exact `StatementOps<S, C>` instance. Checked provider methods request
that instance. A handle indexed by another `S` or `C` does not match its operand
type. Runtime checks guard dynamic indices and row state unless a separate
protocol-evidence design establishes those facts statically.

Connection acquisition and statement preparation still need typed foreign
primitives, initialization guards, and declared outward effects. The connection
definition must supply the authority required to prepare under `C`. Its
associated effect interface should contain the operations actually needed; no
connection effect or constructor is introduced merely by naming the type. The
scope report type must preserve body outcomes and completion reports, including
consumed versus retained state. P-1 selects the `Scope` and `Completion` algebra
above; it does not assume a flattened `Result<T>` wrapper.

For the arena, introduce an ordinary payload type `Memory.Node` containing an
integer and a scoped access family `Memory.Ref : Type -> Type -> Type`. A
bounded first interface can have these operation types:

```text
NodeArenaOps<A>:
  allocate_node : (Memory.Arena<A>, Memory.Node) -> Memory.Result<Memory.Ref<A, Memory.Node>>
  read_value    : (Memory.Arena<A>, Memory.Ref<A, Memory.Node>) -> Int
```

`allocate_node` publishes a typed reference only after allocating and
initializing a node. The reference depends on `A`; aliases preserve that
relationship. `read_value` copies the node's integer field, whose independent
result can escape. A closure retaining the reference remains dependent on `A`
even if its exposed function type is `Unit -> Int`. Use M-02 to test that
capture and M-04 to test copying larger admitted values. An immediate `41`
without an allocated node is insufficient allocation evidence.

This monomorphic interface cannot establish a general arena. For allocation of
arbitrary admitted `T`, an intended method shape is:

```text
allocate<T> : (Memory.Arena<A>, T) -> Memory.Result<Memory.Ref<A, T>> ! {Allocate<A, T>}
```

A current effect operation has no operation-local type parameters. An effect
`Allocate<A, T>` can put `T` in its declaration parameters, but a current
handler covers one exact instance. The resource definition would then need to
express and check coverage for each admitted `T`, and discharge precisely those
instances. Alternatively, a new operation or handler typing rule must account
for that polymorphism. Neither follows from writing `allocate<T>` or removing an
imaginary universal `ArenaOps<A>` row. This is a design question to resolve
before heterogeneous allocation cases, not a limitation to hide behind a helper.

Bytes, native layout, result views, and retained foreign inputs require
similarly explicit type and dependency contracts. Their library representations
and access rules are not supplied by the acquisition syntax.

## Instance typing and lexical lifetime

Let `Q` be a resource family with an admitted definition and inferred outer
parameters `alpha`. The initializer checks as `I<alpha>` in the preceding
environment. A fresh rigid `R` then instantiates the definition, binds `x : Q<R,
alpha>`, installs the exact checked authority and handlers, and owns completion
within the lexical body. `R` and `x` are unavailable to the initializer. Every
RHS term name resolves to an existing binding.

For this comparison, `O_R` is the finite set of exact effect instances installed
by that definition at `R`. A generic-family coverage rule is not assumed. Write
`GAMMA_Q(R, x)` for the preceding environment extended with the fresh type
binder, `x` at its instantiated resource type, and the admitted authority. `d_i`
and `d_b` are inferred dependency summaries for initializer and body. `d_state`
records the initializer dependencies actually retained by the provider. It must
follow checked construction and explicit foreign contracts, rather than assuming
that all initializer dependencies vanish or survive.

The rule below is conditional on an admitted definition. For its first reporting
profile, extra report data consists of independent copies, so it adds no owner
dependency to the body result. `F` and the footprint rows must be specified
before applying the rule to an actual provider.

```sequent
T-Resource-Instance-Candidate :=
  Q has a checked definition with input I, result family F, and provider P
  GAMMA; Owners |- initializer => I<alpha> ! epsilon_i [deps = d_i]
  R is fresh and absent from GAMMA, alpha, and I<alpha>
  P retains d_state from d_i, and those owners remain live
  GAMMA_Q(R, x); Owners + owner(R, d_state) |- body => T ! epsilon_b [deps = d_b]
  epsilon_out = epsilon_i union epsilon_acquire union epsilon_publish union epsilon_handlers union epsilon_finish union (epsilon_b minus O_R)
  F<T, alpha> has kind Type
  R does not escape in T, F<T, alpha>, epsilon_out, d_b, schemes, or evidence
  body satisfies the provider's checked capture and completion obligations
  ===>
  GAMMA; Owners |- Provision(Q, P, R, x, initializer, body) => F<T, alpha> ! epsilon_out [deps = d_b]
```

The initializer's type determines the expected input, not the handle's type. The
body receives the new resource type and authority only after successful
establishment. The rule removes the body's installed exact instances and retains
all outward acquisition, publication, handler, and completion effects. Union and
removal need the current row/lacks checks; uncertain open rows are not silently
closed. A direct outward request from a handler cannot be erased by its name.

The escape premise includes actual captures and operation/evidence metadata; an
identity-free result type alone is insufficient. The output preserves live outer
dependencies. Capture, resume, and admitted discard use the existing resource
analysis extended for the definition's stated obligations. The rule cannot stand
in for the missing checker of arbitrary provider code.

Concrete type consequences include:

- `config : Sqlite.OpenConfig` can initialize a connection; an `Int` cannot.
- `(db, query) : (Sqlite.Connection<C>, Sqlite.SqlText)` can initialize a
  statement under live `C`; its bound type is `Sqlite.Statement<S, C>`.
- `ArenaConfig(capacity, slots)` can initialize A-0; its integer range and
  native
allocation failure remain runtime outcomes, not successful-acquisition facts
inferred from the field types.
- An independent integer can leave its scope. A reference or closure retaining
  the closing identity cannot, including when the dependency is hidden from
its exposed type.

## Surface forms derived from those roles

The instance form refers to a defined resource type. It does not name the
provider independently; the definition supplies that association. Retain the
following acquisition grammar only as a comparison for the typed boundary above.
The selected declaration grammar is given separately in P-1.

```ebnf
experimental_acquisition ::=
  "resource" resource_type_reference "<" upper_identifier ">" identifier
  "=" primary_expression block ;
resource_type_reference ::= upper_identifier [ "." upper_identifier ] ;
```

`primary_expression` and `block` reuse the current [syntax
grammar](../../../spec/syntax.md). A primary expression includes a literal, term
reference, parenthesized expression or tuple, and the existing primary forms
such as `perform`, `hook`, and `cleanup`. It is a syntactic category, not a type
or a purity requirement. For example, `config` and `(db, query)` can occupy the
initializer position directly; a function call `make_config ()` must be grouped
as `(make_config ())`, and `capacity + 16` as `(capacity + 16)`. This inherits
the current resource initializer convention. Whichever form is used must still
check against the resource definition's input type `I<alpha>` and retain its
inferred effects and dependencies.

The reference resolves to a resource type declaration, with its contract, in the
current or imported type namespace. `<R>` introduces the instance's owner binder
rather than applying a constructor to a preexisting type variable. Remaining
parameters, such as a statement's connection identity, must be inferred from
checked inputs; an undetermined parameter needs a designed annotation or an
ambiguity rejection. In particular, spelling `Statement<S>` here would bind
`stmt : Statement<S, C>`, not partially apply its type constructor.

Compare this explicit body with a resource binding covering the remainder of its
enclosing lexical block, following current `let` conventions. Both need the same
initialization order, identity scope, typing, and completion boundary.
Declaration and instance syntax must be documented separately. Resource
interfaces should reuse current effect declarations and handler checks where
possible; provider assembly may use explicit components or a checked packaged
form. Compare their types before judging their spelling or brevity.

The earlier `resource Provider<R> ...` explanation confused the type reference
with its associated provider. The earlier copying helpers also hid allocation
and protocol obligations. They are not proposed APIs. Complete source examples
must include declarations, resolved RHS expressions, inferred or explicit types,
operation requests, handler contracts, and failure branches before becoming
implementation fixtures.

## Elaboration and validation

The proposed resolved instance retains the defining resource identity, admitted
provider association, instantiated outer parameters, fresh owner binder, access
binder type, exact provided operation instances, result relation, and origins.
For discussion use the conceptual Core shape `Provision(Q, P, R, x, initializer,
body)`. It may generalize the existing `Resource` carrier or elaborate to
existing nodes where their checks suffice; a new node is not selected just to
mirror a spelling.

This is an extension of Ash's existing Effect dialect and evaluator. The
validator must independently check the definition/instance relation, parameter
kinds, initializer and binder types, exact effects, dependencies, result
wrapper, control obligations, and origin. Transforms must preserve those facts.
Neither spelling nor raw native addresses can reconstruct the authority.

Foreign invocation requires declared effects and explicit interpretation in the
existing execution path. Passive imports do not initialize a library or install
an interpreter. The current empty entry-row rule still applies unless a separate
proposed change explicitly modifies it. The experiment must resolve the host
entry boundary before claiming that its foreign example checks and runs.

## Program-lifetime resources remain open

Lexical instance typing does not define global resources. Program-lifetime
ownership needs decisions about identity scope across modules, initialization
order, publication, failure, associated handlers, and shutdown. Passive imports
currently perform no initialization. Do not infer a global-resource mechanism by
extending a lexical lifetime or moving acquisition into a module declaration.
SQLite's host-wide library initialization is also distinct from one connection's
lifetime. These questions remain open; the lexical experiment does not settle
them.

## Core transition sketch

This initial sketch shows configuration-first guarded entry. P-1's selected
acquire/finish templates and failure/report transitions above complete its first
slice; `acquire_P` abbreviates executing checked Ash code under the registered
foreign interpreter, rather than a library-specific resource runtime.

The copying fragment uses configuration `CONFIG(H, Sigma, env, e, K, W, t)`:
ordinary heap H, owned provider states Sigma, environment env, expression e,
explicit continuation K, contracted foreign world W, and observation trace t.
`a` is a fresh activation; `P` denotes the resolved provider contract. The trace
is evidence, not a source API.

`Q` is the resolved resource type definition; `P` is its checked, instantiated
provider association. `PROVISION_INIT` retains both, the fresh source identity
binder, handle binder, body, and preceding environment. `OWNER` records one
acquired state and its completion obligation. These are proposed machine frames;
other existing frames retain their ordinary behavior.

The rules below compare config-first entry with publication after successful
acquisition. `acquire_P` is a contracted host interaction, not a proof of C
execution. Its successful reply has completed guarded initialization. The
publication operation is fallible: if it fails after acquisition, the guard must
retain disposal authority and the failure must record whether disposal
completed. That failure branch needs an explicit rule before implementation.

```sequent
family candidate-provision-entry:
  E-Provision-Config :=
    ===>
    CONFIG(H, Sigma, env, Provision(Q, P, R, x, config, body), K, W, t) -> CONFIG(H, Sigma, env, config, PROVISION_INIT(Q, P, R, x, body, env) :: K, W, t)

  E-Provision-Publish :=
    acquire_P(v, W) = Acquired(state, W_1)
    a is fresh
    publish(Q, P, a, state, R, x, env_0, Sigma) = Published(env_1, Sigma_1)
    ===>
    CONFIG(H, Sigma, env, v, PROVISION_INIT(Q, P, R, x, body, env_0) :: K, W, t) -> CONFIG(H, Sigma_1, env_1, body, OWNER(Q, P, a) :: K, W_1, t ++ acquired(a))
```

The first rule evaluates configuration exactly once before either binder is
available. The second installs acquired authority and its owner together. A
refused acquisition runs no body and publishes no authority; its wrapper outcome
and effects of prior config evaluation must be specified separately.

The remaining families must be defined against each selected contract:

| Family | Required premises and postconditions |
| --- | --- |
| Request selection and invocation | Exact identity and source-handler precedence, checked operand, live owner, compatible active access, and the foreign operation's state transition. |
| Arena allocation | Valid size/alignment arithmetic, sufficient remaining space, complete initialization, and publication of a typed access dependent on the owner. |
| Copy and alias | Aliases retain identity and dependencies; independent copies follow a defined value relation and new ownership, with failure handled before publication. |
| Return and close | Save body outcome, complete dependents/actions in valid order, and preserve whether native close consumed or retained authority. |
| Capture/resume/discard | Preserve actual owned state and access obligations across capture; restore without duplication; abandon only admitted owned completion. |
| Internal failure | Distinguish failed source completion, unpublished guards, and host teardown. Retain incomplete cleanup status rather than invent source recovery. |

No borrowed-access transition has been settled by these entry rules. Before the
access slice, define validity intervals and conflicting operations in the
checking invariant. Determine whether facts erase, remain in native or evaluator
state, or arise from runtime validation. A view's validity is not derived only
from the owner's presence in Sigma.

## Initial trace expectations

These are intended comparisons to derive from the completed rules. The notation
is descriptive event order, not executable Core or a proof of native behavior.

```text
S-01:
evaluate config -> acquire C -> prepare S under C -> bind 42
-> step(Row) -> copy integer 42 -> step(Done)
-> finalize S -> close C -> deliver independent 42

M-03:
acquire A -> allocate outer node -> acquire B
-> allocate tuple(ref A, ref B) -> project ref A
-> close B -> use ref A while A is live -> close A

X-01:
acquire A -> allocate bytes -> acquire C -> acquire S dependent on C
-> retain A bytes in S -> execute -> relinquish retained access
-> finalize S -> close C -> close A
```

The negative S-01 variant must reject use after S completion; M-03 must reject
the B projection after B completes; X-01 must reject premature storage release
or conflicting mutation. Core traces and native observations should agree on
their shared events without claiming that every native internal allocation is
represented in Ash Core.

## Correspondence and next decisions

Run source fixtures through Ash's existing modular driver, retaining parse,
resolution, typing outcome, Core form, validator outcome, and derived trace.
Compare actual native results and completion order against that trace. The
safety argument states its trusted host contracts and needs
preservation/progress for the admitted fragment; it is not inherited from a host
wrapper or an unrelated continuation model.

P-1 selects acquisition refusal/publication failure, completion reporting,
host-effect interpretation and the initial arena layout/zero-sized policy above.
Verify those choices against the cases. Settle retained access, invalidation,
branch joins and captured obligations before their source slice. Extend this
document when a bounded decision is made, preserving rejected alternatives and
motivating cases.

Any proposed change to current surface syntax, elaboration, or Core operational
semantics belongs in the later semantic delta and accepted product proposal.
Until then, the normative specification remains the comparison baseline.
