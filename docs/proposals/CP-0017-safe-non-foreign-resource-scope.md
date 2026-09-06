# CP-0017: Safe Non-Foreign Resource Scope

- ID: `CP-0017`
- Status: accepted
- Related: [DN-0028](../design/DN-0028-effect-ash-milestone-plan.md),
  [DN-0027](../design/DN-0027-effect-ash-program-design.md),
  [DN-0026](../design/DN-0026-effect-ash-resource-first-milestones.md)

> This proposal is not current Ash. The user approved one mutable cell per
> acquisition, scope-owned release, reusable access while live, and rejection
> of resource-dependent escape on 2026-09-06, with autonomous implementation.
> This capsule specifies that bounded contract and its required evidence.

## Current behavior

The milestone branch has module/local newtype, exact lexical interface
evidence, exact effect rows and handlers, and checked discard. Ordinary values
and their stored closure captures are unrestricted. A local newtype name cannot
escape in an exposed computation, but an identity-free closure can retain its
ordinary representation. That rule is not resource lifetime checking.

Discard checks request-carried continuation obligations, including restored
control and skipped completion outside a captured segment. It invokes no
cleanup. There is no acquired resource, runtime acquisition identity, resource
access value or provider authority. The milestone is not integrated into main.

A prerequisite defect also needs correction: execution erases a generic
helper's type arguments before matching `E<T>` against its caller's `E<Int>`
handler. This accepted source reaches `runtime.invalid-control-state`; an
otherwise equal monomorphic helper observes its handler result. Returned
requesting closures have the same defect. The dynamic specification's blanket
type-erasure account must distinguish pure erasure from the instantiation
metadata needed to match effect identities. Resource activation identity builds
on that corrected execution boundary, not on a name-based matching exception.

## Proposed behavior

### One sealed cell API

`import @builtin.cell as Cell` imports one compiler-owned module. Ordinary
qualified, targeted and public name imports preserve its defining identities.
The compiler supplies exactly these public names:

| Name | Contract |
| --- | --- |
| `Handle<R>` | Opaque kind `Type -> Type`; an unforgeable cell access value. |
| `Provider<R>` | Sealed exact interface relation supplied by acquisition. |
| `Ops<R>` | Effect with `read : Handle<R> -> Int` and `write : (Handle<R>, Int) -> Unit`. |
| `read` | Interface method `Handle<R> -> Int ! {Ops<R>}` under `Provider<R>`. |
| `write` | Interface method `(Handle<R>, Int) -> Unit ! {Ops<R>}` under `Provider<R>`. |

The alias `Cell` is chosen by source code. Existing names such as `Cell`,
`Handle`, `Provider` and `Ops` do not become reserved words. `builtin` becomes
a reserved module-root name: configuring it as a filesystem root rejects
before filesystem inspection. Only `@builtin.cell` is admitted; other imports
under that root reject. This is one fixed compiler module, not an extensible
intrinsic-module registry. A same-named file or copied API text has no builtin
authority. The admitted module origin, not its spelling, authenticates it.

### Acquisition and ordinary use

`resource` is a new reserved expression keyword. `cell` is contextual within
its production. A resource expression has this form:

```ash
import @builtin.cell as Cell

main : Unit -> Int
main () = resource cell<R> c = 41 {
    let _ = Cell.write (c, 42)
    Cell.read c
}
```

The form has one uppercase identity binder, one ordinary value binder, one
primary-expression initializer and one block body. A non-primary initializer
must be parenthesized. The introducing module must directly
import `@builtin.cell`, through either complete or targeted import. Helpers may
use ordinary facade re-exports of the API. Acquisition is not a first-class
function and adds no exported pseudo-function or general provider declaration.

The initializer checks as `Int` and evaluates exactly once in the preceding
scope, before acquisition. Its effects remain outward. On successful
acquisition, `R` is a fresh rigid, kind-Type identity in the body, `c` has the
authenticated `Handle<R>` type, and the body receives exact `Provider<R>`
evidence and an identity-local interpreter for `Ops<R>`.

The scope owns the cell and its release obligation. Handles are duplicable
access values, not independent release owners. Aliases, tuples, constructors,
ordinary helper calls and repeated calls of a capturing closure are permitted
while the acquisition remains live. Reading returns an ordinary copied `Int`;
writing changes that cell and returns `Unit`. Neither operation transfers
ownership. There is no source handle constructor, representation conversion,
identity inspection, manual release or use-after-release outcome.

Generic forwarding uses ordinary constraints and rows, for example
`Handle<R> -> Int ! {Ops<R>} where Provider<R>`. Sealed provider evidence can
be required abstractly and forwarded. Source `impl` and source `with` cannot
introduce the builtin provider relation, even with matching signatures.
Acquisition alone introduces its trusted methods, which request `Ops<R>`.
Ordinary exact handlers retain their existing lexical interception rules;
intercepting an operation does not create a handle or a provider origin.

### Identity and execution context

Each successful execution of an acquisition introduces a fresh dynamic
activation. Separate and overlapping executions of one source site do not
become equal merely because they share a static declaration identity.
The handle identifies that activation; no separate first-class identity
witness is introduced. Static checking keeps an acquisition binder distinct
from enclosing abstract parameters and other live acquisition binders.

Effect execution preserves validated type and row instantiation through
generic calls, returned closures, recursive templates, handlers and captured
control. A request uses its own lexical instantiation; a handler uses its saved
lexical instantiation. No machine-global substitution or runtime-value-based
type inference is permitted. Pure execution retains its existing erasure.

Effect Core independently restricts type-abstraction bodies to the forms
produced by source lowering: an inert function/constructor value or variable,
transparent type-operation wrappers around such forms, or an authenticated
generated method adapter whose checked applications only construct evidence
functions. Each nested abstraction satisfies the same independent check.
An empty immediate effect row alone is not this proof. This internal invariant
allows execution to retain the lexical abstraction until instantiation without
delaying source effects. Parameterized ordinary constructors retain their
existing constructor behavior; Pure Core is unchanged. Arbitrary effectful or
aggregate-computing Core abstractions are not admitted by this Effect lowering
boundary. This is not a source generalization restriction: source already
generalizes function definitions and eligible anonymous-function bindings.

The same execution context binds a resource identity to its activation.
An outer operation-bearing closure called during a nested execution of the
same acquisition site still addresses the outer identity. This applies when
the closure's resource dependency appears in effect metadata rather than an
ordinary term capture. Type and provider checking must already reject mismatched
acquisitions; a dynamic handle check is not a substitute for static separation.

### Lifetime and capture

Each resource-bearing value and callable retains inferred resource dependencies
separately from request-carried control obligations. Dependencies propagate
through aliases, aggregate fields, patterns, ordinary and imported helpers,
factories, recursive groups, polymorphic instantiation and selected evidence
methods. Returning an identity-free function type does not erase a dependency
on a live cell or its identity-indexed operations.

The body result and its retained value/callable dependencies must not depend on
the closing acquisition. Types, rows, schemes and retained evidence must not
export its identity either. An inner scope may return dependencies on a
still-live outer resource. Copied integers and closures that retain only those
integers may escape. A constant closure created while a cell is live does not
own the cell merely because the implementation retains an unused environment
entry. No resource payload may remain owned by such an entry after scope exit.

Dependency checking also covers operation request operands. A request must not
deliver a payload dependent on an acquisition to a source handler outside that
acquisition, including dependencies hidden in callable values or their selected
evidence. The rule applies separately to each dependency owner: a value that
depends only on an outer resource may cross an unrelated inner acquisition to
a handler still inside its owner. The trusted cell interpreter at its own
acquisition boundary remains an admitted recipient. Resource-free payloads may
cross, and the outer handler may resume the captured resource scope. This slice
adds no temporary lending of dependent values to outer handler clauses.

Unknown higher-order behavior rejects an escape or abandonment when the
relevant dependency cannot be proved absent. This does not authorize blanket
rejection of useful known helper/closure/import abstractions or of ordinary
resource-free predecessors. No source lifetime or capture-polymorphic type
language is added.

### Admitted exits before general cleanup

| Path | Behavior |
| --- | --- |
| Normal completion | Release the scope's cell once, then return the checked result. |
| Nested normal completion | Release inner before outer. |
| Capture followed by resume | Retain the cell with its scope; ordinary completion releases it. |
| Discard confined within an enclosing resource scope | Permit only when continuation and resource completion obligations remain satisfied. |
| Discard abandoning a live resource scope or skipping its required completion | Reject statically, including an affected owner outside the immediate captured segment. |
| Divergence | Remains divergence; no claim of eventual release. |

The builtin allocation has no source-level failure branch. An internal capacity
failure publishes no partial acquisition and retains existing failure ownership.
Internal failure disposal releases owned interpreter memory safely; it is not
a new source cleanup path. Source abort, exception, destructor failure, partial
foreign acquisition, suspension and cancellation are excluded.

### Authentication, diagnostics and resource bounds

Source checking authenticates the builtin origin and the complete relation
between acquisition, identity, handle, provider methods and effect instance.
Summary admission, linking and independent Core validation preserve and check
that relationship. Neither copied names nor ordinary evidence grants provider
authority. Transformed Core re-establishes both stored-dependency and
request-carried-obligation checks from its actual structure.

Lexing and parsing own malformed forms. Resolution owns import availability,
names and scope. Ordinary kind/type/row errors retain precedence. Resource
escape has a type-phase diagnostic at the escaping expression with acquisition
and capture/call labels where known. Unsafe discard keeps
`effect.discard-unsafe` and identifies the live resource obligation. Forbidden
provider introduction fails at the attempted source declaration. Forged
checked/Core facts and runtime invariant failures remain internal errors.

Use the existing owning syntax, module, constraint, type, Core-construction and
Core-validation work ledgers. Inference is finite and conservative, with no
partial successful publication on exhaustion. Every new retained collection
and proportional scan has charged, fallible work and iterative ownership.
Runtime cell capacity counts live owned cells and releases capacity exactly
once on normal exit; capture/restoration moves ownership without duplication.
Deep normal and failed execution must dispose cells, captures and environments
without recursive stack growth. Resource-free pure execution gains no resource
registry, resource frame or live-cell allocation.

## Semantic delta

Add one generative resource acquisition and sealed cell API, stored-dependency
lifetime checking and resource obligations in captured control. Correct effect
instantiation across ordinary abstraction boundaries and distinguish it from
pure type erasure. Keep exactly-once continuation completion and no-cleanup
discard unchanged.

## Affected specification areas

- [Syntax](../../spec/syntax.md) and [lexical structure](../../spec/lexical-structure.md).
- [Name resolution](../../spec/name-resolution.md): compiler module and scope.
- [Static semantics](../../spec/static-semantics.md): sealed authority, rows,
  generativity, dependencies, lifetime, diagnostics and budgets.
- [Elaboration](../../spec/elaboration.md): retained relationships and Core.
- [Dynamic semantics](../../spec/dynamic-semantics.md): instantiation,
  acquisition, operations, retained scope and release.
- [Specification overview](../../spec/README.md) and the
  [tool guide](../tools/ash.md): boundary and builtin-root behavior.

## Resulting specification truth

The complete product branch permits one non-foreign scoped mutable cell whose
access and captured dependencies cannot outlive its owner. Local milestone
integration does not make this current on main; that remains a separate gate.

## Interactions

Retain ordinary local-newtype erasure and identity-free closure behavior,
interface determination and selection order, lexical evidence capture,
exact effect rows and ordered handlers. Separate provider authority from
ordinary interface and future proof authority. Runtime activation witnesses
and dependency summaries leave an explicit boundary for future existential
ownership packages without implementing escape or ownership transfer now.

## Non-goals

No linear handle-use calculus, general borrow/lifetime syntax, generic resource
declarations, acquisition/destructor callbacks, hooks, reliable general cleanup,
foreign providers, native handles, proof evidence, existential packages,
dynamic loading, scheduling, concurrency, escaping or multi-shot continuations.
No main merge, remote push or milestone tag.

## Required evidence

- Generic effect requests and returned closures match concrete caller handlers;
  distinct instantiations remain separate, including rows and method adapters.
- Independent Effect Core checking rejects unproved type-abstraction bodies;
  admitted functions, constructors and authenticated adapters survive both
  transforms without changing strict source effect order or Pure erasure.
- Builtin imports, renaming and facade export retain origin; fake source APIs,
  forbidden roots and forged provider facts do not gain authority.
- Direct read/write, repeated access, aliases, generic/imported helpers,
  nested and sequential scopes, and overlapping same-site acquisitions.
- Reject direct, aggregate, closure, evidence-method and continuation escape;
  admit copied results, constant closures and live outer dependencies.
- Normal and nested release observations; retained capture/resume; inner safe
  discard; rejected outward abandonment and skipped scope completion.
- Reject a hidden resource-dependent request payload sent to an outer handler,
  even when the resource body's own result is dependency-free. Pair it with a
  copied-payload/resume control and a still-live outer-dependency control.
- Source, linked and Core identity/owner/authority/capture tampering; identity
  and folding transforms followed by independent validation and execution.
- Exact work/cell limits, one-short failure, retry, capacity reuse, failure
  atomicity, deep success/failure disposal and pure-program locality.
- Full verification, independent semantic and Rust/resource reviews,
  documentation/link/authority audit, and a downstream simplification review
  before any hooks work. Retain evidence, then close transition artifacts and
  follow the local milestone worktree lifecycle.
