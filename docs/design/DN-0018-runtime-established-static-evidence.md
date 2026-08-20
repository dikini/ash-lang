# DN-0018: Runtime-Established Static Evidence

- ID: `DN-0018`
- Status: exploring
- Related: [DN-0008: Typed Core and Elaboration](DN-0008-typed-core-and-elaboration.md), [DN-0010: Identities and Resource Lifetimes](DN-0010-identities-and-resource-lifetimes.md), [DN-0013: Session and Resource Protocol Stress Tests](DN-0013-session-and-resource-protocol-stress-tests.md), [DN-0017: Resource Management and Storage Policy](DN-0017-resource-management-and-storage-policy.md)

> This design note is informative. It explores runtime checks that produce
> statically tracked evidence; it does not define current Ash, accept refinement
> or dependent types, or authorize trusted compiler primitives. All notation is
> illustrative.

## Question

Can a successful runtime check introduce unforgeable, erasable evidence about a
value or relationship so later code can use the established fact without adding
arbitrary runtime values to Ash types?

## Context and scope

Some useful facts are difficult or undesirable to derive through ordinary type
checking:

- a buffer satisfies an alignment requirement;
- an input has passed validation or authentication;
- two mutable views are disjoint;
- a mapping relates a handle and an address range;
- a dynamically acquired object belongs to a fresh validity generation.

Rejecting every such program loses useful static structure. Adding general
refinement arithmetic or arbitrary term indices would enlarge the type system.
Repeating the check at every use wastes work and obscures the boundary where the
fact became trusted.

[DN-0010](DN-0010-identities-and-resource-lifetimes.md) already explores fresh
identities and witnesses. This note asks whether the same generative mechanism
can brand a checked value or relation. The source exploration calls these
runtime-established witnesses certificates. [DN-0008](DN-0008-typed-core-and-elaboration.md)
owns how evidence remains valid through transformations.

## Constraints

A candidate must:

- make evidence impossible to construct through ordinary untrusted source code;
- identify the operation or trusted boundary that establishes the fact;
- preserve which values and identities the evidence relates;
- prevent evidence from being reused after a relevant value, state, or identity
  changes;
- define what remains at runtime after checking and what may erase;
- keep a failed check on an ordinary typed error path;
- avoid claiming that a brand proves predicates the checker never established.

## Candidate model

### Brand one checked value

A checking operation could return a package containing a fresh evidence identity:

```text
check : T -> Result<(exists c. Checked<c, T>), Error>
```

Code outside the package cannot name or forge `c`. Operations that require the
checked property accept `Checked<c, T>` or an explicit witness associated with
it. The brand may erase when runtime representation does not depend on it, while
the checked value remains.

The type constructor alone is insufficient. The design must restrict its
constructor or otherwise make the evidence introduction rule explicit.

### Brand a relationship

A check may relate several values rather than classify one:

```text
check_disjoint :
    (Slice<a, T>, Slice<b, T>)
    -> Result<(exists c. Disjoint<c, a, b>), Error>
```

An operation that mutates both slices can require the `Disjoint` witness. The
type checker preserves provenance and identity equality; it need not reproduce
the range arithmetic performed by the check.

Symmetry, transitivity, weakening, and composition of relationship evidence are
independent rules. They must not follow merely because the relationship name
suggests them.

### Introduce abstract places only under demonstrated pressure

Whole-resource identity may be too coarse when one allocation is decomposed
into independently mutable views. A split operation could introduce fresh place
identities and evidence that the places are disjoint. These are abstract names,
not runtime integer ranges in types.

Place identity should remain a deferred candidate until a concrete corpus shows
that whole-resource uniqueness plus ordinary runtime checking rejects important
safe programs. A general place calculus would add joins, projections, mutation
invalidation, and diagnostic obligations.

### Keep authority separate from evidence

Evidence that two places are disjoint does not itself grant authority to mutate
them. The operation must also receive values carrying the required unique or
mutable authority. Likewise, an authenticated brand records a successful check;
policy still decides what operations that fact authorizes.

## Candidate directions

### Generative brands and explicit witnesses

Fresh identities record provenance, while abstract constructors restrict
introduction. This reuses the identity questions in [DN-0010](DN-0010-identities-and-resource-lifetimes.md)
and keeps the checker responsible for equality and scope rather than the checked
predicate. It may add packaging and evidence-passing overhead in source or Core.

### Refinement or dependent types

The type system could represent the predicate and prove some checks statically.
This may remove runtime validation and express derived relationships, but it
adds normalization, proof, inference, and diagnostic work far beyond the narrow
brand model.

### Dynamic wrappers only

A validated wrapper could hide its representation and expose safe operations
without a fresh identity. This is simpler when the fact concerns one value. It
may not express relationships among independently used values or distinguish
separate validation generations.

### Compiler-only analysis facts

An analysis could attach non-source evidence used only for optimization. This
avoids surface evidence but cannot support library APIs that need to exchange a
checked fact. Such facts also need explicit invalidation and validation rules.

The candidates may coexist for different consumers. The experiment must show
which minimum mechanism is needed for each case rather than select the richest
system globally.

## Evidence and experiments

Use one small model to compare at least generative brands and dynamic wrappers:

| Case | Required observation | Failure observation |
| --- | --- | --- |
| Successful check | Later operations accept the established fact without repeating the check. | The check result cannot cross an ordinary abstraction boundary. |
| Failed check | No evidence is produced and the error remains explicit. | Failure creates a partial or forgeable witness. |
| Forgery | Ordinary construction, coercion, and unrelated brands are rejected. | A caller fabricates or substitutes evidence. |
| Generation separation | Two successful checks introduce distinct evidence when their validity generations differ. | Equal payload shapes collapse unrelated checks. |
| Relationship provenance | Evidence applies only to the values or identities checked. | It can justify an operation on different values. |
| Mutation invalidation | A mutation that may falsify the predicate consumes or invalidates the evidence. | Stale evidence survives a fact-destroying update. |
| Abstraction | An existential or opaque package preserves usable relationships without exposing the brand. | Opening the package loses the equality or leaks the brand globally. |
| Erasure | Removing proof-only representation after its last checked use preserves behavior and validation. | Erasure removes runtime data or precedes the last consumer. |
| Optimization | Core consumes validated evidence and rejects stale or unchecked facts. | Backend metadata becomes the only authority for correctness. |
| Diagnostics | Errors identify the missing, mismatched, or invalidated evidence. | Users see an unexplained identity mismatch. |

For place decomposition, compare whole-resource rejection with a checked split
that produces two usable mutable views. Record whether abstract names and one
relationship witness suffice. Do not add range arithmetic unless the abstract
model fails a named case.

A prototype is disposable. Retain its design evidence only if constructors
remain unforgeable, provenance survives abstraction, invalidation is explicit,
and Core can validate the evidence lifecycle. Production intrinsics require a
later architectural decision or semantic proposal and an authorized task.

## Open questions

- Is a branded wrapper sufficient, or do useful APIs require first-class
  evidence values?
- Which language boundary may introduce evidence, and how is that authority
  represented and audited?
- Does every successful check need a fresh identity, or can some evidence use a
  stable nominal proposition?
- How do mutation, aliasing, ownership transfer, suspension, and cancellation
  invalidate or retain evidence?
- Which relationship rules are built in, supplied by trusted libraries, or
  carried as separately checked evidence?
- Can existential packaging and ordinary equality constraints preserve all
  useful relationships without higher-rank types?
- What part of evidence survives at runtime for dynamic dispatch, diagnostics,
  or foreign calls?
- When should an optimizer consume evidence rather than preserve it for a later
  pass?
- Which concrete split, projection, or foreign-memory case justifies abstract
  resource places?
- Which bounded-resource properties belong to optional whole-program analysis
  rather than branded expression types?

The hypothesis survives only if the checker can track provenance and validity
without understanding each dynamic predicate, while untrusted code cannot turn
the abstraction into a general cast.
