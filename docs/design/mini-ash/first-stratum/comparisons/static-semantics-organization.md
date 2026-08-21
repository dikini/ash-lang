# First-stratum static-semantics organization comparison

> This comparison is informative evidence governed by
> [DN-0016](../../../DN-0016-first-mini-ash-corpus.md). It does not accept a
> resolver, typechecker, elaborator, or Core architecture and does not define
> current Ash semantics.

## Question

Which boundary among name resolution, typechecking, and elaboration establishes
each first-stratum fact once, preserves precise source relationships, and emits
typed Core without adding inference machinery that the corpus does not use?

## Scope and method

The written comparison applies the provisional scope, typing, elaboration, and
diagnostic rules to `V-001` through `V-008`, `R-001`, `R-002`, `T-001` through
`T-004`, and `X-001` through `X-003`. No code probe is required: the corpus is
monomorphic, every typing rule is syntax-directed or expected-directed, and the
candidate boundaries have different fact ownership visible in the rule inputs
and diagnostic obligations.

The comparison considers four organizations:

1. one recursive operation resolves names, checks types, and emits Core;
2. a resolver emits a binder-identified surface form, then one bidirectional
   typed elaborator emits validated structured Core;
3. resolution and typechecking produce a fully typed surface tree, followed by
   a separate lowering to Core;
4. resolution feeds constraint generation and solving, followed by elaboration.

All candidates must keep parser recovery nodes out of evaluator input. They
must return structured failures rather than encode rule outcomes in diagnostic
strings.

## Facts and their owners

The first-stratum evidence assigns one owner to each fact:

| Fact or failure | Owning operation | Consumer |
| --- | --- | --- |
| One global interface is paired with one body | Definition grouping and resolution | Presentation-specific checking |
| Global and local names have stable binder identities | Resolution | Typing, elaboration, diagnostics, Core validation |
| A local initializer excludes its new binder | Resolution scope construction | `V-003` and Core validation |
| A global excludes itself and is visible only in the remaining file | Resolution scope construction | Whole-program elaboration |
| An expression synthesizes or checks against a monotype | Bidirectional typing rule | Typed-node construction and diagnostics |
| A callee exposes a function domain and codomain | Function-exposure rule | Application checking |
| Two types agree | Type-equality rule | Checking rules and Core validation |
| An equation pattern list follows successive arrow domains | Presentation elaboration guided by the declared type | Function and match construction |
| An operational comma list decomposes one product domain | Presentation elaboration guided by the declared type | Generated tuple destructuring |
| Boolean patterns bind names and cover their domain | Shared pattern and coverage rules | Both definition presentations |
| A generated node has a causal source origin | The operation that inserts it | Diagnostics and later validation |
| Typed Core is internally consistent | Independent Core validator | Evaluator and transformations |

This ownership does not prescribe one Rust module per row. It requires one
reviewable decision path for each fact.

## Candidate comparison

### Fused resolution, checking, and elaboration

A fused traversal can be short for the valid cases. It can carry a name scope
and type context together, then construct Core as it returns.

The rejected cases expose its cost. `R-001` and `R-002` must remain resolution
failures even while the same operation is prepared to typecheck. Local scope
rules, global grouping, expected typing, function exposure, presentation
lowering, and diagnostic construction share one recursive control path. Reuse
for pattern clauses and explicit matches tends to become helper extraction,
which reconstructs the staged boundaries inside the fused function.

This organization can be implemented correctly, but it gives no advantage that
survives the required structured errors and shared pattern rules. It also makes
resolved-form tests and later refactoring harder because name lookup remains
interleaved with every type rule.

### Resolved surface followed by typed elaboration

The resolver replaces each definition and occurrence spelling with a stable
binder identity while retaining spelling and source origin as provenance. Its
scope operations directly express the corpus:

- resolve a nonrecursive initializer before extending the local scope;
- resolve a function body after extending the scope with its parameter;
- reject a duplicate global before checking the second body;
- resolve and check one global before extending the scope over the remaining
  source file.

The typed elaborator then uses separate synthesis and checking entry points. A
check result contains either typed structure or a structured rule failure. Its
application path is conceptually:

```text
synthesize callee
  → expose Function(domain, codomain)
  → check argument against domain
  → construct application annotated with codomain and origins
```

This path distinguishes `T-003` from `T-004` without inspecting an error
message. Primitive operations use the same `check` entry point, so `T-002`
retains the operator and operand relationship. Global definition checking uses
the interface codomain as an expectation, so `T-001` retains the interface and
equation-body relationship.

Presentation-specific entry points decide how source structure becomes shared
typed semantic structure. They call the same function, pattern, coverage,
type-equality, and Core-construction rules. Thus an equation group and an
explicit match can retain different origins while producing the same coverage
reason or comparable structured Core.

This candidate introduces one durable intermediate representation: resolved
surface. Its binder identities and source relationships are independently
useful to diagnostics, tooling, typechecking, and Core validation.

### Typed surface followed by separate Core lowering

A fully typed surface tree gives diagnostics direct access to every original
construct and makes typechecking independently testable. It also stores typed
facts before equation-to-match, block-to-binding, grouping, and operational
tuple elaboration.

For this corpus, the extra boundary does not establish a fact needed by a
separate consumer. The typed elaborator can retain source origins while it
constructs structured Core, and the Core validator independently checks its
result. A separate typed surface tree would require another recursive type,
another validator or trust boundary, and another provenance-preserving
conversion. It becomes justified if later tooling or transformations need
typed presentation structure after checking; the current cases do not show
that need.

### Constraint generation, solving, and elaboration

A constraint representation would separate collection from solving and prepare
for inference variables, kinds, generalization, and richer obligations. Those
are strong downstream pressures in DN-0006 and DN-0008.

The first stratum uses no inference variables, generalization, or nontrivial
constraint resolution. Its only type relation is structural equality over a
small monotype algebra, and anonymous functions check against known expected
types. A solver would turn direct rule failures into deferred constraints and
would need added origin paths to reconstruct `T-001` through `T-004`. That is
more mechanism without more current evidence.

The rule boundary should leave later constraint generation possible. It should
not instantiate a constraint store until a richer stratum supplies cases that
distinguish it from direct checking.

## Structured rule outcomes

The favored organization depends on data-shaped failures. The following forms
are illustrative, not accepted Rust APIs:

```text
ResolveFailure =
    UnknownName { use_origin, spelling, visible_names }
    | DuplicateGlobal { second_origin, first_origin, binder_spelling }

FunctionExposure =
    Function { domain, codomain, type_origin }
    | NotFunction { found, expression_origin }

TypeComparison =
    Equal
    | Mismatch { expected, found, expectation_origin, value_origin }

CheckFailure =
    DefinitionResult { comparison, body_origin, interface_origin }
    | OperatorOperand { comparison, operand_origin, operator_origin }
    | NotApplicable { exposure, application_origin }
    | Argument { comparison, argument_origin, domain_origin }
```

Rendering consumes these facts and decides wording, labels, and justified help.
The resolver and checker do not format source snippets or parse their own error
strings. This preserves Elm-style explanation and Rust-style source precision
without making the renderer a semantic rule owner.

## Corpus comparison

| Pressure | Fused traversal | Resolved surface and typed elaboration | Typed surface then Core | Constraint pipeline |
| --- | --- | --- | --- | --- |
| `V-003` shadowing | Scope can work but shares control with typing | Initializer/body scopes are isolated resolver operations | Same resolver benefit | Same resolver benefit |
| `V-004` and `V-005` expected types | Possible with mode flags or helpers | Direct `check` entry point | Direct checking, then another lowering | Constraints obscure a known expectation unless solved eagerly |
| `V-002` and `V-008` presentation convergence | One traversal needs form-specific branches amid common rules | Form-specific elaboration calls shared semantic rules | Preserved, with an extra typed tree | Preserved after constraint attribution |
| `R-001` and `R-002` | Must classify early failures inside the fused operation | Resolver owns both categories and related spans | Resolver owns both | Resolver owns both |
| `T-001` through `T-004` | Structured helper boundaries recreate staging | Each rule returns the exact expected, found, and related origins | Same evidence, stored twice before lowering | Requires origin-rich constraints and failure attribution |
| `X-001` and `X-002` shared coverage | Common helper is possible | One pattern and coverage subsystem serves both presentations | Same, plus typed presentation lowering | Coverage is not ordinary type equality and still needs its own rule |
| `X-003` grouping | Type-directed branching is mixed with all other work | Presentation elaboration consumes one structural function type | Typed surface records the choice before lowering | Constraints do not remove the presentation decision |
| Later inference and polymorphism | Requires refactoring | Rule interfaces can introduce inference state when cases require it | Same, with more representations to update | Strongest prepared mechanism |

## Conclusion

The evidence favors a resolved surface form followed by a bidirectional typed
elaborator that emits typed structured Core and then invokes an independent Core
validator.

This organization follows the types without making types reconstruct lexical
scope. Resolution establishes binder identity and visibility first. The checker
owns synthesis, checking, function exposure, and structural equality. The
elaboration part of the same operation owns inserted semantic structure and its
causal provenance. Presentation-specific paths call shared semantic rules
rather than create separate function or match semantics.

The current evidence does not justify a fully typed surface representation, a
general constraint solver, or stable identities for every syntax and Core node.
Stable binder identities are required. Stable source origins are required.
Arena node identities remain an independent storage question.

This evidence led to
[AD-0006](../../../../decisions/AD-0006-front-end-semantic-boundaries.md). The
comparison did not itself accept the architecture or settle later inference,
generalization, kinding, constraint resolution, pattern compilation, or Core
storage.

## Accepted outcome

AD-0006 accepts these properties:

- resolution is a distinct checked boundary that assigns stable binder
  identities and enforces lexical and file scope;
- typechecking is bidirectional where expected types provide required
  information;
- one rule interface owns type equality and another owns function exposure;
- presentation-specific elaboration reuses shared function, pattern, coverage,
  and typed-node construction rules;
- inserted nodes retain causal source origins;
- user diagnostics are rendered from structured resolution and checking
  failures;
- typed Core is independently validated before evaluation or after a
  transformation.

The decision does not accept the provisional surface syntax or typing rules,
choose a constraint-solver implementation, require a typed surface tree, or
settle later polymorphism and pattern compilation.

## Remaining questions

- Should the typed elaborator construct Core directly, or use a short-lived
  builder that cannot expose unvalidated nodes?
- Which source-origin relations belong inline and which belong in a side table?
- Which richer stratum first makes inference variables and a constraint store
  cheaper than direct bidirectional checking?
- Does typed tooling later require a retained typed presentation tree, or can
  resolved surface plus typed Core answer its queries?
- How should rule traces be recorded so diagnostic tests can assert semantic
  reasons independently from rendered wording?

## Retention boundary

This comparison uses written evidence because the current algorithms are
syntax-directed and the candidate differences are visible from their fact
ownership. It creates no experimental code. Any later solver, typed-surface, or
diagnostic-renderer probe remains disposable unless an accepted decision and
task retain it.
