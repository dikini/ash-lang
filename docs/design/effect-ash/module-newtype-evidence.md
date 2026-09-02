# Module `newtype` Evidence

This report retains implementation evidence for the first bounded
`effect-ash` input: module-owned, representation-preserving nominal types. It
is informative, not normative. The [Ash specification](../../../spec/README.md)
alone defines the current language on this product branch. Git history retains
the accepted proposal, implementation task, and execution plan after those
transition-only artifacts leave the current tree.

Integration and any Effects Ash milestone tag are separate lifecycle actions.
At the module-`newtype` checkpoint, local or runtime-fresh identity,
existential escape, effects, handlers, resources, providers, hooks, dynamic
loading, proof evidence, implicit coercions, runtime type tags, and ABI
guarantees remained separate work. This integration branch now combines the
separately completed resume-required effect kernel; this report remains scoped
to the module-`newtype` checkpoint.

## Scope and checkpoints

The branch starts from the pure predecessor `d1e323d`. Its principal unsigned
authority and product checkpoints are:

- `487ed30`, which accepts CP-0012;
- `686011c`, which authorizes TASK-0019 and its execution plan;
- `be4e2e5`, which reserves `newtype` and retains its declaration shape;
- `c7c2fa1`, which retains module-owned identities and canonical
  representations through summaries;
- `7bc8d2d`, which checks explicit wrapping and matching while keeping nominal
  interface evidence separate; and
- `15224fc`, which authenticates representation conversions in typed Core and
  erases them during evaluation; and
- `7ae578b`, which retains the final resource matrix, semantic corpus,
  predecessor-accounting correction, and owner-local exact guards.

The accompanying checkpoint-record commits are `ed490f3`, `397c9b3`,
`29e3b2a`, and `3cf4c18`. Commit identities are evidence boundaries, not
language authority.

## Implemented boundary

A module may declare a private, public opaque, or public transparent
`newtype`. The nominal and its same-spelled unary constructor receive stable
module-owned identities. Declaration parameters retain their order, identity,
and fixed kinds; substituting an applied nominal's arguments into its canonical
representation derives the one authorized conversion relation.

The nominal remains distinct from its representation and from same-shaped
nominals. An accessible constructor is a first-class rank-1 function and the
only direct source wrapping operation. Its pattern is the sole, irrefutable
unwrapping operation. Ordinary nominal mismatch, pattern coverage, and
interface selection remain in force. In particular, representation evidence
does not satisfy a nominal interface goal.

Kind checking precedes an iterative, type-work-budgeted graph pass over only
`newtype` representation edges. The pass rejects direct and mutual
zero-storage cycles, but stops at ordinary data. Its deterministic diagnostic
belongs to the first representation occurrence that closes the cycle.

## Visibility, summaries, and linking

Public transparent summaries expose source constructor access and the facts
needed to type wrapping and matching. Public opaque summaries expose the
nominal but withhold constructor access and representation spelling. Private
declarations expose neither source name. In all three cases, authenticated
compiler facts retain the canonical representation long enough to validate
linked conversions; those facts do not create source access.

Import admission and linking authenticate declaration kind, nominal and
constructor identities, owner, parameter order and kinds, constructor
cardinality and spelling, representation and substitution, visibility,
provenance, and route agreement. Qualified imports, targeted renames, direct
re-exports, and facade diamonds preserve one defining fact. Independent
tampering tests reject omissions, reordering, substitutions, forged origins,
access changes, and conflicting diamond facts before Core publication.

The retained source corpus includes:

- private hidden values that cross a module boundary only through exported
  operations;
- transparent wrapping and matching through a re-exporting facade;
- public opaque constructor rejection;
- kinded, parameterized, nested, tuple, ordinary-data, scalar, and first-class
  constructor use;
- explicit nominal interface evidence and rejection of representation-only
  evidence; and
- reserved-keyword, unequal-constructor, representation-cycle, kind,
  mismatch, pattern, coverage, and diagnostic-precedence failures.

## Typed Core and runtime

Elaboration lowers wrapping and matching to one-child typed representation
conversions. A constructor in value position uses existing Core type
abstractions, a generated unary function, and a wrap body; no allocating
constructor variant was added. Fresh generated type binders are matched by
position and kind to the canonical declaration parameters without replacing
those parameter identities.

Both registry-validation modes derive the expected child and result types from
the linked canonical relation. Separate tamper matrices cover direction,
nominal identity and owner, parameter application and substitution, child and
result types, declaration provenance, and canonical source relation. Ordinary
constructors cannot claim the erased conversion path, and `newtype`
constructors cannot claim the allocating ordinary-constructor path.

Identity traversal and literal folding rebuild the authenticated relation and
return to independent validation. The evaluator enters the conversion child
directly. It adds no wrapper cell, tag, copy, lookup, frame, state, or failure.
A result whose source type is `UserId` over `Int` therefore renders its value as
`42` and reports its type as `UserId`.

## Exact resources and predecessor stability

The retained resource matrix closes ten new carrier categories across five
separate ledgers: syntax, module type work, interface constraints, Core
construction, and Core validation. Owner-local probes establish exact success,
one-unit-short rejection before publication, retry from the same logical input,
and deep or wide teardown where the carrier can grow.

The principal additive boundaries are:

- 28 cumulative syntax-work units: nine retained tokens plus 19 syntax events;
- 20 type-work units for the first imported nominal-and-constructor family;
- two type-work units for a scalar canonical representation: one retained
  authority slot and one representation type cell, with zero interface work;
- `4P+3` type-work units for fresh substitution of a constructor with `P`
  parameters;
- 12 type-work units for the one-vertex scalar representation graph: two
  vertex-index, two adjacency, two type-walk, and six depth-first-search units;
- one Core-construction type-work unit for the scalar conversion result type;
- `18P+9` type-work units for the complete generated constructor function;
- six Core-construction units to transform a scalar conversion: two for
  remapping, two for its child copy, and two for its conversion copy; and
- a fixed 518-unit registry-and-node validation envelope for the retained
  two-parameter fixture, plus `4P+1` units for the conversion relation: `P`
  argument slots, `P+1` application-spine inspections, `P` replacement slots,
  and `P` parameter/argument rows. At `P=2`, the exact total is 527.

Every proportional charge precedes retained allocation or publication. No
production limit changed. A source program with no `newtype` still produces
eight Core nodes, no representation conversion, the same seven-step evaluator
trace and maximum frame depth across retries, and `42 : Int`.

The final gate also exercised the predecessor method-parameter resource
manifest. It exposed eager shadow-map duplication in the shared substitution
helper: replacement keys and discarded source-variable occurrences were being
charged even when no `forall` binder could shadow them. Lazy retention now
allocates shadow state only for an actual overlap. This restores the four
predecessor Core-validation boundaries at 681, 1,183, 805, and 2,426 units while
retaining charged, fallible nested-shadow handling.

## Downstream Effects pressure

The checkpoint provides transferable evidence for stable generative identity,
hidden compiler authority, linked authentication, and erased static
operations. It deliberately does not answer later questions:

- local `newtype` needs lexical identity ownership and escape rules rather than
  reusing module identity allocation unchanged;
- runtime generativity needs lifetime and withdrawal semantics, and returning
  such identities creates existential-packaging pressure;
- proof evidence must remain distinct from the compiler's canonical
  representation authority; and
- resource scope may reuse the charge-before-publication and authenticated
  identity patterns, but cannot infer runtime acquisition or release semantics
  from a pure erased conversion.

The implementation also preserves deliberate simplifications: one canonical
relation instead of a general coercion system, no constructor-specific Core
function variant, no runtime registry or tag, no heap-inspection API, and no
new interface-selection path.

## Reviews and verification

Each implementation checkpoint received independent semantic/Core and
Rust/resource review. Checkpoint 5's resource review found that parameterized
conversion validation had not charged all four distinct parameter traversals;
the corrected exact boundary is `4P+1`, and re-review approved it without a
remaining Critical or Important finding.

The final product reviews covered semantic/specification agreement,
compiler/Core and runtime authentication, Rust ownership and resources,
documentation authority and links, downstream Effects pressure, and
simplification. They found three resource-evidence gaps: self-measured rather
than fixed formulas, incomplete predecessor heap/resource evidence, and a
missing mixed-error precedence case. The corrected matrix fixes the formulas,
retains the predecessor boundaries, and adds the mixed corpus case. Review of
the specification and retained design material corrected constructor-occurrence
wording, cycle diagnostic and retry wording, stale open questions, and missing
authority and exclusion labels. Re-review found no remaining Critical or
Important issue.

The pre-cleanup gate ran `cargo xtask verify`, Markdown lint, diff hygiene, and
status inspection. It passed formatting, metadata, build, Clippy, 855 library
tests, 10 CLI unit tests, every integration target, 67 executable
specification examples, and Rustdoc. The dedicated resource, corpus,
module-newtype, visibility, resolution, elaboration, Core-validation, and
architecture suites are included in that run. Manual review checked changed
relative links, formal notation, diagnostic precedence, authority boundaries,
and the absence of wrapper allocation. The retained product-evidence commit is
`7ae578b`; the specification and this report are retained together in the
following documentation checkpoint.
