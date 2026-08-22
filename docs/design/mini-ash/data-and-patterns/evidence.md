# Data and Pattern Integration Evidence

This report records implementation evidence for accepted CP-0003 and compares
it with the informative findings in [DN-0007](../../DN-0007-data-and-pattern-typing.md)
and [DN-0019](../../DN-0019-primitive-feature-composition.md). It does not
define Ash semantics. The normative specification owns the merged language.

## Scope and environment

The measurement covers `4d5ce64...e5ac562` plus the documentation and deep-test
checkpoint in the `feature/data-and-adts` worktree.

| Property | Observation |
| --- | --- |
| Baseline | recursive-definition merge `4d5ce64` |
| First implementation checkpoint | unsigned commit `e5ac562` |
| Rust | `rustc 1.97.1 (8bab26f4f 2026-07-14)` |
| Cargo | `cargo 1.97.1 (c980f4866 2026-06-30)` |
| Host | Linux `x86_64` |

At the evidence checkpoint, the production diff under `src/` contains 3,128
added and 27 deleted lines in 12 files. The feature-owned data and pattern
pipeline accounts for 2,900 lines. These counts include private tests and
do not measure semantic difficulty.

## Changed composition points

- The lexer adds uppercase identifiers, `_`, `type`, `match`, `|`, and `=>`.
  The token spelling table is the closed parser-facing join.
- The driver selects the data-and-pattern grammar when a file uses an owned
  token or tuple punctuation. First-stratum sources retain their established
  concrete parser and pipeline.
- `Type` adds nominal and tuple variants. Type admission, provenance traversal,
  display, registry validation, and coverage are the exhaustive consumers.
- The data-and-pattern pipeline owns declaration parsing, two-pass identity
  allocation, resolved registries, bidirectional checking, typed patterns,
  usefulness, validation, heap evaluation, matching, and observation.
- `Observation` and `Value` add one heap-backed result boundary. Existing
  scalar and closure observations retain their representations.

The exact audit below found 144 occurrences in seven production files at the
checkpoint. It locates declarations and consumers; it is not an edit count.

```text
rg -n \
  'TokenKind::(Type|Match|UpperIdentifier|Wildcard|Pipe|FatArrow)|'\
'Type::(Tuple|Nominal)|CheckedPattern|HeapCell' src
```

## What localized

Two-pass type and constructor allocation, expected-type pattern checking, the
shared usefulness relation, guarded-root analysis, heap cells, alias handling,
and active-path rendering have one implementation owner. Match arms,
equational clauses, and local irrefutability all call the same usefulness
function. Constructor expressions use ordinary unary application after one
registry lookup determines their type.

The explicit heap avoided Rust ownership cycles. Recursive data names denote
numeric slots; constructor cells and tuple cells contain numeric locations.
The 10,000-member cyclic group evaluates, renders, and drops on a 256 KiB host
stack. Iterative matching and rendering, rather than recursive Rust ownership,
make that boundary possible.

## What necessarily crossed stages

Nominal identity must survive resolution, type equality, constructor typing,
coverage, validation, evaluation, and source-facing type display. Tuple shape
likewise crosses parsing, typing, constructor payload metadata, pattern
checking, application, matching, and rendering. These are semantic facts, not
registration data.

Constructor-guarded recursion changes group initialization. Function templates
alone cannot represent it: all member slots must exist before initialization,
data initializers must run in source order, and completed slots alias their
constructed roots. Observation must retain the evaluation heap because a
cyclic value cannot be copied into an acyclic host enum.

## Maintenance mutations

Three deliberate uncommitted mutations tested discoverability. Each was
reverted with a targeted patch.

### Constructor registry accessor

Renaming `Registry::constructor` produced four unique missing-method errors in
`extended.rs`. The exact search `rg -n '\.constructor\(' src tests` found the
same four call sites: name lookup, payload coverage, witness display, and value
rendering. Rust exposed all production consumers in one check.

### Observed heap contract

Adding one required field to `ObservedHeap` produced one missing-field error at
the sole heap-freezing boundary. This confirms that evaluation-to-observation
ownership has one constructor.

### Type family

Adding a temporary `Type::Probe` variant produced six unique non-exhaustive
match errors in four files: Core payload admission, elaboration provenance,
the shared type display/equality owner, and three data-pipeline consumers. The
compiler located the closed semantic joins without a search. The wildcard in
the equality decision remained an intentional review point because a new type
must not compare equal accidentally.

After reverting all probes, `cargo check --all-targets` passed.

## Transfer from earlier evidence

DN-0007's central split transferred: tuples are structural, nominal sums use
declaration identity, constructors are ordinary values, patterns check against
expected types, local bindings require irrefutability, and matches and equations
share coverage. Records, polymorphic constructors, and access control did not
transfer because CP-0003 excludes them.

DN-0019's simplification rule also transferred. Ordinary application carries
payload constructors and higher-order construction. One typed pattern and
coverage representation serves three surface contexts. The new facts that
could not lower away—nominal registries, structured patterns, and heap
locations—remain explicit at validation and observation boundaries.

The recursive-definition evidence correctly predicted the runtime difference:
allocate-all-then-check scope transferred, while cyclic constructor data needed
preallocation and initialization rather than function templates alone.

## External notation tooling

The repository continues to use readable `ebnf` and `sequent` fences with
matching prose. The previously recorded lack of an external railroad or
sequent renderer remains outside this repository. This increment adds no
renderer dependency or conformance claim.
