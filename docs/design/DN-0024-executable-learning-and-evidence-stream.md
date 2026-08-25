# DN-0024: Executable Learning and Evidence Stream

- ID: `DN-0024`
- Status: exploring
- Related: [AD-0002: Documentation System](../decisions/AD-0002-documentation-system.md),
  [DN-0016: First Mini-Ash Corpus Stratum](DN-0016-first-mini-ash-corpus.md),
  [DN-0019: Primitive Feature Composition](DN-0019-primitive-feature-composition.md),
  [DN-0020: Ash Dialect Milestones](DN-0020-ash-dialect-milestones.md),
  [CP-0005: Passive Static Modules](../proposals/CP-0005-passive-static-modules.md)

> This design note is informative. It governs the initial experiment with a
> separate executable learning and evidence stream under the scope and
> retention conditions below. It does not define current Ash, accept a
> permanent repository architecture, or make tutorial material a second
> specification.

## Question

Can a separately maintained, version-pinned documentation stream teach Ash,
reinterpret established programming works, exercise realistic applications,
and provide useful design evidence without becoming language authority or
imposing backward-compatibility work on Ash?

## Context

The [current specification](../../spec/README.md) defines one implemented
Mini-Ash dialect. The `mini-ash` Git tag retains that completed milestone, while
current source evolves toward Modular Ash as described by
[DN-0020](DN-0020-ash-dialect-milestones.md). The compiler does not keep old
dialects selectable merely to preserve earlier source programs.

The accepted [CP-0005](../proposals/CP-0005-passive-static-modules.md) proposes
replacing the single-file program root with passive modules and a `main`
entrypoint. That behavior is not current Ash until its implementation, tests,
and specification land together. The pending source-shape transition makes a
small, migratable pilot more useful than a large Mini-Ash translation effort.

Ash already uses executable examples in the specification and tool guide. The
first Mini-Ash corpus also showed that a shared set of programs can pressure
syntax, typing, diagnostics, Core representation, and evaluation together.
That corpus was design and implementation evidence. It was not organized to
teach programmers, adapt established algorithms, or explore complete
applications.

The [documentation policy](../project/documentation.md) keeps explanatory
language material subordinate to the specification and tool documentation
subordinate to tested behavior. A larger learning stream must preserve that
boundary while moving at a different cadence from the compiler repository.

Established textbooks provide more than example syntax. They carry design
methods, data-structure invariants, algorithm derivations, complexity
arguments, and application techniques. Reinterpreting those ideas in Ash can
teach the language and expose pressure for libraries, effects, state, resource
handling, concurrency, and richer types. Blindly translating chapters would
lose that purpose and create unnecessary copyright and maintenance risk.

## Constraints

### Keep authority one-way

Published tutorials explain the Ash version they target. Their language claims
derive from that version's specification. A tutorial, executable case, test,
stress result, or external repository convention cannot create Ash semantics.

When tutorial behavior and its source of truth disagree, classify the finding:

- correct tutorial mistakes against the specification;
- minimize implementation failures of specified behavior as Ash regressions;
- return unspecified semantic questions to design or proposal work;
- retain library, tooling, diagnostic, and performance pressure without
  presenting it as a language change.

### Treat teaching and stress as the same work viewed differently

The stream has three equal content families:

- tutorials that teach Ash and program design;
- structures, algorithms, and development techniques adapted from established
  work;
- realistic application cases such as deterministic automation, data
  transformation, interpreters, services, and web systems.

Stress evidence crosses every family. A case should teach a coherent idea and
state which language, implementation, diagnostic, library, or application
boundary it exercises. The publication need not form one connected textbook,
but prerequisites must make useful reading paths possible.

### Make code executable

Every displayed code block presented as runnable must be transcluded from a
canonical source file or checked for exact agreement with it, regardless of
language or content family. Test it with the applicable executor, compiler, or
parser. A successful Ash example asserts its value, type, output, and exit
status as applicable. An intentional Ash rejection asserts the stable reason
and relevant source location on which its explanation depends. Scripts,
configuration, and host-language harness code receive equivalent checks for
the behavior the text presents.

Execution alone is insufficient. Each substantive adapted unit must explain,
as relevant, the problem, representation and invariants, construction or
derivation, cost, and departures from its source material. The explanation
should preserve the source's intellectual purpose while making the Ash-specific
choices explicit. Elementary examples need only the explanation required for
their learning outcome.

Pseudocode, transcripts, possible future Ash, and incomplete fragments must be
identified as non-executable and must not use a runnable language's code fence.
Laboratory code may target an experimental compiler only when an immutable
retained ref or source artifact keeps that target fetchable and the case records
its build instructions. A commit name on a disposable branch is insufficient.
The code must execute against that target and remain visibly separate from
published tutorials.

Application tests must be deterministic and hermetic. Checked-in fixtures,
temporary directories, controlled clocks or randomness, and loopback services
are appropriate as the language gains those capabilities. A live public
service is not a documentation test dependency.

### Move forward without maintaining old editions

A published edition pins a named Ash milestone and the tag's exact commit. Old
editions remain available through Git tags or immutable builds. New material,
corrections, and migrations move forward; the experiment does not require
backports or source compatibility with earlier Ash dialects.

Every published view must display its Ash milestone and resolved commit without
requiring a reader to inspect repository metadata.

An upstream-main canary is a discovery channel, not the publication contract.
A canary failure may reveal an intentional transition, a regression, or a
documentation assumption. It must not silently retarget the published edition.

### Preserve source integrity

Each adapted unit records its source, edition, intellectual contribution, and
material actually used. Exposition and Ash code should be original by default.
Do not copy prose, exercise statements, or solutions merely because a source is
available online. Review the applicable license before adapting any protected
expression or redistributing source material.

## Candidate repository directions

### Documentation inside `ash-lang`

Keeping the complete stream in this repository would make compiler and tutorial
changes atomic. It would also place a growing curriculum, its research records,
application fixtures, and scheduled stress workloads in the compiler's routine
development path. A worktree could isolate authors locally, but it would not
separate repository history, dependencies, review load, or CI cost.

### Separate version-pinned repository

A separate repository can record one published Ash target while probing newer
targets independently. It can choose documentation tooling, accept a larger
corpus, and run scheduled application workloads without burdening routine Ash
verification. Its cost is explicit cross-repository coordination and a delay
between an Ash transition and the next complete documentation edition.

This is the leading direction for the initial experiment.

### Separate repository with an upstream contract subset

The full stream could remain external while a curated subset becomes Ash
regression evidence. This gives language changes early downstream coverage but
adds ownership and duplication decisions. It should emerge only after the
external corpus identifies durable obligations worth retaining upstream. The
pilot must not create a second copy of every tutorial program in `ash-lang`.

## Leading repository model

The initial documentation repository should contain these conceptual areas:

```text
content/learn/          sequenced and focused Ash tutorials
content/cases/          structures, algorithms, and techniques
content/applications/   deterministic application slices
lab/                    versioned pressure cases and design experiments
research/sources/       source evaluations and adaptation records
```

This layout is a starting constraint, not an accepted choice of renderer,
manifest format, test framework, or repository name. Prefer unit-local prose,
programs, fixtures, and metadata so that one case can be understood and tested
without reconstructing an unrelated global build convention.

Each unit needs a stable case identity and should record:

- publication, laboratory, or migration state;
- exact Ash target;
- applicable specification sections or governing design note;
- learning prerequisites and outcomes;
- difficulty, Ash features, and stress dimensions exercised;
- source references and adaptation notes;
- commands and expected observations;
- known limitations and resulting evidence links.

The repository should apply Ash's [writing guide](../project/writing.md) to its
prose. It may define additional editorial rules, but those rules cannot change
the authority or status of Ash artifacts.

## Coverage discipline

The repository should maintain a coverage view across learning prerequisites,
difficulty, Ash features, programming techniques, structure and algorithm
families, application domains, source traditions, positive and negative cases,
and stress dimensions. Use that view to select work and expose omissions. It is
not a language-conformance claim or a target to maximize feature counts in each
example.

Early units should combine accessible and demanding programs rather than
finishing all elementary material before beginning advanced cases. A small
teaching example may isolate one idea; a harder case should exercise several
ideas whose interaction matters. Independent units are preferable when a
forced chapter sequence adds no pedagogical value.

## Version and migration workflow

An immutable documentation source tag preserves each published edition; a
rendered build publishes it. The documentation repository's `main` branch is
the one active forward line. Do not maintain a branch for an older edition or
merge new work backward. During a migration, the last edition remains
published from its tag while `main` is visibly incomplete and targets the next
exact Ash commit. Remove unmigrated units from the current tree, record them in
the migration inventory, and restore them from the prior tag as they pass the
new target. Publish a new tag only after the intended coverage is coherent.

The published edition pins a milestone tag and its resolved commit. Every
change to a published unit or shared renderer, harness, dependency, or build
rule runs the complete executable documentation suite against that target.

The repository also tests the complete published suite periodically against an
exact `ash-lang` `main` commit. A smaller sentinel set may provide more frequent
signal when its coverage is stated. These canaries report compatibility without
changing the published pin. Laboratory cases may name other immutable
experimental targets when an Ash design note governs the question, comparison
criteria, and disposal condition.

A repository-visible compatibility record should name the publication pin, the
latest tested `ash-lang` `main` commit, the cases run, the result, and any open
migration or evidence work. Classify a canary failure rather than leaving the
record red without explanation. The canary may remain non-blocking for
`ash-lang`; its purpose is to expose downstream pressure without coupling both
repositories' routine verification.

The pilot should detect an advanced `ash-lang` `main` at least daily and run the
sentinel set against it. Run the complete published suite at least weekly and
before selecting a forward migration target. Record a canary as stale when
these intervals are missed; a stale result is not compatibility evidence.

When an intentional Ash transition breaks the published corpus, classify the
old-edition result as expected incompatibility and link the forward migration
inventory. Pin the active forward line to an exact current commit and restore a
green representative sentinel before expanding the migration. The published
edition remains unchanged until the forward line is coherent and a new
milestone is available.

A forward migration follows these steps:

1. preserve the current documentation source with an immutable tag and publish
   its rendered build;
2. after the Ash transition is implemented and specified, move the active
   `main` line to an exact current target and mark it as a migration;
3. include a unit in the next rendered edition only after all of its Ash code
   passes against the new target;
4. track omitted units in a migration inventory rather than publishing broken
   examples;
5. when the Ash milestone tag is available, verify the coherent forward line
   against its resolved commit, then publish the next edition; and
6. stop maintaining the earlier edition.

The migration need not preserve old syntax or explanations. It should preserve
the pedagogical or algorithmic idea when that idea remains useful, and explain
how the new Ash boundary changes its expression.

## Cooperative evidence flow

### From documentation to Ash

A documentation discovery begins in its complete problem context. An evidence
candidate should identify the case and exact commits, the user-level task, its
source tradition, executable observations, the blocked or costly boundary, and
the significance of the finding beyond one example.

If Ash adopts the finding, adapt the smallest distinguishing cases into the
relevant design note and link the richer external case at an immutable commit.
The Ash note owns the design question, alternatives, comparison criteria, and
retention decision. The external case continues to own the pedagogical or
application explanation.

Do not send every documentation program upstream. A failure of current
specified behavior may become a minimized regression test. When selected for
upstream investigation, a capability gap enters a design note as pressure and
establishes no obligation by itself. A non-language, tool, diagnostic, or
resource case may test an obligation only after its governing decision, policy,
or implemented contract accepts that obligation. After a semantic change
becomes implemented specification truth, a representative documentation case
may become a retained language test.

One case may expose pressure; a new language mechanism normally needs several
cases, contrary evidence, and an explanation of why existing semantics or a
library cannot meet the need.

### From Ash to documentation

An Ash design note may request pressure from a class of problems. It should
state the current boundary, candidate mechanisms, positive and negative cases,
and the observations that would distinguish them. The documentation laboratory
can then supply a small teaching case, an established structure or algorithm,
a realistic application boundary, and a scaled stress case where each adds
different evidence.

Results return to the design note. A semantic direction still proceeds through
a change proposal and an authorized task. Implementation, positive and
negative tests, and specification changes land together before the feature
becomes ordinary tutorial material.

When a feature becomes current Ash, the forward documentation line interprets
it through concrete programs. Experimental comparison prose does not
automatically become a tutorial; rewrite it around the behavior Ash actually
retained.

### Experimental code lifecycle

Laboratory programs are evidence, not published Ash examples. Each experiment
names its governing Ash design note, immutable executable target, and build
instructions. If Ash disposes that target, remove the external laboratory case
after retaining its observations unless the governing evidence package retains
a fetchable source artifact. If Ash rejects the direction, retain the
observations in the governing artifacts and remove obsolete laboratory code
from the current documentation tree. If Ash implements the capability, adapt
the case to current syntax and graduate it only after the specification is
current.

### Stress observation lifecycle

Correctness checks and stress measurements serve different purposes. A stress
record should identify the program or generator, input size and seed when
applicable, Ash target, compiler or runtime phase, semantic observation,
termination or failure result, measured time, memory, or stack conditions,
execution environment, and repetition method. Record only fields relevant to
the question under test.

Machine-specific measurements are evidence by default, not pass thresholds or
language guarantees. A threshold becomes a required gate only when the
specification, an accepted decision, or an implemented tool contract owns it.
Keep small deterministic correctness cases in per-change verification and run
larger measurements on a stated schedule so results remain repeatable and
comparable across Ash targets.

## Research program

Select sources by the contribution they make rather than by an attempt to port
their tables of contents. Evaluate at least:

- pedagogical method and prerequisite structure;
- structures, algorithms, or techniques not already represented;
- executable examples, independent expected results, and complexity evidence;
- pressure on current and plausible future Ash capabilities;
- lasting problem content rather than framework-specific fashion;
- edition, access, attribution, and licensing constraints; and
- which material should deliberately remain outside the stream.

The following sources seed the survey; selection remains part of the pilot.

| Source | Candidate contribution |
| --- | --- |
| [*How to Design Programs*, second edition](https://mitpress.mit.edu/9780262344128/how-to-design-programs/) | Systematic program-design recipes, examples, tests, structural recursion, abstraction, and pedagogical progression. |
| [*Structure and Interpretation of Computer Programs*, second edition](https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/6515/sicp.zip/index.html) | Procedural abstraction, data abstraction, interpreters, state, and changing models of computation. |
| [*Purely Functional Data Structures*](https://www.cambridge.org/core/books/abs/purely-functional-data-structures/contents/9DA321DB54345B01758FE0107B9824E2) | Persistence, strict and lazy representations, amortization, numerical representations, and bootstrapping. |
| [*Pearls of Functional Algorithm Design*](https://www.cambridge.org/core/books/pearls-of-functional-algorithm-design/B0CF0AC5A205AF9491298684113B088F) | Self-contained problems, equational derivation, functional pearls, and comparisons with direct specifications. |
| [*Algorithm Design with Haskell*](https://www.cambridge.org/core/books/algorithm-design-with-haskell/824BE0319E3762CE8BA5B1D91EEA3F52) | Divide and conquer, greedy methods, thinning, dynamic programming, exhaustive search, and correctness reasoning. |
| [*Introduction to Algorithms*, fourth edition](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/) | Broad classical coverage and an imperative comparison point when Ash gains state and mutation. |
| [*Programming Languages: Application and Interpretation*](https://www.plai.org/) | Interpreters as executable programs and pressure on representation, binding, state, and language implementation. |
| [*Concepts, Techniques, and Models of Computer Programming*](https://mitpress.mit.edu/9780262220699/concepts-techniques-and-models-of-computer-programming/) | A progression from declarative programming through explicit state, concurrency, and distributed models. |
| [*The Practice of Programming*](https://www.pearson.com/en-us/subject-catalog/p/practice-of-programming-the/P200000009026) and [*The Unix Programming Environment*](https://www.pearson.com/en-us/subject-catalog/p/unix-programming-environment-the/P200000000349) | Testing, debugging, notation, performance, portability, filters, and deterministic automation tasks. |
| [*Domain Modeling Made Functional*](https://pragprog.com/titles/swdddf/domain-modeling-made-functional/) | Typed domain models, workflows, validation, and application boundaries. |
| [*Designing Data-Intensive Applications*](https://dataintensive.net/) | Data pipelines, storage, streaming, reliability, and distributed-system pressure; use as a source of workloads and invariants rather than code to translate. |

The survey should also consider individual functional pearls and established
works in parsing, databases, distributed systems, testing, and software design
when they add a case that the initial books do not cover.

## Initial experiment

The pilot may create a separate documentation repository. Its first published
target should be the `mini-ash` tag and exact commit. The initial corpus should
remain small enough to migrate or discard.

Candidate pilot coverage includes:

- a short learning path through functions, algebraic data, patterns,
  recursion, and rank-1 polymorphism;
- one persistent structure whose invariant and cost can be explained in
  the pinned Mini-Ash target;
- one algorithm or small interpreter that combines several features of that
  target;
- one deterministic application kernel over explicit input and output data;
- positive, negative, and scaled cases that exercise the compiler and
  evaluator; and
- at least one honest capability-gap record for an end-to-end boundary that
  the pinned target cannot express.

Mini-Ash has no modules, strings, I/O, effects, mutation, networking, or general
laziness. The pilot may model a pure transformation or planning kernel, but it
must not describe that kernel as a complete ETL tool, automation runner, or web
application. Those vertical cases join later editions when Ash can execute
their environmental boundaries.

## Evidence and retention

The pilot should record:

- time required to add and explain one unit;
- time and failure classes involved in advancing the Ash pin;
- documentation build and test cost;
- whether readers can distinguish published and experimental behavior;
- coverage across pedagogy, target features, difficulty, and application
  domains;
- evidence candidates produced by the corpus;
- cases requested by Ash design work and the observations they return; and
- source-provenance and adaptation-review cost.

Retain the separate-repository model through an architectural decision only if
the pilot keeps published code executable, makes version status unambiguous,
supports forward migration without backports, and produces transferable
evidence at an acceptable coordination cost.

If cross-repository lag obscures current behavior, experimental targets confuse
readers, or maintenance cost dominates content and evidence work, archive the
pilot repository after retaining its findings. Compare a monorepo stream or a
smaller external corpus with a curated upstream subset before continuing.

## Open questions

- What repository name, renderer, and executable-example harness best fit the
  pilot without constraining later application tests?
- How should the documentation repository expose incomplete forward migrations
  without presenting them as supported editions?
- Which stable case-identity and manifest format gives cross-repository links
  enough durability without adding a registry maintenance burden?
- What threshold should promote a documentation finding into an Ash design
  note or retained regression test?
- Which first application kernel provides realistic pressure while staying
  honest about Mini-Ash's pure single-file boundary?
