# Task: Establish the Ash Reboot Project Foundation

Establish the initial project foundation for the Ash language reboot.

The repository contains `Ash Reboot Foundations.md`. Read it completely before making changes. Treat it as the primary statement of development principles, architectural constraints, artifact discipline, and current design direction.

It is **not** the Ash language specification. Do not turn speculative or future ideas from that document into current language requirements.

## Goal

Create the smallest useful repository foundation that allows future human contributors and coding/design agents to:

- understand what Ash currently is;
- understand why the project is organized as it is;
- distinguish current truth from proposals, exploration, decisions, and implementation work;
- reconstruct the minimum sufficient context for a task;
- begin the first design and implementation work without inventing project process ad hoc.

Optimize for clarity and context reconstruction, not process sophistication.

## First: inspect the repository

Before changing anything:

1. Inspect the complete current repository tree.
2. Read all existing root-level project instructions and relevant documentation.
3. Read `Ash Reboot Foundations.md` completely.
4. Inspect repository history when it helps determine whether something already has an established meaning.
5. Identify existing conventions that should be preserved rather than replaced.

Do not assume the repository is empty.

Do not copy historical material from the old `/home/dikini/Projects/ash-lang/dikini/ash` repository into this repository. Historical Ash is evidence, not authority.

## Establish the repository structure

Create a minimal structure for the following artifact classes where appropriate:

- current specification;
- design notes;
- architectural decisions;
- change proposals;
- implementation tasks;
- development trajectory;
- project/development documentation;
- agent instructions and skills.

Choose simple names and organization.

Do not introduce directories merely because they might become useful later.

Do not create an archive for superseded documents. Git history is the archive.

## Establish the root documentation

Create or update the root `README.md`.

It should be a concise entry point that explains:

- what this repository is;
- the purpose of the Ash reboot;
- the relationship to historical Ash;
- the current maturity of the project;
- where the canonical specification is;
- where design exploration, decisions, proposals, tasks, and trajectory live;
- where contributors and agents should start.

Keep the README navigational. Move detailed process documentation elsewhere.

Create or update `CONTRIBUTING.md` if it provides useful contributor-facing guidance that does not duplicate `AGENTS.md`.

## Establish agent guidance

Create a concise root `AGENTS.md`.

Its central principle should be:

> Reconstruct the minimum sufficient context for the task from the repository rather than relying on remembered knowledge of Ash.

Define how an agent should gather context for at least:

- design work;
- implementation work;
- QA/testing;
- specification/documentation work;
- planning.

Make clear that agents must distinguish:

- current specification truth;
- accepted decisions;
- proposed changes;
- active implementation work;
- exploratory or speculative design.

An implementation task must not silently invent language semantics. If implementation reveals that proposed semantics are wrong or incomplete, return to the relevant design/proposal rather than encoding a local semantic decision in the implementation.

Keep `AGENTS.md` short enough to function as an entry point. Put detailed reusable instructions into project rules or agent skills where that improves context locality.

## Establish artifact conventions

Define lightweight conventions and templates for:

### Design notes

Used for exploration, research, alternatives, experiments, tradeoffs, uncertainty, and future architectural pressure.

They are informative, not normative.

### Architectural decisions

Used when an important non-language architectural or project decision has converged.

Examples include parser architecture, Core representation, compiler pass organization, repository workflow, or implementation tooling.

### Change proposals

Used for proposed changes to Ash semantics.

A proposal should make clear:

- current behavior;
- proposed behavior;
- semantic delta;
- affected specification areas;
- resulting specification truth;
- interactions;
- non-goals;
- required evidence.

A proposal does not describe current Ash until implementation, tests, and specification changes merge.

### Tasks

Used to plan and record implementation work.

Tasks may contain dependencies, work, progress, verification, discoveries, and deviations.

Tasks do not define language semantics.

## Artifact identity

Introduce a small stable-ID convention if doing so remains lightweight.

A reasonable starting shape is:

- `DN-0001` — design note
- `AD-0001` — architectural decision
- `CP-0001` — change proposal
- `TASK-0001` — task

Keep metadata minimal.

Do not create a large manually maintained metadata system.

Prefer information derivable from repository content and Git history.

## Establish specification discipline

Create documentation describing how the Ash specification relates to implementation.

The invariant is:

> The canonical specification describes exactly the Ash implemented on `main`.

The specification is normative.

It must contain only implemented language/runtime behavior.

Future features, partially implemented semantics, and desired behavior belong elsewhere.

Specification changes for language behavior should merge together with the implementation and tests that make those statements true.

Do not populate the specification with the intended future Ash language.

If no executable Ash language currently exists, say so plainly. A tiny truthful specification is better than a detailed speculative one.

Also capture the current methodological question around formal semantics without prematurely resolving it unless the repository already contains an accepted decision.

## Establish writing guidance

Create concise project writing guidance based on `Ash Reboot Foundations.md`.

In particular:

- prefer plain, direct language;
- prefer active voice;
- remove words that add no information;
- distinguish facts, decisions, and ideas;
- keep explanation proportional to commitment;
- avoid unnecessary jargon;
- avoid architecture-by-adjective;
- prefer concrete properties over words such as "extensible", "robust", "modular", or "scalable";
- prefer nouns and verbs over adjectives;
- avoid overexplaining and overdesigning.

Use this guidance in the documents you create.

## Establish development trajectory

Create a lightweight representation of the current development trajectory.

Do not create one giant sequential roadmap.

Represent dependencies and maturity separately where useful.

Near-term work may be detailed.

Distant work should preserve intent, dependencies, major interactions, architectural pressure, and large risks without pretending unresolved decisions have been made.

Future architectural pressure may be expressed using:

- Current work MUST
- Current work MUST NOT
- Current work NEED NOT

Do not turn the full future Ash feature inventory into planned implementation work.

## Seed immediate design work

Create initial design-note skeletons for:

1. Core representation;
2. parser architecture.

Populate them only with design intent, constraints, questions, candidate directions, and experiments actually supported by `Ash Reboot Foundations.md`.

Do not prematurely turn either into an architectural decision.

For Core, preserve the distinction between a Freer-like semantic direction and commitment to a particular concrete encoding.

For the parser, preserve the distinction between normative grammar and parser implementation architecture.

## Agent skills

Create only a small number of high-value project-local agent skills.

Prefer role-oriented skills such as:

- context reconstruction;
- design work;
- implementation work;
- QA/testing;
- specification work.

Avoid creating many tiny skills.

Each skill should tell an agent:

- when to use it;
- what context to reconstruct;
- which artifact types are authoritative for that work;
- what it may change;
- what it must not infer or decide locally;
- how to verify the result.

Avoid duplicating large amounts of project documentation inside skills. Link to canonical project documents where possible.

## Tooling

Establish only tooling justified at this stage.

Basic repository-neutral files such as `.gitignore` or `.editorconfig` are appropriate when useful.

Do **not** choose a compiler implementation language, build system, package manager, CI stack, formatter, linter, parser framework, or other implementation-specific tooling unless that decision is already established by repository evidence.

If the implementation environment is unresolved, record it as an explicit early architectural/design decision that needs to be made.

Do not solve it implicitly while bootstrapping the repository.

Do not build sophisticated artifact-validation or graph tooling yet.

The intended progression is:

1. repository structure and templates;
2. validation after conventions have been exercised;
3. derived artifact/reference graph;
4. history/context queries;
5. agent-oriented context assembly.

We are establishing the first stage.

## Keep the foundation small

Apply this test to every new file, rule, directory, template, and field:

> Does this materially reduce uncertainty or make future context reconstruction cheaper?

If not, leave it out.

Do not build a project-management system.

Do not build a knowledge-management system.

Do not encode speculative future requirements as current process.

Do not create boilerplate merely because mature projects commonly contain it.

## Validate the result

Before finishing:

1. Review every created or modified file.
2. Check links and references.
3. Check that artifact terminology is consistent.
4. Check that normative and informative material are clearly separated.
5. Check that no speculative language feature has accidentally become current specification truth.
6. Check that no task or design note is being treated as normative semantics.
7. Check that historical Ash has not been imported as current authority.
8. Check that the repository can answer, or clearly point toward answering:

   - What is Ash now?
   - Why is it designed this way?
   - What is changing?
   - What work is active?
   - What remains uncertain?
   - Where did this information come from?

9. Remove unnecessary boilerplate discovered during review.

## Deliverable

Implement the foundation directly in the repository.

When finished, report:

- the resulting repository structure;
- files created or substantially changed;
- the purpose of each major artifact;
- important conventions established;
- decisions deliberately left unresolved;
- any conflicts or ambiguities found in the foundations;
- recommended next steps.

Do not begin substantial Ash compiler implementation as part of this task.

The objective is to leave behind a small, coherent development environment from which the reboot can begin correctly.