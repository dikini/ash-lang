# Artifact guide

Ash keeps distinct artifacts because they carry different authority. Git history is the archive; the working tree contains only current artifacts and reusable templates.

## Current specification

The [specification](../../spec/README.md) answers “What is Ash now?” It is normative, describes `main`, and contains only implemented language and runtime behavior.

## Design notes

Design notes answer “What are we considering, and what remains uncertain?” They hold research, alternatives, experiments, tradeoffs, and future pressure. They are informative, not normative.

A note may also record an accepted design. `Status: accepted` records acceptance
of its explicitly named scope. State which parts are implemented, which are not
implemented, and which earlier choices are retired or superseded. Acceptance of
the implemented scope does not accept the note's remaining alternatives. Current
language rules stay in `spec/`; accepted non-language choices stay in
architectural decisions. A note's status does not replace either source.

A design note may govern a bounded disposable prototype when code is needed as evidence. Such a prototype tests a named question and comparison criteria. It is not product implementation, does not create specification truth, and must not become production architecture without a decision and task.

## Architectural decisions

Architectural decisions record accepted non-language choices such as parser architecture, Core representation, pass organization, repository workflow, or implementation tooling. Create one only after relevant exploration has converged.

## Change proposals

Change proposals describe proposed transitions in Ash semantics. They state current behavior, proposed behavior, semantic delta, affected specification areas, resulting truth, interactions, non-goals, and required evidence. A `proposed` proposal is under consideration. An `accepted` proposal may authorize tasks, but still does not describe current Ash. After one product checkpoint retains the implementation, tests, specification update, review, and verification, remove the proposal from that product branch. Git retains it as transition evidence. This cleanup prepares the branch's post-transition tree; it does not make the change current or replace integration into `main`.

## Tasks

Tasks plan and record authorized work, dependencies, progress, verification, discoveries, and deviations. They do not define language semantics. A semantic gap returns to the governing proposal or design work.

### Execution plans

An execution plan is a temporary project-management document owned by one active
task. It translates authorized work into ordered changes and verification steps.
It has no independent authority and cannot define semantics or architecture.
Link it from its task and remove it when the task finishes; Git retains the plan.

## Identity and references

Use a stable ID and a descriptive filename:

- `DN-0001-short-name.md` — design note;
- `AD-0001-short-name.md` — architectural decision;
- `CP-0001-short-name.md` — change proposal;
- `TASK-0001-short-name.md` — task.

Allocate the next number unused in both the current tree and Git history. Never reuse an ID. Keep metadata to `ID`, `Status`, and links to `Related` artifacts when relevant. Reference another artifact by both ID and relative link so the relationship remains readable without a generated index.

Templates are not numbered artifacts. Execution plans do not receive artifact
IDs. Remove completed, rejected, or superseded artifacts when they no longer
describe current project state; Git retains their reasoning and identity.

## Typical flows

Non-language architecture:

```text
research → design note → architectural decision → task → implementation
```

Language semantics:

```text
research → design note → change proposal → task
         → implementation + tests + specification update
```
