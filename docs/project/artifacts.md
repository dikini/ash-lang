# Artifact guide

Ash keeps distinct artifacts because they carry different authority. Git history is the archive; the working tree contains only current artifacts and reusable templates.

## Current specification

The [specification](../../spec/README.md) answers “What is Ash now?” It is normative, describes `main`, and contains only implemented language and runtime behavior.

## Design notes

Design notes answer “What are we considering, and what remains uncertain?” They hold research, alternatives, experiments, tradeoffs, and future pressure. They are informative, not normative.

## Architectural decisions

Architectural decisions record accepted non-language choices such as parser architecture, Core representation, pass organization, repository workflow, or implementation tooling. Create one only after relevant exploration has converged.

## Change proposals

Change proposals describe proposed transitions in Ash semantics. They state current behavior, proposed behavior, semantic delta, affected specification areas, resulting truth, interactions, non-goals, and required evidence. A proposal does not describe current Ash until its implementation, tests, and specification update merge together.

## Tasks

Tasks plan and record authorized work, dependencies, progress, verification, discoveries, and deviations. They do not define language semantics. A semantic gap returns to the governing proposal or design work.

## Identity and references

Use a stable ID and a descriptive filename:

- `DN-0001-short-name.md` — design note;
- `AD-0001-short-name.md` — architectural decision;
- `CP-0001-short-name.md` — change proposal;
- `TASK-0001-short-name.md` — task.

Allocate the next unused number within the artifact class. Never reuse an ID. Keep metadata to `ID`, `Status`, and links to `Related` artifacts when relevant. Reference another artifact by both ID and relative link so the relationship remains readable without a generated index.

Templates are not numbered artifacts. Remove completed, rejected, or superseded artifacts when they no longer describe current project state; Git retains their reasoning and identity.

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
