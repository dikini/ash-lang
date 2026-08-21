---
name: reconstructing-ash-context
description: Use when starting Ash design, implementation, QA, specification, documentation, or planning work, especially when prior experiments or downstream pressure may affect the goal.
---

# Reconstructing Ash Context

Reconstruct the smallest causal semantic model that can explain the task. The
goal is understanding, not a reading receipt.

## Semantic readiness

Context is sufficient when you can explain:

- current Ash behavior affected by the goal;
- accepted boundaries and invariants the change crosses;
- prior experiments whose positive or contrary evidence transfers;
- downstream pressure that could make the obvious approach short-lived;
- whether existing semantics, elaboration, or future libraries could remove
  part of the proposed mechanism;
- important exclusions and why they do not apply.

For architecture-sensitive work, share this synthesis briefly before planning.
Do not replace it with a document list or persist a research-intake checklist.

## Retrieval

1. Read [AGENTS.md](../../../AGENTS.md) and the
   [writing guide](../../../docs/project/writing.md). Use the
   [artifact guide](../../../docs/project/artifacts.md) for authority and
   lifecycle questions.
2. State the semantic question and the affected pipeline boundaries. Read the
   applicable current specification and accepted decisions first.
3. Search design indexes, headings, and text using the concepts and
   relationships in the goal. Treat `Related` links as evidence hints, not a
   complete reading queue.
4. Challenge the initial model: which design note, experiment, or downstream
   feature pressure would object to the simplest implementation? Read only the
   material needed to resolve that challenge.
5. Transfer an experimental finding only within its tested scope. Include
   contrary evidence and reject experiment-specific machinery that the goal
   does not need.
6. Stop when the semantic-readiness explanation is supported. Do not scan every
   note or follow every link by default.

Read relevant [specification](../../../spec/README.md) sections for semantic
claims. Product implementation requires an accepted proposal or decision, an
active task, and relevant tests or invariants. A bounded design prototype
requires a design note with a named question, comparison criteria, and disposal
or retention conditions.

## Boundaries

Context reconstruction is read-only. It assembles evidence but does not
authorize repository changes; the governing proposal, decision, or task
determines any later write scope.

Do not read bootstrap plans, templates, unrelated notes, or historical Ash for
background. Consult history only to answer a provenance question that current
artifacts cannot answer.

Never promote a design note, trajectory item, proposal, task, test, or
implementation detail into current Ash semantics.

## Verification

Link every context conclusion to its repository source. Confirm that semantic
claims come from `spec/`, accepted non-language choices come from current
decisions, and unknowns remain labeled as unknowns.
