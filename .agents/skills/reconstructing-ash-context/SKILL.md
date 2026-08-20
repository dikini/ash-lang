---
name: reconstructing-ash-context
description: Use when starting Ash design, implementation, QA, specification, documentation, or planning work and deciding which repository context is necessary.
---

# Reconstructing Ash Context

Reconstruct the smallest evidence set that can answer the task. Do not scan the repository or follow every link by default.

## Route

1. Read the repository's [AGENTS.md](../../../AGENTS.md); consult the [artifact guide](../../../docs/project/artifacts.md) only when an authority or lifecycle rule is unclear.
2. State the question, work role, and facts needed to answer it.
3. Before creating or editing project prose, read the [writing guide](../../../docs/project/writing.md).
4. Open the target artifact through its index. Start with that artifact and one authority check.
5. Add a source only to answer a named gap. `Related` links are candidates, not a reading queue. Inspect headings before loading sections of a long file.
6. Read relevant [specification](../../../spec/README.md) sections when making semantic claims. For product implementation, require an accepted proposal or decision, an active task, and relevant tests or invariants; stop if one is missing. A bounded design prototype instead requires a design note with a named question, comparison criteria, and disposal or retention conditions.
7. Record each source's authority and unresolved questions. Stop as soon as every required fact has evidence.

## Boundaries

Context reconstruction is read-only. It assembles evidence but does not authorize repository changes; the governing proposal, decision, or task determines any later write scope.

Do not read bootstrap plans, templates, unrelated notes, or historical Ash for background. Consult history only to answer a provenance question that current artifacts cannot answer.

Never promote a design note, trajectory item, proposal, task, test, or implementation detail into current Ash semantics.

## Verification

Link every context conclusion to its repository source. Confirm that semantic claims come from `spec/`, accepted non-language choices come from current decisions, and unknowns remain labeled as unknowns.
