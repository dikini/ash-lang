# Semantic Context Workflow Design

## Goal

Make prior Ash research influence later Mini-Ash work without adding a new
catalogue, mandatory research ledger, or large reading checklist.

## Problem

Ash already separates specifications, decisions, proposals, tasks, design
notes, and experiments by authority. The documents contain substantial design
context and links. The failure is retrieval and synthesis: an agent can satisfy
the explicit artifact rules while reading only the nearest authority and
missing transferable evidence, downstream pressure, or opportunities to
simplify the proposed feature.

Adding more metadata and mandatory tables would make compliance easier to
audit, but would compete with semantic reasoning and duplicate the current
catalogue.

## Design

Keep the artifact structure and change the context-reconstruction outcome.
"Minimum sufficient context" means the smallest causal semantic model that
explains:

- current Ash behavior affected by the goal;
- accepted boundaries and invariants crossed by the change;
- prior experiments with transferable positive or contrary evidence;
- downstream pressure that could make the obvious implementation short-lived;
- opportunities to express the feature through existing semantics,
  elaboration, or future libraries;
- intentionally excluded information and why it is not relevant.

The agent searches by concepts and relationships as well as `Related`
metadata. It challenges the initial result by asking which design note or
experiment would object to the simplest proposed implementation. It stops when
it can explain the causal model, not merely when it has found an authorizing
artifact.

For architecture-sensitive work, the agent gives the user a short semantic
context synthesis before planning. This is disposable conversation context,
not a committed task form.

## Research preservation

Experiments retain detailed evidence and runnable code at stable commits. A
current design note preserves a short general finding using vocabulary that
future goal-driven searches can discover. The finding states its tested scope,
contrary evidence, and what it does not establish. It does not become current
language truth or accepted architecture.

The Float experiment should therefore contribute a concise finding about
cross-stage representation pressure, feature-owned behavior, maintenance
discovery, and simplification before composition. The detailed experimental
branch remains available for reproduction and comparison.

## Repository changes

- Revise `.agents/skills/reconstructing-ash-context/SKILL.md` around semantic
  readiness rather than a minimal reading sequence.
- Add one concise routing sentence to `AGENTS.md`; do not add a trigger table or
  document checklist.
- Add an informative primitive-feature composition note on `main` containing
  the distilled findings and links to the retained experiment commit and
  evidence location.
- Link the note from the existing design-note index.
- Add a behavioral fixture that evaluates context synthesis for a recursion
  goal. It should verify relationships and exclusions rather than exact prose
  or a list of files.

## Validation

Use a recursion pressure scenario before and after the skill change. A useful
result must connect recursion to binder identity, recursive scope and typing,
Core validation, closure or environment representation, and explicit-machine
evaluation. It must transfer the general representation-pressure finding from
Float while excluding Float CLI and operator machinery. It must also consider
whether recursion lowers through existing binding and function forms before
assuming a new representation.

Repository verification checks Markdown style, links, authority language, and
the normal project verifier. The experiment remains informative and no
specification file changes.
