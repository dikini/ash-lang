# Import Ash Design Exploration

## Goal

Convert five user-supplied explorations into topical Ash reboot design notes that preserve useful ideas, proposed rules, alternatives, stress tests, and future pressure without defining current Ash or implying a roadmap commitment.

## Source reconstruction

Use these complete sources:

- `ash-surface-function-definitions-design-note.md`;
- `Ash V1 Type System — Initial Design Note.md`;
- `Ash Session Types — Stress Tests.md`;
- `Ash Kind Declarations and Type Promotion — Initial Design Note(1).md`;
- `Ash Algebraic Effects — Initial Design Note(1).md`, followed by `Ash Algebraic Effects — Initial Design Note (continued).md`, then `Ash Algebraic Effects — Initial Design Note (continued)(1).md`.

The earlier algebraic-effects and kind files are truncated and are not authoritative import sources. Preserve the complete source set in Git history before replacing it with adapted current artifacts.

## Topical structure

Create ten `Status: exploring` design notes:

- `DN-0005` — surface function definitions and elaboration;
- `DN-0006` — initial type-system scope, kinds, inference, and polymorphism;
- `DN-0007` — products, ADTs, patterns, and coverage;
- `DN-0008` — typed Core and elaboration architecture;
- `DN-0009` — effect APIs, rows, handlers, and continuations;
- `DN-0010` — typed identities and resource lifetimes;
- `DN-0011` — providers, modules, and static/dynamic resolution;
- `DN-0012` — coeffects and typed hook points;
- `DN-0013` — session and resource protocol stress tests;
- `DN-0014` — finite user-defined kinds and restricted promotion.

The split follows design questions rather than source-file boundaries. Related notes link to one another and to existing parser, Core, specification-methodology, and reboot-foundation context.

## Adaptation rules

Every note states that it is informative and does not define current Ash. Syntax and type notation are illustrative unless a later proposal and implementation establish them.

Replace unsupported commitments with their actual status:

- “v1 commitment” becomes a candidate for the first coherent language;
- “current direction” becomes a hypothesis or candidate direction unless existing repository evidence establishes it;
- “implementation obligation” becomes evidence required before a proposal or decision can converge;
- downstream features remain future pressure or stress tests and do not enter the development trajectory automatically.

Preserve substantive alternatives, rationale, examples, interactions, failure cases, and open questions. Remove duplicated continuation text, generated code-fence `id` attributes, repeated summaries, and prose that adds no information.

## Suggested design rules

Use a consistent `## Suggested design rules` section when source material proposes rules. Give each rule:

- a descriptive heading;
- a quoted `Suggested rule:` statement;
- nearby rationale or counterexample;
- links to relevant notes when the interaction is not local.

Suggested rules remain non-normative. Descriptive headings and the literal `Suggested rule:` marker make them searchable without creating a separate registry or metadata system.

## Index and trajectory

Update the design-note index with short topical descriptions and group notes for navigation. Do not add all imported topics to the development trajectory. Existing trajectory items may link to relevant notes only where that improves current context without changing maturity or priority.

## Verification

Build a source-section coverage map during conversion. Review every resulting note for topical cohesion, authority wording, and retained uncertainty. Check relative links, unique design-note IDs in the tree and history, searchable suggested rules, absence of generated fence IDs, and unchanged canonical specification truth.
