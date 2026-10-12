# Documentation policy

Ash documentation belongs to one of four domains. Classify a document before
deciding what governs it, when it changes, and how to verify it.

When documentation disagrees with its source of truth, correct the documentation
unless the governing workflow changes both together. A document cannot create
language semantics, architecture, or tool behavior merely by describing it.

Grammar productions and Gentzen-style inference rules follow the
[formal-notation guide](notation.md). The notation controls their Markdown
representation; it does not change the authority of the containing document.

## Project-management documentation

This domain contains design notes, architectural decisions, change proposals,
tasks, the development trajectory, and task-owned execution plans.

The artifact type determines authority. The canonical specification remains the
only source of current Ash semantics. An accepted architectural decision governs
current non-language architecture. Proposals, tasks, plans, and design notes do
not define current Ash.

Update these documents with the work they describe. An execution plan belongs to
one active task, has no independent authority, and leaves the current tree when
the task finishes. Other artifact lifecycles follow the artifact guide.

Verify required sections, IDs, status, relationships, authority boundaries, and
the evidence named by the artifact.

## Ash language and tool documentation

This domain contains the normative specification, explanatory language material,
and documentation for the compiler, interpreter, REPL, and related Ash tools.

Language claims derive from `spec/`. Explanatory material must agree with the
current specification and must label proposed or future behavior. A language
change updates implementation, positive and negative tests, and the specification
together through the proposal workflow.

Tool claims derive from implemented and tested tool behavior. Documentation must
not present an implementation accident as a language rule. Update tool
documentation with changes to documented commands, inputs, outputs, diagnostics,
configuration, or platform behavior.

When language or tool behavior ceases to be current, update or remove its
documentation in the same change. Git retains the superseded text.

Verify semantic claims against `spec/`, language examples against required tests,
and documented tool behavior against the implementation. Test examples when
executable support exists.

## Rust crate documentation

This domain contains crate-level documentation, Rust API documentation, examples,
and descriptions of errors, invariants, and safety obligations.

The implemented Rust API and its tests constrain this documentation. Crate
documentation explains implementation interfaces; it does not define Ash
semantics. Update it with the API, invariant, error behavior, or safety obligation
it describes.

When an API, error behavior, invariant, or safety obligation ceases to exist,
update or remove its documentation in the same change. Git retains the
superseded text.

`cargo xtask verify` builds workspace documentation with warnings denied. The
workspace denies broken intra-doc links. Review API contracts, examples, errors,
invariants, and safety explanations with the relevant code change.

## Project documentation

This domain contains root and directory README files, contributor and agent
guides, development policies, and material not owned by another domain.

The decision, policy, implementation, or specification being described remains
authoritative. This domain is a catchall for subject matter, not authority.

Update project documentation with contributor setup, repository workflow, policy,
or project structure. Link new documents from the relevant index. Correct or
remove stale instructions.

Verify changed Markdown against the writing guide and Markdown lint. Check
relative links and documented commands. Confirm that normative, accepted,
proposed, and informative statements retain their actual status.

## Working records and build history

Keep useful working records while a PR is live, including current handoffs,
review notes, and verification receipts and logs needed for review or repair.

Preserve lasting conclusions in the appropriate documentation. Record measured
results with their scope and limits; consolidate durable findings rather than
copying the build chronology into a guide or decision.

After PR closure, discard obsolete build history. Keep records still needed by
another live PR or active checkpoint until that need ends. Retain compatible
build caches that serve continuing work. Worktree retirement follows
[AD-0011](../decisions/AD-0011-milestone-worktree-lifecycle.md).

## Current verification boundary

`cargo xtask verify` enforces Rust formatting, build, lint, tests, and rustdoc
checks. Documentation classification, artifact structure, Markdown lint, relative
links, command accuracy, and authority review remain manual requirements.

Adding automated documentation checks requires an authorized task. A missing
automatic check does not remove the manual requirement.

Manual review also checks formal-notation fence syntax, accompanying verbal
explanations, source readability without a renderer, and agreement between prose
and notation.
