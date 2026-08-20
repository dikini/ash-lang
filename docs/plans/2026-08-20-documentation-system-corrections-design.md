# Documentation System Corrections Design

## Purpose

Correct three gaps found after implementing AD-0002 without reopening the
decision or expanding the documentation system.

## Changes

The Ash language and tool section of `docs/project/documentation.md` will require
documentation to change or leave the current tree with the behavior it describes.
The Rust crate section will apply the same rule to APIs, errors, invariants, and
safety obligations. Git remains the archive.

The first documentation-policy reference in `AGENTS.md` will link directly to
`docs/project/documentation.md` so an agent can reach the governing policy from
its starting document.

The introduction in `docs/project/README.md` will describe the directory as the
home for documentation, dependency, specification, writing, and artifact
policies. This replaces its narrower description of artifact relationships.

AD-0002, Rust code, directory structure, and verification automation will not
change.

## Verification

The correction will run:

- `cargo xtask verify`;
- Markdownlint on every changed and temporary task document;
- relative-link inspection;
- `git diff --check`.

An active task and execution plan will record the work and its evidence. Both
plans and the completed task will leave the current tree after verification.
