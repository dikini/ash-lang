# Effect Ash Closure Execution Plan

**Goal:** Close the selected milestone on verified main without adding features.

**Owner:** [TASK-0031](TASK-0031-close-effect-ash-milestone.md).

**Approach:** Reuse retained slice evidence, inspect cross-slice boundaries,
repair only demonstrated gaps, and preserve separate integration/publication
approval. The existing isolated milestone checkout holds audit documentation;
main stays untouched until its integration gate is approved.

## 1. Reconstruct and audit

- Baseline: `035b456`; fresh library/CLI tests passed.
- High-reasoning read-only semantic review: combined source, diagnostics,
  linked/Core tampering, transforms, runtime, resource and migration coverage.
- High-reasoning read-only architecture/resource review: named proof,
  existential, suspension, concurrency, replay and dynamic-loading pressures;
  Pure locality; concrete simplification opportunities and residual risks.
- Parent owns documentation and verification. Serialize any demonstrated code
  fix, require its failing regression first, and return semantic gaps to the
  user rather than deciding them in this task.

## 2. Retain closure evidence and documentation

Create `docs/design/effect-ash/milestone-closure-evidence.md` with obligation,
test/invariant, review and residual-risk mappings. Correct the missing Cleanup
inventory in `spec/elaboration.md` from the existing Core/validation contract.
Update stale milestone summaries in DN-0028 and `docs/design/README.md` without
rewriting accurately labeled historical checkpoint evidence.

Obtain independent documentation review. Run `cargo xtask verify`, Markdown
lint with explicit unchanged-baseline findings, relative-link/anchor checks and
`git diff --check`. No universal ARM64 execution claim follows from compilation.

## 3. Main integration gate

The user requested a signed local main merge. Preserve all six existing
main documentation paths, including untracked TASK-0024, using the approved
temporary shelving/restoration procedure. Preserve main's committed README.
Use an explicit signed merge; never reset, overwrite or commit unrelated work.
Verify the merged main code and restored user changes. Tag and push only if
separately authorized.

## 4. Complete the milestone

Only after integrated verification, record 100/100 relative planning weights
closed, exact retained commits and residual limitations. Remove this temporary
plan and TASK-0031 with index updates, preserving them in Git history. Check
links and status-only changes, commit unsigned, and leave closure-owned state
clean while preserving the user's prior dirty state. Remove only clean,
retained milestone worktrees allowed by AD-0011.

Update present-state passages in DN-0026, DN-0027, DN-0028 and the trajectory;
replace DN-0028's task link with retained closure evidence. In the nine slice
reports, qualify opening branch-only claims as historical and link current
specification/closure. Retain dated counts, hashes, old planning weights and
historical no-main-merge records. Correct implemented cleanup/hooks/native
provider gaps, but preserve general FFI, files, suspension and other exclusions.
