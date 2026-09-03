# AD-0011: Milestone Worktree Lifecycle

- ID: `AD-0011`
- Status: accepted
- Related: [DN-0027: Effect Ash Program Design](../design/DN-0027-effect-ash-program-design.md), [DN-0028: Effect Ash Milestone Plan](../design/DN-0028-effect-ash-milestone-plan.md)

## Decision

An unintegrated milestone has one persistent integration branch and at most one
checked-out product worktree for its active checkpoint. The integration branch
is the continuation anchor; it does not need a persistent worktree while a
checkpoint branch is active. `main` remains unchanged until the milestone's
separate integration gate approves it.

After a product checkpoint closes and its tip is an ancestor of `main` or the
milestone integration branch, remove its worktree and delete its local feature
branch. Git history through the retaining branch preserves the complete
checkpoint commits. Before removal, require a clean worktree and prove the
ancestry relation against the intended retaining ref.

Planning branches that contributed patch-equivalent work without becoming
ancestors of the retained product history must not be merged merely to make
them reachable. Remove their worktrees and move their refs under
`archive/planning/` instead. The archive ref preserves the exact commits while
making clear that the branch is not a continuation point.

Keep the current active checkpoint worktree and branch until its accepted
proposal, task, specification, evidence, review, verification, and transition
cleanup all close. Then recreate an integration worktree, merge the completed
checkpoint with an explicit merge commit, verify the combined result, and
remove the checkpoint worktree and branch. The next authorized checkpoint
starts from that verified integration tip.

Build output and other ignored caches are disposable. They carry no design,
semantic, task, or evidence authority and need not be retained when a worktree
is removed.

## Context

The Effects Ash work occupied separate planning, product, and integration
worktrees. This preserved isolation during concurrent checkpoints, but closed
and superseded checkouts remained registered afterward. Seven local worktrees
under `.worktree/` consumed about 49 GB, mostly through independent Rust
`target/` directories, and exposed several plausible but incorrect restart
points.

The history already contains the required continuity:

- the relational-interface checkpoint is reachable from `main`;
- the module-`newtype` and resume-required effect-kernel checkpoints are both
  merged into `integration/effect-ash-foundations`;
- the active local-`newtype` checkpoint starts from the integrated product
  baseline `fa26025`; and
- the two earlier planning tips have patch-equivalent successors in the
  product branches but are not themselves ancestors of those successors.

Keeping every checkout adds disk and navigation cost without preserving more
Git history. Merging obsolete planning branches would instead add misleading
ancestry to the product line. Squashing or rebasing the milestone would erase
the checkpoint boundaries used by retained evidence and review.

## Consequences

- `main` continues to describe current Ash; worktree cleanup does not integrate
  Effects Ash semantics.
- `integration/effect-ash-foundations` names the only milestone continuation
  line between completed checkpoints.
- `.worktree/` normally contains only the active product checkpoint.
- Completed feature branch names disappear after their exact commits become
  reachable through a retained branch.
- Superseded planning history remains available under an archive namespace but
  is visibly excluded from active development.
- Recreating an integration worktree adds one explicit step at checkpoint
  closure and avoids keeping a large idle build cache.
- This decision does not authorize a merge into `main`, a push, a milestone
  tag, deletion of an unmerged tip, or cleanup of worktrees outside this
  repository's `.worktree/` directory.

## Verification

For each cleanup operation:

- record the exact source and destination ref names and object IDs;
- require `git status --short` to be empty in every worktree being removed;
- prove each deleted feature tip is an ancestor of its retained branch;
- prove each renamed planning ref resolves to the same object ID before and
  after the rename;
- use `git worktree remove` rather than deleting a registered checkout
  directly;
- confirm `git worktree list --porcelain` contains only the intended active
  checkout under `.worktree/`;
- confirm `main`, the integration branch, and the active checkpoint retain
  their original object IDs; and
- confirm no remote ref, tag, source file, specification file, or product test
  changed.
