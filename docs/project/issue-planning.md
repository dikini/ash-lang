# Working rules for planning issues

These rules guide the preparation of bounded implementation issues. They do
not authorize implementation or replace the governing proposal, task or
delivery workflow. Plan the work before creating issues.

## Difficulty points

- Give each independently assigned work unit one whole-number difficulty
  estimate from **1 to 5**. Five is the maximum; split anything estimated above
  five before assigning it. Do not use ranges or estimates in days.
- Prefer smaller, well-defined units. Aim for most units to be below five,
  preferably one to three where a useful boundary exists. Do not split a
  cohesive change merely to manufacture small numbers.
- Estimate relative difficulty using the known work: unfamiliarity, number
  of crossed interfaces, complexity of implementation, failure cases and the
  verification needed. Points are a prediction, not a measure of time, lines
  changed, number of tests or individual productivity.
- Include the work needed for each unit's checks and review. Plan shared
  integration, independent QA, review and final gates as bounded work too;
  do not hide the remaining delivery chain in one implementation issue.
- Preserve each original prediction. After delivery, record the observed
  difficulty separately and explain material differences. If scope changes,
  record the added, removed or split work and estimate the remaining scope
  without rewriting the original prediction.
- Assign each point to one unit and one functionality area. The sum of the
  detailed units must equal the functionality total for the same scope; do
  not count shared evidence twice. Preserve earlier totals as historical
  predictions when making a revised plan.

## Slice 1 calibration

Use retained expression-macro delivery evidence as a comparison, not as an
automatic conversion from elapsed time or effort credits to difficulty points.
The completed task and its original ledger are preserved in Git at
`d0b1bf68:docs/tasks/TASK-0067-expression-macros.md`. For example:

- A captured constructor-pattern repair crossed parsing and ordinary name
  resolution, and required positive and negative cases. Use it to judge a
  bounded cross-interface task rather than estimating from its line count.
- Nested syntax transfer and unwrapping each exposed stack failures. A task
  touching that path needs a bounded-depth and failure case; a passing shallow
  example alone is insufficient evidence.
- The removal of per-reference grants showed that retaining an existing
  resolver boundary can be simpler than adding another validation system.
  Consider existing mechanisms before assigning new machinery.
- The final mixed-syntax identity case needed a real Ash transformer and the
  public driver. Plan the producer, real consumer and the connected check;
  isolated helpers do not establish the complete path.

Compare proposed tasks with the scope and evidence of these observations.
They are calibration anchors, not predetermined point assignments. Record the
reason for a score so later estimates can be compared with actual outcomes.

## Boundaries and acceptance

Each planned unit must identify:

1. A concrete outcome and the exact deliverables, including affected
   producer/consumer interfaces where relevant.
2. A **Do not do** section listing specific prohibited changes and tempting
   adjacent work. These are hard boundaries, not suggestions.
3. Predefined positive and negative acceptance cases with expected outcomes
   and relevant fixtures. Distinguish focused checks from the connected
   production-path gate when a later consumer is needed.
4. The governing artifact, prerequisites, blocking issues and ownership. A
   task or issue organizes work; it does not define Ash semantics.

If a boundary appears to prevent the assigned outcome, stop the affected work,
record the concrete reason and return the issue to its design owner. Continue
other authorized work that does not depend on that decision. A reviewer checks
the boundaries as well as the acceptance evidence.

## Dependencies and parallel work

- Draw the dependency graph from actual producer/consumer requirements, not
  from issue numbering or an assumption that one role must finish an entire
  phase before another starts. Name the interface, prerequisite and check for
  every edge.
- Identify independent units that can proceed in parallel. Define ownership
  of shared files, checkouts, build caches and heavy tools so parallel work
  does not overwrite changes or invalidate a verification input.
- An agreed producer interface and focused evidence can let a consumer begin;
  it does not make the producer's connected acceptance gate pass early.
- Allow design, planning, development, QA and review to overlap on different
  units. On each unit, QA and review assess a specified candidate, and
  acceptance requires its stated evidence.
- Define one integration owner and a production-path acceptance check that
  connects the independently developed pieces. Preserve partial status until
  that check and the relevant review are complete.
