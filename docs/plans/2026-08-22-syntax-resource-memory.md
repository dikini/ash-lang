# Syntax Resource Memory Remediation Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Bound wide-source front-end memory before CST materialization while preserving the accepted 100,000-field coverage regression and releasing obsolete stage ownership.

**Architecture:** A private cumulative budget charges retained lexer tokens, lexical diagnostics, and parser events before allocation. Lexer or parser exhaustion returns one structured resource-bearing syntax result that cannot project; successful orchestration explicitly drops predecessor representations at stage boundaries.

**Tech Stack:** Rust 2024, retained lexer/event parser/CST pipeline, typed stage failures, Cargo integration tests, GNU `time` measurement

---

### Task 1: Fix the public resource contract with failing tests

**Files:**
- Modify: `tests/lexer.rs`
- Modify: `tests/parser.rs`
- Modify: `tests/data_and_adts.rs`

**Step 1: Write the lexer-width rejection test**

Import `SYNTAX_WORK_LIMIT`. Build a comma-only source with more retained tokens
than the limit, call `lex`, and require a `SyntaxWork` resource fact rather than
unbounded token retention.

**Step 2: Write the cumulative parser-event rejection test**

Build a 110,000-field tuple match. Require `ResourceFailure::SyntaxWork`, an
unprojectable resource tree, no fabricated parser diagnostic, and bounded event
retention.

**Step 3: Preserve the coverage boundary**

Keep `a_wide_tuple_case_group_charges_type_and_specialization_cells` at 100,000
fields and its exact `CoverageResourceExhausted` assertion. This proves the new
syntax budget does not hide the usefulness boundary.

**Step 4: Add reason and rendering assertions**

Construct the public syntax failure through the source pipeline and require
`parse.resource`, `internal.resource.syntax-work`, and non-source-rejection
classification.

**Step 5: Run the focused tests and observe RED**

Run:

```text
cargo test --locked --test lexer syntax_work
cargo test --locked --test parser syntax_work
cargo test --locked --test data_and_adts a_wide_tuple_case_group_charges_type_and_specialization_cells -- --exact
```

Expected: the new tests fail to compile because the limit and resource variant
do not exist; the retained coverage test still passes.

### Task 2: Implement cumulative syntax resource accounting

**Files:**
- Create: `src/syntax_resource.rs`
- Modify: `src/lib.rs`
- Modify: `src/lexer/mod.rs`
- Modify: `src/parser/mod.rs`
- Modify: `src/parser/cst.rs`
- Modify: `src/parser/project.rs`
- Modify: `src/render.rs`
- Modify: `src/driver.rs`

**Step 1: Add the shared budget**

Define `SYNTAX_WORK_LIMIT` as 1,500,000 units. Implement a private
`SyntaxBudget` whose `charge` method subtracts before allocation and returns
`ResourceFailure::SyntaxWork { limit }` transactionally. Unit-test the exact
boundary and next charge.

**Step 2: Charge lexer retention**

Charge every token and lexical diagnostic before pushing it. Carry the budget
and optional resource failure in `Lexed`. Stop scanning at exhaustion without
manufacturing EOF or diagnostics.

**Step 3: Charge parser events**

Move all event push and insertion sites through one charging helper. On
exhaustion, keep parser control progressing without retaining more events and
return a resource-bearing concrete result without constructing a partial root.

**Step 4: Preserve structural-depth behavior**

Keep the existing balanced, token-complete structural-depth path when syntax
work remains. If both limits are reached, syntax work stops further allocation
and the first structured resource fact remains deterministic.

**Step 5: Wire public failure behavior**

Re-export `ResourceFailure` and `SYNTAX_WORK_LIMIT` from `parser`, reject every
resource tree at projection, render `SyntaxWork` as
`internal.resource.syntax-work`, and make a resource fact take precedence in
`PipelineFailure::reason_code`.

**Step 6: Run focused GREEN tests**

Run:

```text
cargo test --locked --lib syntax_resource
cargo test --locked --test lexer syntax_work
cargo test --locked --test parser syntax_work
cargo test --locked --test data_and_adts a_wide_tuple_case_group_charges_type_and_specialization_cells -- --exact
cargo test --locked --test core_validation oversized_unchecked_match_maps_coverage_exhaustion_to_resource -- --exact
```

Expected: all selected tests pass with no warnings.

### Task 3: Release obsolete front-end representations

**Files:**
- Modify: `src/driver.rs`
- Test: `tests/corpus.rs`
- Test: `tests/data_and_adts.rs`

**Step 1: Release the concrete tree**

After successful projection, explicitly drop the concrete tree before entering
resolution.

**Step 2: Release the surface tree**

After successful resolution, explicitly drop the surface program before
constructing the elaborator.

**Step 3: Verify behavioral preservation**

Run:

```text
cargo test --locked --test corpus
cargo test --locked --test data_and_adts
```

Expected: all source outcomes, provenance, and coverage classifications remain
unchanged except the new over-budget syntax case.

### Task 4: Measure the corrected boundary and retain evidence

**Files:**
- Modify: `docs/design/mini-ash/data-and-patterns/evidence.md`
- Modify: `docs/tasks/TASK-0009-implement-monomorphic-data-and-patterns.md`

**Step 1: Measure the admitted case**

Run the 100,000-field test under `/usr/bin/time -v` and record elapsed time and
maximum RSS.

**Step 2: Measure the rejected case**

Temporarily raise the new syntax-work rejection fixture to 1,000,001 fields,
run it under `/usr/bin/time -v`, confirm syntax-work exhaustion, and restore
the retained fixture before continuing.

**Step 3: Update retained evidence**

Record the allocation attribution, before/after measurements, selected budget,
structured failure, changed composition points, and direct Core coverage test.
Update TASK-0009 progress without turning measurements into language truth.

**Step 4: Commit the remediation**

Run focused formatting and tests, then commit without signing:

```text
git add src tests docs
git commit --no-gpg-sign -m "fix(parser): bound wide syntax memory"
```

### Task 5: Complete verification and review handoff

**Files:**
- Verify all changed files

**Step 1: Run required gates**

Run:

```text
cargo fmt --all --check
cargo check --locked --all-targets
cargo test --locked --all-targets
cargo xtask verify
```

Expected: every command exits zero with no warnings or failed tests.

**Step 2: Verify documentation**

Run the repository Markdown lint command for changed Markdown. Check changed
relative links and confirm the design, plan, task, and evidence preserve their
non-normative authority.

**Step 3: Audit the diff**

Run `git diff --check main...HEAD`, inspect every resource match exhaustively,
confirm no unsafe code or allocator dependency was retained, and confirm the
worktree is clean.

**Step 4: Stop for review**

Report commits, red-green evidence, measurements, verification results, and
remaining exclusions. Do not integrate or remove temporary TASK-0009 artifacts
without explicit user confirmation.
