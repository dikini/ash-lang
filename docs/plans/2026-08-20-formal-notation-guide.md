# Formal Notation Guide Implementation Plan

<!-- markdownlint-disable MD001 MD036 -->

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Publish Ash's portable Markdown contracts for grammar productions and
Gentzen-style inference rules.

**Architecture:** AD-0003 owns the accepted non-language decision. One temporary
task publishes a project notation guide, routes authors and reviewers to it,
records manual verification and known external renderer gaps, and then leaves
the current tree with its execution plan.

**Tech Stack:** Markdown, Markdownlint, Git, and Node.js checks against the two
external JavaScript renderers.

---

Use `@superpowers:verification-before-completion` before every success claim,
commit, and task completion.

### Task 1: Authorize the documentation work

**Files:**

- Create: `docs/tasks/TASK-0004-publish-formal-notation-guide.md`
- Create: `docs/plans/2026-08-20-formal-notation-guide.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`

**Step 1: Confirm that TASK-0004 is unused**

Run:

```bash
! git log --all --name-only --pretty=format: | rg 'TASK-0004'
```

Expected: exit 0 with no matches.

**Step 2: Create the active task and implementation plan**

Create TASK-0004 with AD-0003 as its authority. Scope it to the project notation
guide and contributor routing. Exclude renderer repository changes, language
semantics, and new verification automation.

Save this implementation plan at
`docs/plans/2026-08-20-formal-notation-guide.md` and link it from TASK-0004.

**Step 3: Mark TASK-0004 active**

Replace `No implementation task is active.` in `docs/tasks/README.md` with:

````markdown
- [TASK-0004: Publish the Formal Notation Guide](TASK-0004-publish-formal-notation-guide.md)
````

Replace the inactive-task statement in `docs/trajectory.md` with:

```markdown
TASK-0004 is publishing the accepted formal-notation contract. Other work still
needs enough evidence to authorize implementation.
```

Add this row to the trajectory table:

```markdown
| [Formal notation fences](decisions/AD-0003-formal-notation-fences.md) | implementation | AD-0003 | Complete [TASK-0004](tasks/TASK-0004-publish-formal-notation-guide.md): publish and route the operational notation guide. |
```

**Step 4: Verify and commit task activation**

Run:

```bash
markdownlint --disable MD013 -- \
  docs/plans/2026-08-20-formal-notation-guide.md \
  docs/tasks/README.md \
  docs/tasks/TASK-0004-publish-formal-notation-guide.md \
  docs/trajectory.md
test -f docs/decisions/AD-0003-formal-notation-fences.md
git diff --check
```

Expected: all commands exit 0.

Commit:

```bash
git add docs/plans docs/tasks docs/trajectory.md
git commit -m "docs: authorize formal notation guide"
```

### Task 2: Publish the notation contract

**Files:**

- Create: `docs/project/notation.md`

**Step 1: Demonstrate that the operational guide is absent**

Run:

```bash
test ! -e docs/project/notation.md
```

Expected: exit 0 because the guide does not exist.

**Step 2: Create the guide**

Create `docs/project/notation.md` with this structure and content:

````markdown
# Formal notation

Ash Markdown uses registered code fences for grammar productions and
Gentzen-style inference rules. These formats control source notation and
rendering; they do not define Ash language semantics.

Every formal-notation fence needs a verbal explanation. State what the notation
defines or demonstrates and explain any metavariables or side conditions needed
to read it. Keep the prose and notation consistent. The explanation must remain
useful when a Markdown renderer displays the fence as an ordinary code block.

Use ordinary prose, inline code, or displayed text when a statement is not a
grammar production or inference rule. For example, a discussion can write
`A & B` without constructing an inference rule.

## Grammar productions

Use a bare `ebnf` fence for grammar productions. Each production has an
identifier, `::=`, an expression, and a terminating `;`. A production may span
lines because `;`, not a newline, marks its end.

This grammar says that an expression contains a term followed by zero or more
additive operations, while a term applies the same structure to multiplication
and division:

```ebnf
expression ::= term { ("+" | "-") term } ;
term ::= factor { ("*" | "/") factor } ;
```

An expression may contain:

- identifiers as nonterminal references;
- double-quoted terminals;
- whitespace-separated sequences;
- alternatives separated by `|`;
- groups enclosed by `( ... )`;
- optional expressions enclosed by `[ ... ]`;
- zero-or-more repetitions enclosed by `{ ... }`;
- postfix `?`, `*`, and `+` operators;
- character classes such as `[a-zA-Z_]`;
- slash-delimited display regexes such as `/\d+/`.

Regex contents are labels for a lexical form. A renderer preserves the contents
but does not execute them. Comments and other EBNF dialect features are outside
the Ash contract. A general renderer may accept `=` for compatibility, but Ash
grammar productions use `::=`.

## Inference rules

Use a bare `sequent` fence when a rule is naturally a Gentzen-style inference
with zero or more premises and one conclusion. This includes typing and
operational-semantics rules with that structure.

A named rule starts with a name and `:=`. Indent its body, place premises above
`===>`, and place exactly one conclusion below it. A rule with `===>` first has
no premises. Rule and family names match `[A-Za-z_][A-Za-z0-9_-]*`.

This rule says that an application steps when its function expression steps:

```sequent
E-App1 :=
  expression, store -> expression', store'
  ===>
  expression argument, store -> expression' argument, store'
```

Write independent premises on separate lines. Place adjacent bracket groups on
one line when sibling premises should appear side by side. A bracket group may
contain a complete anonymous inference to form a nested derivation. Formula and
judgment text is otherwise unrestricted.

Ash-authored rules use `===>`. A general renderer may also accept `=>`.

## Symbols

Unicode symbols and keyboard-friendly aliases are both valid in formula and
judgment text. A renderer normalizes these aliases:

| Source | Rendered |
| --- | --- |
| `<->`, `->`, `<-` | `↔`, `→`, `←` |
| `|-`, `|=` | `⊢`, `⊨` |
| `/\`, `\/`, `~` | `∧`, `∨`, `¬` |
| `forall`, `exists` | `∀`, `∃` |
| `GAMMA`, `DELTA`, `TAU`, `PI`, `THETA`, `SIGMA` | `Γ`, `Δ`, `Τ`, `Π`, `Θ`, `Σ` |
| `alpha`, `beta`, `gamma`, `delta`, `epsilon` | `α`, `β`, `γ`, `δ`, `ε` |
| `theta`, `lambda`, `mu`, `pi`, `tau` | `θ`, `λ`, `μ`, `π`, `τ` |
| `eta`, `rho`, `sigma`, `phi`, `omega` | `η`, `ρ`, `σ`, `φ`, `ω` |
| `box`, `always`, `diamond`, `eventually` | `□`, `□`, `◇`, `◇` |
| `next`, `until`, `release` | `○`, `U`, `R` |
| `-*`, `-o`, `tensor`, `par` | `⊸`, `⊸`, `⊗`, `⅋` |
| `with`, `plus` | `&`, `⊕` |
| `one`, `zero` | `1`, `0` |
| `bottom`, `bot`, `top` | `⊥`, `⊥`, `⊤` |
| `union`, `intersect` | `∪`, `∩` |

Word aliases match complete words. Ordinary `&`, `+`, `-`, `*`, `/`, and `|`
remain unchanged unless they form a registered compound alias.

## Rendering and ports

Markdown source is canonical; diagrams are derived presentation. Without a
renderer, each fence remains a readable code block. A renderer replaces a fence
only after successful parsing. On failure, it reports a source location and
preserves the source for correction instead of silently choosing another
interpretation.

A renderer port may use any rendering engine, but it must implement these source
formats and symbol aliases. It may accept additional syntax for other projects.
Ash documents stay within the contract above. No LaTeX equivalent is required.

The accepted decision records the current
[renderer conformance gaps](../decisions/AD-0003-formal-notation-fences.md#consequences).
````

**Step 3: Check the guide against AD-0003**

Run:

```bash
rg -n '^## (Grammar productions|Inference rules|Symbols|Rendering and ports)$' docs/project/notation.md
rg -n '::=|;|===>|E-App1|GAMMA|omega|renderer conformance gaps' docs/project/notation.md
test -f docs/decisions/AD-0003-formal-notation-fences.md
markdownlint --disable MD013 -- docs/project/notation.md
git diff --check
```

Expected: the four headings and required contract terms are present; the link
target exists; lint and whitespace checks exit 0.

**Step 4: Commit the notation guide**

```bash
git add docs/project/notation.md
git commit -m "docs: publish formal notation contract"
```

### Task 3: Route authors and reviewers to the contract

**Files:**

- Modify: `docs/project/README.md`
- Modify: `docs/project/writing.md`
- Modify: `docs/project/documentation.md`

**Step 1: Demonstrate that the routes are absent**

Run:

```bash
! rg -q 'notation.md' docs/project/README.md
! rg -q 'Formal notation' docs/project/writing.md
! rg -q 'formal-notation fences' docs/project/documentation.md
```

Expected: every command exits 0 because the routes are absent.

**Step 2: Add the project-index route**

Add this item after the documentation policy in `docs/project/README.md`:

```markdown
- [Formal notation](notation.md)
```

**Step 3: Add author guidance**

Append this section to `docs/project/writing.md`:

```markdown
## Formal notation

Follow the [formal-notation guide](notation.md) for grammar productions and
Gentzen-style inference rules. Use `ebnf` fences for grammar productions and
`sequent` fences for inference rules with premises and one conclusion. Explain
every formal-notation fence in prose and keep the explanation consistent with
the notation. Use ordinary prose or inline notation when no production or
inference structure is needed.
```

**Step 4: Add the documentation-review route**

Add this paragraph after the opening classification paragraphs in
`docs/project/documentation.md`:

```markdown
Grammar productions and Gentzen-style inference rules follow the
[formal-notation guide](notation.md). The notation controls their Markdown
representation; it does not change the authority of the containing document.
```

Append this sentence to `Current verification boundary`:

```markdown
Manual review also checks formal-notation fence syntax, accompanying verbal
explanations, source readability without a renderer, and agreement between prose
and notation.
```

**Step 5: Verify the routes**

Run:

```bash
rg -n '\[Formal notation\]\(notation.md\)' docs/project/README.md
rg -n '\[formal-notation guide\]\(notation.md\)' docs/project/writing.md docs/project/documentation.md
rg -n 'Manual review also checks formal-notation fence syntax' docs/project/documentation.md
test -f docs/project/notation.md
markdownlint --disable MD013 -- \
  docs/project/README.md \
  docs/project/documentation.md \
  docs/project/notation.md \
  docs/project/writing.md
git diff --check
```

Expected: each route appears once in its intended file; the target exists; lint
and whitespace checks exit 0.

**Step 6: Commit the routes**

```bash
git add docs/project/README.md docs/project/documentation.md docs/project/writing.md
git commit -m "docs: route formal notation guidance"
```

### Task 4: Verify the contract and record evidence

**Files:**

- Modify: `docs/tasks/TASK-0004-publish-formal-notation-guide.md`

**Step 1: Verify the supported portions of the EBNF example**

Run:

```bash
node --input-type=module -e "import {compileEbnf} from '/home/dikini/Projects/railroad/src/ebnf.js'; compileEbnf('expression = term { (\"+\" | \"-\") term } ;')"
```

Expected: exit 0. This shows that the current renderer supports the expression
syntax when its known assignment-operator gap is removed.

**Step 2: Confirm the railroad conformance gap**

Run:

```bash
! node --input-type=module -e "import {compileEbnf} from '/home/dikini/Projects/railroad/src/ebnf.js'; compileEbnf('expression ::= term ;')" 2>/dev/null
```

Expected: exit 0 for the negated command because the current parser rejects
`::=`. Record this as an expected external conformance gap, not an Ash failure.

**Step 3: Verify the supported portions of the sequent example**

Run:

```bash
node --input-type=module -e "import {parse} from '/home/dikini/Projects/sequent-md/packages/core/src/index.js'; const result = parse('E_App1 :=\n  expression, store -> expression\x27, store\x27\n  ===>\n  expression argument, store -> expression\x27 argument, store\x27'); if (result.diagnostics.length) process.exit(1)"
```

Expected: exit 0. This shows that the current renderer supports the inference
syntax when its known hyphenated-name gap is removed.

**Step 4: Confirm the sequent conformance gap**

Run:

```bash
node --input-type=module -e "import {parse} from '/home/dikini/Projects/sequent-md/packages/core/src/index.js'; const result = parse('E-App1 :=\n  ===>\n  A'); if (result.diagnostics.length === 0) process.exit(1)"
```

Expected: exit 0 because the current parser reports diagnostics for the
hyphenated name. Record this as an expected external conformance gap.

**Step 5: Run repository verification**

Run:

```bash
cargo xtask verify
markdownlint --disable MD013 -- \
  docs/decisions/AD-0003-formal-notation-fences.md \
  docs/plans/2026-08-20-formal-notation-guide.md \
  docs/project/README.md \
  docs/project/documentation.md \
  docs/project/notation.md \
  docs/project/writing.md \
  docs/tasks/README.md \
  docs/tasks/TASK-0004-publish-formal-notation-guide.md \
  docs/trajectory.md
git diff --check
```

Expected: all commands exit 0.

**Step 6: Inspect authority and prose boundaries**

Confirm manually:

- the notation guide defines representation, not Ash language semantics;
- both special-fence examples have verbal explanations;
- every alias in AD-0003 appears in the guide;
- the guide identifies source as canonical and preserves readable fallback;
- the renderer gaps remain labeled as external implementation work.

Expected: every item holds.

**Step 7: Record progress and discoveries**

Replace `Progress` in TASK-0004 with:

```markdown
The operational guide now defines both fence formats and the complete alias
vocabulary. Project, writing, and documentation guidance route authors and
reviewers to it. Manual and repository checks pass.
```

Replace `Discoveries` with:

```markdown
- The railroad renderer supports the accepted expression forms but still needs
  `::=` support.
- The sequent renderer supports the accepted inference forms and aliases but
  still needs hyphenated rule and family names.
- Neither external gap prevents unrendered Markdown from remaining readable.
```

Leave `Deviations` as `None.`

**Step 8: Verify and commit the evidence record**

Run:

```bash
markdownlint --disable MD013 -- docs/tasks/TASK-0004-publish-formal-notation-guide.md
git diff --check
```

Expected: both commands exit 0.

Commit:

```bash
git add docs/tasks/TASK-0004-publish-formal-notation-guide.md
git commit -m "docs: record formal notation verification"
```

### Task 5: Complete TASK-0004

**Files:**

- Remove: `docs/tasks/TASK-0004-publish-formal-notation-guide.md`
- Remove: `docs/plans/2026-08-20-formal-notation-guide.md`
- Modify: `docs/tasks/README.md`
- Modify: `docs/trajectory.md`

**Step 1: Remove completed planning records**

Remove TASK-0004 and its execution plan. Git history retains the authorization,
execution steps, and verification evidence.

**Step 2: Restore current-state indexes**

Replace the active task in `docs/tasks/README.md` with:

```markdown
No implementation task is active.
```

Replace the active-task statement in `docs/trajectory.md` with:

```markdown
No implementation task is active. Other work still needs enough evidence to
authorize implementation.
```

Remove the formal-notation row from the trajectory table.

**Step 3: Verify the final state**

Run:

```bash
cargo xtask verify
markdownlint --disable MD013 -- \
  docs/decisions/AD-0003-formal-notation-fences.md \
  docs/project/README.md \
  docs/project/documentation.md \
  docs/project/notation.md \
  docs/project/writing.md \
  docs/tasks/README.md \
  docs/trajectory.md
! rg -n 'TASK-0004|2026-08-20-formal-notation-guide' docs AGENTS.md
test -f docs/project/notation.md
git diff --check
git status --short
```

Expected: all checks before `git status` exit 0; no current-tree reference to the
completed task or plan remains; status lists only the intended cleanup changes.

**Step 4: Commit completion**

```bash
git add docs/tasks docs/plans docs/trajectory.md
git commit -m "docs: complete formal notation guide"
```
