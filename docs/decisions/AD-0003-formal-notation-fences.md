# AD-0003: Formal Notation Fences

- ID: `AD-0003`
- Status: accepted
- Related: [AD-0002](AD-0002-documentation-system.md)

## Decision

Ash documentation uses two Markdown fence formats for formal notation:

- `ebnf` for grammar productions;
- `sequent` for Gentzen-style inference rules, including typing and
  operational-semantics rules when they have premises and one conclusion.

Ordinary prose, inline code, or displayed text remains appropriate when a
statement is not a grammar production or inference rule. For example, a
discussion may write `A & B` without placing it in a `sequent` fence.

Every `ebnf` or `sequent` fence must have an accompanying verbal explanation.
The prose and notation must agree and must let a reader understand the point
when diagram rendering is unavailable.

The operational contract will live in `docs/project/notation.md`. The project
documentation index will link it, the writing guide will direct authors to it,
and documentation review will check conformance to it. The Ash contract, not a
particular renderer implementation, defines valid Ash source notation.

### EBNF

Ash uses a bare `ebnf` info string. A production has an identifier, `::=`, an
expression, and a terminating `;`. Expressions may contain nonterminal
references, double-quoted terminals, whitespace-separated sequences, `|`
alternatives, `( ... )` groups, `[ ... ]` optional expressions, `{ ... }`
zero-or-more repetitions, postfix `?`, `*`, and `+`, character classes, and
slash-delimited display regexes. Productions may span lines because `;`, not a
newline, terminates a production.

For example, the first production defines an expression as a term followed by
zero or more additive operations. The second applies the same structure to
multiplication and division:

```ebnf
expression ::= term { ("+" | "-") term } ;
term ::= factor { ("*" | "/") factor } ;
```

Comments and other EBNF dialect features are outside the initial Ash contract.
Renderers may accept `=` for documents outside Ash, but Ash-authored productions
use `::=`.

### Sequents

Ash uses a bare `sequent` info string. A named rule starts with a name and `:=`,
followed by an indented inference. Rule and family names match
`[A-Za-z_][A-Za-z0-9_-]*`. Premises appear above `===>`, and exactly one
conclusion appears below it. Placing `===>` first creates a zero-premise rule.
Separate lines or adjacent bracket groups express multiple premises; bracketed
inferences express nested derivations.

Formula and judgment text is otherwise unrestricted. Authors may use either
Unicode or keyboard-friendly aliases. Ash-authored rules use `===>`, although a
general renderer may also accept `=>`.

For example, the prose says that an application steps when its function
expression steps, while the rule states the state transition precisely:

```sequent
E-App1 :=
  expression, store -> expression', store'
  ===>
  expression argument, store -> expression' argument, store'
```

Renderers normalize these keyboard aliases while accepting their Unicode
results directly:

- judgments and connectives: `<->` to `↔`, `->` to `→`, `<-` to `←`, `|-` to
  `⊢`, `|=` to `⊨`, `/\` to `∧`, `\/` to `∨`, `~` to `¬`, `forall` to `∀`, and
  `exists` to `∃`;
- uppercase Greek: `GAMMA` to `Γ`, `DELTA` to `Δ`, `TAU` to `Τ`, `PI` to `Π`,
  `THETA` to `Θ`, and `SIGMA` to `Σ`;
- lowercase Greek: `alpha` to `α`, `beta` to `β`, `gamma` to `γ`, `delta` to
  `δ`, `epsilon` to `ε`, `theta` to `θ`, `lambda` to `λ`, `mu` to `μ`, `pi` to
  `π`, `tau` to `τ`, `eta` to `η`, `rho` to `ρ`, `sigma` to `σ`, `phi` to `φ`,
  and `omega` to `ω`;
- modal and temporal notation: `box` and `always` to `□`, `diamond` and
  `eventually` to `◇`, `next` to `○`, `until` to `U`, and `release` to `R`;
- linear-logic notation: `-*` and `-o` to `⊸`, `tensor` to `⊗`, `par` to `⅋`,
  `with` to `&`, `plus` to `⊕`, `one` to `1`, `zero` to `0`, `bottom` and `bot`
  to `⊥`, and `top` to `⊤`;
- set notation: `union` to `∪` and `intersect` to `∩`.

Word aliases match complete words. Ordinary `&`, `+`, `-`, `*`, `/`, and `|`
characters remain unchanged unless they form a registered compound alias.

### Rendering and portability

Markdown source is canonical; a diagram is derived presentation. Without a
renderer, a fence remains a readable code block. A renderer replaces a fence
only after successful parsing. On failure, an integration reports a source
location and preserves the source for correction rather than silently choosing
another interpretation.

A renderer port may use any rendering engine, but it must implement the Ash
contract and alias vocabulary. It may accept additional syntax for other
projects. Ash documents remain within the documented subset. The contract does
not require a LaTeX equivalent.

## Context

Ash expects grammar, typing, and operational-semantics material. Plain code
fences preserve source but do not expose the structure of productions or
inference trees in rendered documentation. LaTeX would add another notation and
input method when readable keyboard-oriented forms already exist.

The `railroad` project renders `ebnf` fences as railroad diagrams. Its current
parser accepts most of the required expression syntax but accepts only `=` as a
production operator. The `sequent-md` project renders `sequent` fences as proof
trees and already implements the required alias vocabulary, but its current
identifier grammar rejects hyphenated rule names such as `E-App1`.

Putting the full contract in the writing guide would mix prose guidance with a
notation grammar. Putting it in the documentation policy would mix source
authority rules with detailed syntax. A dedicated notation guide keeps the
contract together while those documents link to it at the points where authors
and reviewers need it.

## Consequences

- Grammar productions and Gentzen-style rules have one portable source format.
- Prose remains required; a rendered graph never carries the explanation alone.
- Authors can use readable Unicode when generating text and aliases when typing
  it directly.
- Formal statements that are not inference rules do not need artificial
  `sequent` structure.
- The railroad parser must accept `::=` as equivalent to `=` while retaining
  `=` for compatibility. Its diagnostics, tests, README, and examples must
  cover both forms. An Ash conformance fixture must cover multiline productions,
  `;`, alternatives, repetition, character classes, and regex literals.
- The sequent parser must accept hyphens after the first character of rule and
  family names. Its grammar, tests, README, and examples must cover the expanded
  names. An Ash conformance fixture must cover axioms, multiple premises, nested
  derivations, a hyphenated name, aliases, and Unicode.
- The sequent renderer needs no alias change for the initial contract.
- The renderer updates belong to their own repositories. The Ash documentation
  work records the conformance gaps but does not modify those repositories.
- New automated Ash documentation checks require separate authorization under
  AD-0002. The initial verification remains manual.

## Verification

- The notation guide defines both fence grammars and the complete alias map.
- Repository guidance links authors and reviewers to the notation guide.
- Every special-fence example has prose that explains it.
- EBNF examples use `::=` and `;`; sequent examples use `:=` and `===>`.
- Examples parse after the listed renderer updates and remain understandable as
  unrendered Markdown.
- Renderer errors expose a source location and retain the source text.
- Documentation review confirms that prose and notation agree and that no
  notation rule defines Ash language semantics by itself.
