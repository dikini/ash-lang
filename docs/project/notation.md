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

Use `family name:` followed by indented named rules to group related rules. A
renderer may lay the rules out side by side when space permits.

Ash-authored rules use `===>`. A general renderer may also accept `=>`.

## Symbols

Unicode symbols and keyboard-friendly aliases are both valid in formula and
judgment text. A renderer normalizes these aliases:

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
