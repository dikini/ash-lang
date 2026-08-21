# First-stratum parser-architecture comparison

> This comparison is informative evidence governed by
> [DN-0016](../../../DN-0016-first-mini-ash-corpus.md). It does not accept a
> parser architecture or define current Ash syntax.

## Question

Which parser organization keeps grammar growth local, represents precedence
and ambiguity explicitly, preserves source structure, and produces the required
`P-001` through `P-003` diagnostics without coupling the grammar to one parser
framework?

## Scope and method

The written comparison applies four candidate organizations to the provisional
[grammar](../grammar.md), every valid source presentation, and the three parser
failures. It traces concrete dispatch, precedence, span, and recovery behavior.
No code probe is required at this stage because the distinguishing behavior
comes from ownership of tokens, events, recovery, and grammar decisions. A
prototype would otherwise need to choose the unresolved layout and multiline
equation rules, turning those choices into accidental evidence.

The candidates are:

1. grammar-shaped recursive descent that constructs a spanned surface AST
   directly;
2. event-producing recursive descent with a token-complete concrete syntax tree and
   a separate surface-AST projection;
3. parser combinators that construct a spanned tree and carry structured
   failure and recovery state;
4. a parser generated from a separate grammar, with custom tree and recovery
   actions.

The comparison treats expression precedence as a subproblem. Each candidate
must either use precedence climbing, Pratt parsing, layered grammar productions,
or generated precedence declarations without changing the independent EBNF.

## Shared boundaries

Every viable candidate needs the same boundaries:

```text
source text
  → tokens with source spans and layout boundaries
  → error-bearing surface representation
  → validated surface AST without recovery nodes
  → resolution
```

Lexing owns token boundaries, reserved words, integers, delimiters, operators,
and the provisional `line_end` token. Parsing owns grammar, precedence,
associativity, grouping, definition boundaries, missing forms, and recovery.
Neither stage decides name agreement, function grouping from types, or static
semantics.

The error-bearing representation retains all consumed tokens, grouping
delimiters, missing-token markers, error nodes, and diagnostics. Projection to
the resolver's input must fail while any recovery node remains. This keeps a
fabricated parser placeholder from becoming a resolved or typed expression.

## Candidate organizations

### Direct spanned-AST recursive descent

This candidate gives each grammar area a parser function or module. A program
parser coordinates global definitions and the required result. Dedicated
parsers own blocks, definitions, patterns, and types. An expression parser owns
application and infix precedence.

The control flow is direct and the resulting tree can match resolver needs.
Checkpointing or lookahead can distinguish a complete global definition from
the final expression. Right-recursive type parsing naturally makes `->`
right-associative, while an expression precedence loop makes application
left-associative and higher precedence than multiplication and addition.

The cost appears at recovery and tooling boundaries. A surface AST must add
special missing and error variants or maintain a separate recovery structure.
If it discards punctuation and layout, formatter and editor work must recover
them from source. If it retains every token and delimiter, it becomes a
concrete syntax tree under another name. Direct AST construction is therefore
the smallest batch-parser baseline, but its apparent single representation
does not survive the corpus's recovery-node and source-coverage requirements.

### Event-producing recursive descent

This candidate uses the same grammar-shaped control but emits events rather
than constructing semantic nodes during recursion:

```text
StartNode(kind)
Token(token_id)
Missing(expected, origin)
Error(structured_reason)
FinishNode
```

The event stream builds a token-complete concrete syntax tree. A separate projection
constructs the spanned surface AST only after checking that no missing or error
nodes remain. Parser functions can start a node before enough input is known,
then assign or wrap its final kind after precedence and lookahead decisions.

This organization separates three concerns:

- recursive descent decides declaration, block, pattern, and type structure;
- a Pratt or precedence-climbing layer decides expression grouping;
- tree events preserve tokens, recovery, and source coverage.

Feature components can contribute one or more entry points at an explicit
dialect boundary:

```text
global-definition forms
expression prefix forms
expression infix operators and binding powers
pattern forms
type-atom forms
```

The selected dialect still has one closed dispatch point. Adding a match
expression changes the prefix-form selection and its feature parser, not the
binding, type, or global-definition parsers. Adding an operator changes its
token and infix table entry, not the nested-construct parsers. This is the
parser analogue of a closed Core dialect assembled from feature families.

The additional concrete tree and AST projection cost memory and conversion
code. The corpus already requires delimiter spans, presentation structure, and
recovery nodes, so the second representation establishes facts used by
diagnostics and likely tooling rather than serving as an unmotivated stage.

### Parser combinators

Combinators can mirror grammar productions and make local alternatives easy to
compose. A suitable result type must distinguish at least:

```text
Success(value, next_position)
Recover(value_with_errors, next_position)
Failure(expected_set, position, committed)
```

Commitment matters. After consuming `fn`, an opening block brace, or the left
side of `+`, unrestricted backtracking would replace a specific error with an
unrelated alternative's expectation. Recovery also needs delimiter-aware
synchronization and access to opening-token spans.

A small custom combinator layer could provide those operations. Once it adds
Pratt parsing, committed alternatives, an event sink, structured reasons,
missing nodes, and synchronization sets, the architectural result approaches
the event-producing recursive-descent candidate with combinator syntax around
its functions. The comparison therefore does not reject combinators; it finds
that generic sequencing and choice do not answer the important corpus
questions. A future code probe should compare concrete combinator ergonomics
only after the required event and recovery contracts are fixed.

### Generated parser

A generated candidate can keep productions in a dedicated grammar input and
derive exhaustive parsing tables. It can expose conflicts mechanically and may
make broad grammar review concise.

The Ash EBNF must remain independent of generator directives, semantic actions,
precedence annotations, and recovery productions. The generated candidate
would therefore maintain both the specification grammar and an implementation
grammar. It must also construct the same token-complete or equivalently covered
surface representation and implement the same contextual diagnostics.

The first corpus is too small and its layout boundary too provisional to show
that generated conflict reports or tables repay this second grammar and custom
recovery layer. This candidate remains a later baseline when grammar size or
ambiguity produces evidence that handwritten dispatch no longer stays local.

## Precedence and ambiguity

The event-producing recursive-descent candidate can use a data-defined infix
table while keeping construct-specific parse code outside the table:

| Form | Relative binding | Associativity |
| --- | --- | --- |
| Juxtaposed application | Highest expression operator | Left |
| `*` | Above `+` | Left |
| `+` | Above `==` | Left |
| `==` | Lowest named level | Non-associative |

Application is detected by the start of a primary expression rather than an
operator token. A repeated `==` at the same expression level produces a
structured non-associativity failure instead of silently choosing a tree.
Parentheses restart expression parsing at the lowest binding power and retain
both delimiter spans in the concrete tree.

Function type parsing remains separate. Parsing the codomain recursively after
one `->` produces the right-associated type structure. Neither expression
binding powers nor parser associativity decide whether an equation head is
curried or an operational parameter list has a product domain; typing and
elaboration own that distinction.

## Definition boundaries

The current top-level starts are distinguishable without semantic feedback:

- an equational global begins with `identifier :`;
- an inline operational global begins with `fn identifier (`;
- an anonymous function expression begins with `fn (`;
- any other expression start begins the required program result.

An equation group continues only while the next logical line has an equation
head and `=` at its current boundary. The interface-name agreement remains a
resolution check. The parser records each spelling and span rather than making
the grammar context-sensitive.

This lookahead depends on the provisional `line_end`. The exact treatment of a
multiline equation right-hand side remains unresolved and must be settled in a
semantic proposal before a retained parser relies on it.

## Recovery traces

### `P-001`: required result at end of file

After completing the last global, the program parser reaches end of input while
still requiring one expression. It emits `parse.expected-result` at the empty
end-of-file span and finishes an error-bearing program node. It does not attach
the failure to the complete preceding definition.

### `P-002`: unclosed parenthesized argument

The group parser records the opening `(` before parsing its expression. At end
of input it emits a missing `)` event, labels the opening delimiter as primary,
and records end of input as the point where the close was expected. The partial
group stays in the concrete tree but cannot project to resolver input.

### `P-003`: missing operand followed by an unclosed argument

Inside the operational body, the `+` infix parser commits to a right operand.
When it sees the body's `}`, it emits `parse.expected-operand` related to `+`
and a missing-expression node before the close. Recovery does not consume `}`;
the block parser closes the body normally.

Parsing then continues with the program result. Its opening `(` reaches end of
input and emits the independent `parse.unclosed-group` failure. Because the
first recovery synchronized at the existing brace and did not invent tokens
beyond it, no errors derived only from the missing operand are produced. The
result is exactly the two required structured diagnostics.

These traces define candidate behavior, not final wording or punctuation.

## Comparison

| Criterion | Direct spanned AST | Event-producing recursive descent | Parser combinators | Generated parser |
| --- | --- | --- | --- | --- |
| Grammar locality | Direct functions are local; AST construction can spread edits | Feature parser plus one closed dialect dispatch point | Local combinators, subject to shared commitment and recovery contracts | Local grammar production, plus actions and generated conflicts |
| Application and infix precedence | Explicit precedence code | Explicit precedence code plus token-complete events | Needs dedicated precedence combinators or Pratt subparser | Generator declarations or layered productions |
| Non-associative equality | Direct check | Direct check with error node around retained tokens | Requires committed semantic check | Grammar or action-specific rejection |
| `P-001` context | Program function can name the missing result | Program event context retains completed globals and EOF | Requires production-specific reason | Requires custom production or action |
| `P-002` opening span | Must retain delimiter separately | Opening token remains in tree | Combinator state must retain it | Tree action must retain it |
| `P-003` cascade control | Manual synchronization | Manual synchronization recorded as events | Requires cut and recovery primitives | Requires custom error production or recovery hook |
| Source coverage | Only if AST stores all required tokens or parallel data | Complete for the lexer token stream | Depends on output sink | Depends on generated tree actions |
| Formatter/editor pressure | Weaker if punctuation is discarded | Concrete tree is reusable without exposing recovery nodes downstream | Comparable if it emits the same tree | Comparable if actions emit the same tree |
| Specification independence | Preserved | Preserved | Preserved if combinator structure is not published as grammar | Requires explicit separation from generator grammar |
| Current machinery | Smallest | Adds events, concrete tree, and projection | Adds generic control plus the same recovery concepts | Adds generator, implementation grammar, actions, and recovery integration |

## Conclusion

The evidence favors event-producing recursive descent with a dedicated Pratt or
precedence-climbing expression layer, token-complete error-bearing concrete
syntax, and a separate validated surface-AST projection. Whether the lexer
exposes trivia remains a separate question.

The recommendation is about responsibilities, not a parser library. Grammar
features own their local parsers. One explicit dialect assembly point lists the
accepted global, prefix, infix, pattern, and type forms. The event layer owns
complete coverage of lexer tokens and recovery structure. Projection owns the
invariant that resolver input contains no missing or error nodes.

This organization gives `P-001` through `P-003` direct recovery paths and keeps
operator changes separate from nested constructs. It also preserves enough
source structure for presentation-specific diagnostics and later tooling
without making the concrete tree semantic authority.

The written evidence does not select a parser crate, tree library, token-storage
strategy, incremental-reparse algorithm, or layout policy. A bounded code probe
should wait until an accepted architecture and proposed syntax define which of
those implementation details must be measured.

## Accepted outcome

[AD-0005](../../../../decisions/AD-0005-parser-architecture.md) accepts these
properties:

- lexing and parsing are separate checked boundaries with source spans on every
  token;
- grammar-shaped feature parsers emit events for a token-complete concrete syntax
  representation;
- expressions use one explicit application and infix precedence mechanism;
- the selected parser dialect has one closed assembly point for feature forms
  and operator entries;
- parser recovery preserves missing and error nodes only in the error-bearing
  surface representation;
- projection to resolver input fails while recovery nodes remain;
- parser diagnostics carry structured reasons, primary spans, related spans,
  expected forms, and synchronization context;
- implementation grammar structure remains non-normative and is checked against
  the applicable specification grammar.

The decision does not accept provisional Ash syntax, choose a parser or tree
library, define layout or semicolon behavior, require incremental parsing, or
settle the final expression versus result-binding question.

## Remaining questions

- Which concrete tree and event representation gives sufficient source coverage
  without storing redundant span data?
- Should the first retained parser preserve trivia losslessly even though the
  current corpus excludes comments?
- How should multiline equation bodies and logical `line_end` tokens interact?
- Which recovery synchronization sets remain stable as declarations and nested
  constructs grow?
- When does grammar size justify comparing a generated implementation grammar
  again?

These questions need accepted syntax or a larger corpus before a code probe can
answer them without inventing language behavior.

## Retention boundary

This comparison uses written control and recovery traces. It creates no parser
prototype. Any later prototype remains disposable until an accepted
architectural decision and implementation task retain it. Its concrete grammar
must remain separate from normative Ash syntax.
