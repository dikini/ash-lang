# Lexical Structure

An Ash source file is UTF-8 text. Ash identifiers, reserved words,
punctuation, module paths, and integer spellings use ASCII characters. Quoted
foreign-declaration strings may contain UTF-8 text. A byte
order mark is not part of the source language.

## Tokens

An ordinary identifier starts with an ASCII lowercase letter or underscore and
continues with ASCII letters, decimal digits, or underscores. Ordinary
identifiers name term binders and module-path segments. A constructor, nominal
type, interface, effect, type-variable, module-alias, or uppercase import
identifier starts with an ASCII uppercase letter and has the same continuation
characters.
Resolution determines the meaning of an uppercase occurrence from its
syntactic position and scope.

The reserved words `fn`, `let`, `rec`, `and`, `type`, `newtype`, `interface`,
`impl`, `effect`, `perform`, `handle`, `with`, `resume`, `discard`, `resource`,
`hook`, `register`, `cleanup`, `where`,
`match`, `import`, `as`, `pub`, `opaque`, `Int`, `Bool`, `Unit`, `true`, and
`false` cannot be identifiers. The single spelling `_` is the
wildcard token rather than an ordinary identifier; spellings such as `_tail`
remain ordinary identifiers.

`publish` remains an ordinary operation identifier. `cell` is contextual in a
resource acquisition and remains an ordinary identifier elsewhere.
Foreign-declaration words such as `foreign`, `library`, `profile`, `repr`,
`symbol`, `signed`, `unsigned`, `size_t`, `name`, `abi`, `operand`, `output`,
`outcome`, `otherwise`, `from`, `scalar`, `readable`, `result` and `void` are contextual
in those declarations and do not become generally reserved identifiers.
`builtin` is reserved as a module-root name, not as an
identifier; [name resolution](name-resolution.md#compiler-owned-cell-module)
defines that root's fixed import.

An integer literal is either `0` or a nonzero decimal digit followed by zero or
more decimal digits. Its value is the corresponding mathematical non-negative
integer. There is no fixed-width overflow. A leading zero in a multi-digit
integer is invalid. A leading `-` is not part of an integer literal.

The remaining punctuation admitted by Ash is `(`, `)`, `{`, `}`, `<`, `>`,
`@`, `.`, `:`, `=`, `==`, `+`, `*`, `->`, `=>`, `!`, `|`, and comma. `@`
introduces a named module root. A period separates module-path segments, a
module alias from a qualified member, or an effect from one of its operations;
it does not begin a floating-point literal. `!` introduces a latent effect row
on a computation result. Angle brackets delimit parameter lists on nominal, global, and
implementation declarations, method parameter lists, named type applications,
and interface declarations and applications. Angle brackets delimit nonempty
ordered parameter and argument lists on interfaces. They also
delimit effect declaration parameter lists and named effect applications. Every
written angle-bracketed parameter or argument list is nonempty. The longest
token wins where one spelling prefixes another.
Semicolon is recognized only to provide its specified source rejection; no
grammar production admits it as source punctuation.
The lexer also recognizes a standalone minus, but no production in the admitted
subset uses it.

Foreign profile and native-symbol names use double-quoted strings. Their
contents admit `\"`, `\\`, `\n`, `\r`, `\t` and `\0` escapes; other escapes,
unescaped ASCII control characters and a missing closing quote reject. These
declaration strings specify profile and native-symbol data. This checkpoint
does not standardize the experimental ordinary `String` expressions. Ash has no
comments, character literals, Unicode identifiers,
floating-point literals, or negative integer expressions.

This complete entry module is rejected with the lexical reason `lex.comment`.
The executable test
`lexical_comment_rejection_example_has_its_documented_reason` checks the
example:

```ash
// comments are not in Ash
main : Unit -> Int
main () = 1
```

## Whitespace and logical lines

Spaces and horizontal tabs are whitespace and separate tokens where needed.
The lexer recognizes LF and CRLF as line-break sequences. LF has a one-byte
source span, CRLF has a two-byte source span, and each counts as one line break.
A bare carriage return is invalid.

At module level and inside the nearest enclosing braced block, a line break
produces one logical line boundary. Inside parentheses it is whitespace rather
than a boundary. A braced block establishes its own block context even when it
occurs inside parentheses. Line breaks within that block are boundaries. When
the block ends, the surrounding parenthesized context resumes. Empty logical
lines are ignored.

An import or module declaration ends at a module-level logical line boundary.
An unparenthesized infix expression occupies one logical line. A binding
initializer or equation body may continue through balanced parentheses or a
complete nested block or function body. Indentation has no lexical meaning, and
an operator at the end of a line does not continue an expression implicitly.

These rules make both LF and CRLF valid source layout while preserving exact
source locations for diagnostics.
