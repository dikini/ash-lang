# Lexical Structure

An Ash source file is UTF-8 text. Mini-Ash identifiers, reserved words,
punctuation, and literal spellings use ASCII characters. A byte order mark is
not part of the source language.

## Tokens

An identifier starts with an ASCII lowercase letter or underscore and continues
with ASCII letters, decimal digits, or underscores. The reserved words `fn`,
`let`, `Int`, `Bool`, `Unit`, `true`, and `false` cannot be identifiers.

An integer literal is either `0` or a nonzero decimal digit followed by zero or
more decimal digits. Its value is the corresponding mathematical non-negative
integer. There is no fixed-width overflow. A leading zero in a multi-digit
integer is invalid. A leading `-` is not part of an integer literal.

The remaining tokens are `(`, `)`, `{`, `}`, `:`, `=`, `==`, `+`, `*`, and
`->`. The longest token wins where one spelling prefixes another, as with `=`
and `==`.

Mini-Ash has no comments, string or character literals, escapes, Unicode
identifiers, or negative literals. An uppercase-starting word other than a
reserved type name is also invalid.

This source is rejected with the lexical reason `lex.comment`. The executable
test
`lexical_comment_rejection_example_has_its_documented_reason` checks the
example:

```ash
// comments are not in Mini-Ash
1
```

## Whitespace and logical lines

Spaces and horizontal tabs are whitespace and separate tokens where needed.
The lexer recognizes LF and CRLF as line-break sequences. LF has a one-byte
source span, CRLF has a two-byte source span, and each counts as one line break.
A bare carriage return is invalid.

At file level and inside the nearest enclosing braced block, a line break
produces one logical line boundary. Inside parentheses it is whitespace rather
than a boundary. A braced block establishes its own block context even when it
occurs inside parentheses. Line breaks within that block are boundaries. When
the block ends, the surrounding parenthesized context resumes. Empty logical
lines are ignored.

An unparenthesized infix expression occupies one logical line. A binding
initializer or equation body may continue through balanced parentheses or a
complete nested block or function body. Indentation has no lexical meaning, and
an operator at the end of a line does not continue an expression implicitly.

These rules make both LF and CRLF valid source layout while preserving exact
source locations for diagnostics.
