binding-initializer = This binding needs a value of type `{ $expected }`, but its initializer has type `{ $found }`.
initializer = This initializer has type `{ $found }`.
binding-annotation = This annotation requires type `{ $expected }`.
lex-bare-carriage-return = A carriage return must be followed by a line feed (CRLF); a line feed (LF) also starts a new line.
lex-byte-order-mark = Ash source files must not contain a byte order mark (BOM).
lex-unicode-identifier = Ash identifiers use only ASCII letters, digits and underscores.
lex-comment = Ash does not support comments.
lex-negative-literal = Ash does not support negative integer literals.
lex-invalid-integer-literal = An integer literal must be 0 or a sequence of ASCII digits without a leading zero.
lex-invalid-identifier = An Ash identifier must start with an ASCII letter or underscore and continue with ASCII letters, digits or underscores.
lex-unknown-character = This character cannot begin an Ash token.
parse-expected =
    { $expected ->
        *[expression] An expression is required here.
        [operand] An operand is required here.
        [identifier] An identifier is required here.
        [type] A type is required here.
        [effect-row] An effect row is required here.
        [kind] A kind is required here.
        [pattern] A pattern is required here.
        [interface-parameter] An interface type parameter is required here.
        [interface-method] An interface method signature is required here.
        [effect-operation] An effect operation signature is required here.
        [interface-application] An interface application is required here.
        [implementation-method] An implementation method equation is required here.
        [comma] `,` is required here.
        [left-paren] `(` is required here.
        [right-paren] `)` is required here.
        [left-brace] `{ "{" }` is required here.
        [right-brace] `{ "}" }` is required here.
        [greater] `>` is required here.
        [colon] `:` is required here.
        [equal] `=` is required here.
        [arrow] `->` is required here.
        [fat-arrow] `=>` is required here.
        [line-end] A logical line end is required here.
        [end-of-file] The input must end here.
    }
parse-found =
    { $found ->
        [identifier] An identifier occurs here.
        [uppercase-identifier] An uppercase identifier occurs here.
        [integer] An integer literal occurs here.
        [line-end] A logical line ends here.
        [end-of-file] The input ends here.
       *[other] Found `{ $found }` here.
    }
parse-operand = The operator needs a right operand.
parse-unclosed-group = This opening parenthesis has no matching `)`.
parse-repeated-equality = Equality comparisons cannot be chained without parentheses.
parse-recursive-member = A recursive binding member is required here.
parse-unexpected-and = `and` is allowed only within a recursive binding group.
parse-semicolon = Ash does not support semicolons.
parse-unexpected-token = This token is not allowed at this grammar position.
parse-recovery = Parsing continues from this position.
parse-synchronization = Parsing resumes at this boundary.
