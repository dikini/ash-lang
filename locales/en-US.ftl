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
input-invalid-utf8 = `{ $path }` is not a valid UTF-8 source file.
import-target = The failure occurred while processing this import.
module-root-unavailable = Cannot use `{ $path }` as a directory for module root `{ $root }`.
module-root-io = Cannot use `{ $path }` for module root `{ $root }`: { io-cause }
input-read = Cannot read `{ $path }`: { io-cause }
io-cause = { $kind ->
        [not-found] the file or directory does not exist.
        [permission-denied] access is denied.
        [connection-refused] the connection was refused.
        [connection-reset] the connection was reset.
        [host-unreachable] the host is unreachable.
        [network-unreachable] the network is unreachable.
        [connection-aborted] the connection was aborted.
        [not-connected] the connection is not established.
        [addr-in-use] the address is already in use.
        [addr-not-available] the address is unavailable.
        [network-down] the network is down.
        [broken-pipe] the pipe is closed.
        [already-exists] the target already exists.
        [would-block] the operation would block.
        [not-a-directory] a path component is not a directory.
        [is-a-directory] the target is a directory.
        [directory-not-empty] the directory is not empty.
        [read-only-filesystem] the filesystem is read-only.
        [stale-network-file-handle] the network file handle is stale.
        [invalid-input] an input parameter is invalid.
        [invalid-data] the operation encountered invalid data.
        [timed-out] the operation timed out.
        [write-zero] the write operation made no progress.
        [storage-full] the storage is full.
        [not-seekable] the file does not support seeking.
        [quota-exceeded] a resource quota was exceeded.
        [file-too-large] the file exceeds a size limit.
        [resource-busy] the resource is busy.
        [executable-file-busy] the executable file is busy.
        [deadlock] the operation would cause a deadlock.
        [crosses-devices] the operation crosses filesystem boundaries.
        [too-many-links] the file has too many links.
        [invalid-filename] the file name is invalid or too long.
        [argument-list-too-long] the argument list is too long.
        [interrupted] the operation was interrupted.
        [unsupported] the operation is unsupported.
        [unexpected-eof] the file ended unexpectedly.
        [out-of-memory] memory allocation failed.
        [other] an uncategorized I/O error occurred.
       *[uncategorized] an uncategorized I/O error occurred.
    }
syntax-depth = Parsing `{ $path }` reached the compiler's nesting limit of { $limit }.
module-reserved-root = The module root `{ $root }` is reserved by Ash.
module-duplicate-root = The module root `{ $root }` is configured more than once.
module-invalid-root-name = `{ $root }` is not a valid lowercase Ash identifier for a module root.
module-unknown-root = No module root named `{ $root }` is configured.
module-unknown-builtin = This import names no compiler-owned module.
module-not-found = The imported source file `{ $path }` does not exist.
module-import-cycle = This import creates a dependency cycle through `{ $path }`.
module-path-escape = The imported source file `{ $path }` is outside a root that must contain it.
module-missing-parent = Ash retained a module path without a parent directory.
module-missing-segments = Ash retained an import path without any module-name segments.
source-ids = Ash cannot allocate another source identity for `{ $path }`.
projection-recovery = Ash encountered syntax-recovery markers while converting `{ $path }` to its internal form.
projection-malformed = Ash found inconsistent internal syntax for `{ $path }`: { $cause ->
    [unexpected-finish] a closing event has no opening event.
    [unclosed-node] a syntax node was not closed.
    [invalid-root-count] syntax events do not form one complete rooted tree.
    [token-out-of-range] a token index is outside the retained token stream.
    [duplicate-token] a token was retained more than once.
    [missing-token] a token is missing from the syntax tree.
    [token-out-of-order] tokens are not in source order.
    [foreign-span] a span belongs to another source file.
    [invalid-span] source spans or end-of-input markers are inconsistent.
   *[unexpected-shape] a syntax node has an unexpected structure.
    }
source-unrepresentable-span = Ash encountered an unrepresentable source length or token offset while constructing a span for `{ $path }`.
source-path-limit = The display path for `{ $path }` exceeds Ash's source-model limit.
source-text-limit = The text in `{ $path }` exceeds Ash's source-model size limit.
source-line-limit = `{ $path }` has more lines than Ash's source model can represent.
source-column-limit = A line in `{ $path }` has more columns than Ash's source model can represent.
source-range = Ash produced byte range { $start }..{ $end } outside the { $length } bytes of `{ $path }`.
source-foreign-span = Ash used a span from source { $found } where source { $expected } was required for `{ $path }`.
source-offset = Ash used byte offset { $offset } beyond the { $length } bytes of `{ $path }`.
source-code-point = Ash used byte offset { $offset } inside a UTF-8 code point in `{ $path }`.
source-line-state = Ash's internal line index for `{ $path }` is inconsistent.
module-resource = Ash exhausted resources for { $resource ->
    [graph-identities] module graph identities
    [sources] module sources
    [edges] import edges
    [path-segments] module path segments
    [owner-facts] module ownership facts
   *[pending-work] pending module-loading work
    }.
syntax-work = Processing `{ $path }` reached the compiler's syntax-work limit of { $limit }.
