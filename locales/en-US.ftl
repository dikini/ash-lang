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
entry-missing-main = The entry module must define its own `main`; importing one is not enough.
entry-polymorphic = The entry point `main` must have no type parameters.
entry-domain = The entry point `main` must be a function accepting `Unit`.
entry-effects = Calling `main` must require no effects from its caller.
entry-open-result = The result type of `main` must be fully determined, with no type parameters, quantified types, or open effect rows.
entry-constrained = The entry point `main` must require no interface evidence from its caller.
entry-module = This is the entry module.
resolve-type-kind = The interface `{ $name }` cannot be used as a value type.
resolve-interface-kind = The name `{ $name }` does not refer to an interface.
resolve-effect-kind = The name `{ $name }` does not refer to an effect.
resolve-mixed-type-row-roles = The parameter `{ $name }` is used both as a type and as an effect-row tail; these require different kinds.
incompatible-name-role = This name has an incompatible role here.
type-definition-result = The function body must return `{ $expected }`, but returns `{ $found }`.
type-operator-operand = This operator requires an `Int` operand, but this operand has type `{ $found }`.
type-argument = This function argument must have type `{ $expected }`, but has type `{ $found }`.
type-not-applicable = This expression cannot be called: its type is `{ $found }`, not a function type.
type-equation-signature = This equation needs a function signature, but its signature has type `{ $found }`.
type-found = This has type `{ $found }`.
type-result-annotation = This signature requires result type `{ $expected }`.
type-operator-requirement = This operator requires `Int` operands.
type-function-domain = This function requires an argument of type `{ $expected }`.
type-application = This is the containing function application.
type-equation-head = This equation head requires a function signature.
entry-main = This is the local `main` declaration.
kind-expected-type = This position requires a complete value type (kind `Type`), but has kind `{ $found }`.
kind-not-applicable = The applied type has kind `{ $found }` and cannot take type arguments.
kind-argument = This argument needs kind `{ $expected }`, but has kind `{ $found }`.
kind-found = Found kind `{ $found }` here.
kind-found-declaration = This declaration fixes the kind as `{ $found }`.
kind-required-declaration = This declaration requires argument kind `{ $expected }`.
resolve-unknown-term = No term named `{ $name }` is in scope.
resolve-unknown-operation = The selected effect declares no operation named `{ $name }`.
unresolved-name = This name could not be resolved here.
resolve-duplicate-global = The name `{ $name }` is already declared in this scope.
resolve-duplicate-type = The name `{ $name }` is already used by a type, interface, or effect.
resolve-duplicate-constructor = The constructor `{ $name }` is already declared.
resolve-duplicate-alias = The module alias `{ $name }` is already bound.
resolve-duplicate-parameter = The type parameter `{ $name }` is already declared in this scope.
resolve-duplicate-binder = The pattern binds `{ $name }` more than once.
resolve-duplicate-recursive-member = The recursive group defines `{ $name }` more than once.
duplicate-name = This name conflicts with an earlier declaration.
first-declaration = First declaration of this name.
first-definition = Complete earlier definition.
resolve-equation-name = The equation is named `{ $name }`, but its signature declares `{ $expected }`. Rename the equation to `{ $expected }`.
resolve-newtype-name = The constructor is named `{ $name }`, but this newtype requires `{ $expected }`.
resolve-unused-parameter = The explicit type parameter `{ $name }` is not used in the declaration header.
resolve-import-conflict = The name `{ $name }` conflicts with a binding already in scope for this file.
resolve-opaque-constructor = The constructor `{ $name }` belongs to an opaque type and is not accessible here.
resolve-private-export = The declaration `{ $name }` is private to its defining module.
resolve-missing-export = No imported declaration named `{ $name }` is available in this namespace.
resolve-missing-module-alias = No module alias named `{ $name }` is in scope.
incorrect-name = This name does not match the required spelling.
unused-parameter = This parameter is not used in the declaration header.
conflicting-binding = This binding conflicts with a file-wide name.
inaccessible-name = This name is not accessible here.
required-name-declaration = This declaration determines the required name.
inaccessible-declaration = The inaccessible declaration is here.
resolve-unknown-type = No type named `{ $name }` is in scope.
resolve-unknown-row-parameter = No effect-row parameter named `{ $name }` is in scope.
resolve-unknown-interface-parameter = The owning interface has no parameter named `{ $name }`.
resolve-unknown-constructor = No constructor named `{ $name }` is in scope.
resolve-unknown-interface = No interface named `{ $name }` is in scope.
resolve-unknown-effect = No effect named `{ $name }` is in scope.
resolve-unexported-effect = The selected module exports no effect named `{ $name }`.
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
