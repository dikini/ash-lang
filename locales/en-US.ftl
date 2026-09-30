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
handler-argument-count = This effect instance has the wrong number of type arguments for its declaration.
effect-row-union = This expression combines effect rows that have no most general union.
method-implicit-parameters = Method type parameters must be explicitly declared in the method's parameter list.
method-missing-interface-parameter = This method type must mention every interface parameter.
method-missing-determinant = This method type must mention every determining interface parameter.
interface-parameter-declaration = An interface parameter is declared here.
missing-method-parameter = This required interface parameter is absent from the method type.
impl-determination-coverage = This dependent argument uses a type variable that does not occur in the implementation's determining arguments.
dependent-variable = This dependent type variable is declared here.
determinant-missing-variable = This determining argument does not contain the dependent type variable.
undetermined-parameter = A type variable in this requirement's selection key is absent from the definition's value type. It cannot be determined from that type.
requirement-only-parameter = This type parameter does not occur in the definition's value type.
impl-overlap = This implementation can match the same interface application as an earlier available implementation.
impl-determination-conflict = These implementations can match the same determining arguments but require incompatible dependent arguments.
earlier-implementation = The earlier implementation is defined here.
earlier-implementation-import = This import made the earlier implementation available.
later-implementation = The later implementation is defined here.
later-implementation-import = This import made the later implementation available.
interface-argument-count = This interface application has the wrong number of type arguments: expected { $expected }, supplied { $found }.
interface-parameters = The interface parameter list is declared here.
constraint-unsatisfied = No available evidence satisfies this interface requirement.
constraint-ambiguous = The types in this interface requirement are not sufficiently determined to select evidence.
constraint-cycle = Selecting evidence for this requirement returns to a requirement whose selection is already in progress.
selection-declaration = This declaration introduced the interface requirement.
selection-import = This import made the declaration available.
selection-interface = This interface participates in the failing evidence selection.
selection-implementation = Evidence selection followed this implementation.
selection-method = This implementation method supplies the selected evidence.
selection-implementation-import = This import made the selected implementation available.
impl-orphan = This module owns neither the interface nor an outer nominal type in the implementation's selection key. Dependent arguments and nested nominal types do not establish ownership.
impl-foreign-interface = This selected interface belongs to another module.
constraint-private-interface = This public definition exposes a private interface in its requirements.
impl-private-interface = A public implementation must use public interfaces both for its head and for its prerequisites.
duplicate-requirement = This exact interface requirement is declared more than once.
private-interface-declaration = This interface is declared private here.
earlier-requirement = The earlier identical requirement is here.
impl-variable-head = An implementation's selection key cannot consist only of bare type variables.
impl-prerequisite-variable = This prerequisite uses a type variable that does not occur in the implementation head.
impl-prerequisite-decrease = This generic prerequisite does not have a strictly smaller selection key than the implementation head.
impl-selected-interface = This is the interface being implemented.
impl-head-variables = Every prerequisite type variable must occur in this implementation head.
impl-head-decrease = Each prerequisite key argument must equal or be a strict syntactic subterm of its corresponding head argument, with at least one strict decrease.
interface-method-function = An interface method must have a function type with a top-level arrow.
interface-method-declaration = This method signature is declared here.
impl-missing-method = This implementation does not supply a required interface method.
impl-duplicate-method = This implementation supplies the same interface method more than once.
impl-extra-method = This method is not declared by the implemented interface.
impl-interface = The implemented interface is declared here.
evidence-local-key = This evidence declaration needs an active local nominal type in its selection key: the determinant arguments, or all arguments when there is no determination edge.
evidence-duplicate = An active evidence declaration already supplies this exact interface application.
evidence-determination-conflict = These evidence declarations have the same determining arguments but different dependent arguments.
evidence-missing-method = This evidence declaration does not supply a required interface method.
evidence-duplicate-method = This evidence declaration supplies the same method more than once.
evidence-extra-method = This method does not belong to the interface supplied by this evidence declaration.
evidence-earlier = The earlier active evidence declaration is here.
evidence-required-method = This interface method must be supplied.
evidence-earlier-method = This method was already supplied here.
evidence-interface = The supplied interface is declared here.
type-polymorphic-recursion = This recursive call requires type { $expected }, but uses { $found }. Recursive calls must keep the same type instantiation.
recursive-function = This recursive function is checked with one fixed type instantiation.
recursive-application = This application supplies the recursive argument.
missing-handled-effect = The handled computation must explicitly request this exact effect instance, including its type arguments.
effect-row-exclusion = This computation requires an effect excluded from the row tail. An effect written before a row tail cannot also occur in that tail with the same type arguments.
effect-row-exclusion-contract = This type is required here.
discard-unknown = Ash cannot prove that this continuation can be discarded without skipping required completion.
discard-clause = This discard would skip a clause that still requires completion.
discard-cleanup = This discard would skip a cleanup action that must complete.
discard-request = This request or call can capture the continuation.
discard-clause-owner = This clause still requires completion.
discard-cleanup-owner = This cleanup action must complete.
effect-row-cleanup-requirement = The cleanup effects do not satisfy the required effect row.
effect-row-removal = Ash cannot determine the effect row remaining after this handler removes its exact effect instance.
effect-row-infinite-function = This function would require an infinite effect row.
effect-row-function-mismatch = This function body's effects do not match its function type.
effect-row-function-outside-declared = This function body requests effects outside its declared effect row.
effect-row-cleanup-inference = Ash cannot infer a most general effect row for this cleanup action.
effect-row-cleanup-outside-expected = This cleanup action requests effects outside its expected effect row.
effect-row-discard-cleanup = The effects of this discard do not match the cleanup actions it owns.
handler-operation-owner = This operation belongs to a different effect declaration.
handler-clause-count = This handler must contain exactly one clause for every operation of the handled effect.
handler-operation-index = This operation is not declared by the handled effect.
handler-duplicate-operation = This handler repeats a clause for the same operation.
equation-pattern-count = Every equation in this group must have the same positive number of parameter patterns.
equation-declared-arrows = This equation has more parameter patterns than function arrows in its declared type.
hook-api = An API used by `hook` or `register` must declare exactly one operation, `publish`, whose parameter and result types are equal before type arguments are substituted.
function-needs-context = This anonymous function needs an expected function type.
function-context-binding = Add a function type annotation to this binding.
function-context-result = The type of this result must be inferred without an expected function type.
function-context-application = This application requires the function expression's type to be inferred first.
function-context-operator = This operator requires the operand's type to be inferred first.
type-mismatch = This expression must have type `{ $expected }`, but it has type `{ $found }`.
local-nominal-escape = This type or effect row exposes a local nominal type outside its scope.
local-nominal-scope = This scope owns the local nominal type.
resource-escape = This value or computation depends on a resource that would be out of scope.
resource-acquisition = This resource is acquired here and must remain within its scope.
recursion-initializer = This recursive initializer must be a direct `fn` expression.
recursion-root = This recursive data initializer must start with a fully applied constructor of its declared nominal type.
recursion-group = This declaration introduces the recursive group.
recursion-member-annotation = The recursive member's type is declared here.
newtype-representation-cycle = These newtype representations form a recursive cycle.
newtype-cycle-member = This declaration participates in the representation cycle.
cleanup-context = Discard would remove a handler that this cleanup action still needs.
cleanup-required-action = This cleanup action requires the handler.
cleanup-abandoned-handler = Discard would abandon this handler.
type-infinite = This expression would require an infinite type: a type would have to contain itself.
type-ambiguous = Ash cannot determine a complete type for this expression.
recursion-unguarded-use = This recursive value cannot be passed through this expression during initialization.
continuation-not-consumed = This path can finish without resuming or safely discarding the continuation.
continuation-already-consumed = This path has already resumed or discarded the continuation; it cannot do so again.
continuation-capture = This nested scope cannot capture the enclosing clause's right to resume or discard.
pattern-type-mismatch = This pattern cannot match a value of type `{ $expected }`.
pattern-constructor-payload = This constructor has the wrong payload shape.
pattern-constructor-owner = This constructor belongs to a different nominal type than the value being matched.
pattern-refutable-binding = This binding pattern can fail; for example, it does not match `{ $witness }`.
pattern-refutable-function = This function parameter pattern can fail; for example, it does not match `{ $witness }`.
pattern-refutable-handler = This handler operation pattern can fail; for example, it does not match `{ $witness }`.
coverage-non-exhaustive = These cases do not cover every possible input; for example, `{ $witness }` is not covered.
coverage-empty-match = A match requires at least one arm.
coverage-redundant-case = This case can never be selected because earlier cases already cover its inputs.
resolve-identity-exhausted = Ash exhausted its identifier space for { $space ->
    [interface] interfaces in a module
    [method] methods in an interface
    [effect] effects in a module
    [operation] operations in an effect
    [implementation] implementations in a module
    [requirement] interface requirements in a declaration
    [nominal] nominal types in a module
    [constructor] constructors in a declaration
    [type-binder] type parameters
    [local-nominal] local nominal types
    [continuation] continuations
    [lexical-evidence] lexical evidence and resource providers
   *[term-binder] value bindings
    }.
resolve-duplicate-effect = This effect row contains the same effect instance more than once.
first-effect-instance = The first occurrence of this effect instance is here.
resolve-operation-shape = An effect operation needs an outer function arrow without an explicit effect row.
resolve-sealed-provider = Only resource acquisition may introduce a compiler-owned resource provider.
resolve-builtin-required = This resource acquisition requires a direct import of `{ $builtin }`.
resolve-continuation-outside = `{ $operation }` is only available inside an effect operation clause.
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
source-ids-unlocated = Ash cannot allocate another source identity.
source-unrepresentable-span-unlocated = Ash encountered an unrepresentable source length or token offset while constructing a span.
source-path-limit-unlocated = The display path exceeds Ash's source-model limit.
source-text-limit-unlocated = The source text exceeds Ash's source-model size limit.
source-line-limit-unlocated = The source has more lines than Ash's source model can represent.
source-column-limit-unlocated = A source line has more columns than Ash's source model can represent.
source-range-unlocated = Ash produced byte range { $start }..{ $end } outside the source's { $length } bytes.
source-foreign-span-unlocated = Ash used a span from source { $found } where source { $expected } was required.
source-offset-unlocated = Ash used byte offset { $offset } beyond the source's { $length } bytes.
source-code-point-unlocated = Ash used byte offset { $offset } inside a UTF-8 code point.
source-line-state-unlocated = Ash's internal source line index is inconsistent.
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
syntax-depth-unlocated = Source processing reached the compiler's structural-depth limit of { $limit }.
syntax-work-unlocated = Source processing reached the compiler's syntax-work limit of { $limit }.
projection-recovery-unlocated = Ash encountered syntax-recovery markers while converting source syntax to its internal form.
projection-malformed-unlocated = Ash found inconsistent internal syntax: { $cause ->
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
determination-empty-determinant = The determining side must contain at least one interface parameter.
determination-empty-dependent = The dependent side must contain at least one interface parameter.
determination-both-sides = An interface parameter cannot occur on both sides of a determination.
determination-omitted = The determination must include every interface parameter.
determination-repeated = This parameter is repeated on the same side of the determination.
determination-order = Parameters on each side of a determination must follow their interface declaration order.
determination-key-occurrence = This parameter also occurs on the determining side.
determination-missing-parameter = This interface parameter is missing from the determination.
determination-earlier-occurrence = The parameter already occurs here on this side.
determination-preceding-occurrence = This preceding occurrence is out of declaration order with the highlighted parameter.
determination-requirement-conflict = These requirements have the same determining arguments but different dependent arguments.
determination-prerequisite-conflict = These prerequisites have the same determining arguments but different dependent arguments.
determination-improvement-conflict = The determining arguments `{ $key }` require dependent arguments `{ $expected }`, but these dependent arguments are `{ $found }`.
determination-earlier-requirement = This earlier requirement fixes different dependent arguments for the same determining arguments.
determination-earlier-prerequisite = This earlier prerequisite fixes different dependent arguments for the same determining arguments.
determination-expected-source = This source fixes the expected dependent tuple.
core-build-arena-id-exhausted = The compiler has exhausted its Core arena identities.
core-build-node-id-exhausted = The compiler has exhausted the node identities in this Core arena.
core-build-binder-id-exhausted = The compiler has exhausted its Core binder identities.
core-build-duplicate-binder-reservation = The compiler reserved the same resolved binder identity more than once.
core-build-binder-reservation-phase-started = The compiler tried to reserve resolved binder identities after Core binder construction had begun.
core-build-unreserved-resolved-binder = The compiler tried to construct a Core binder without reserving its resolved identity.
core-build-duplicate-resolved-binder = The compiler tried to construct a resolved Core binder more than once.
core-build-foreign-binder = The compiler used a binder from a different Core arena.
core-build-type-depth-exceeded = A type exceeds the compiler's Core type nesting limit.
core-build-type-work-exceeded = Core construction exhausted the compiler's type-work budget.
core-build-origin-depth-exceeded = Source-origin metadata exceeds the compiler's Core nesting limit.
core-build-pattern-depth-exceeded = A pattern exceeds the compiler's Core pattern nesting limit.
core-build-invalid-payload = The compiler encountered inconsistent state while rebuilding a Core payload.
core-build-invalid-node-id = The compiler requested a root node that does not belong to this Core arena.
coverage-state-limit = Pattern coverage analysis reached the compiler's state limit.
coverage-work-limit = The compiler could not complete pattern coverage analysis within its work resources.
compiler-type-resources = The compiler ran out of resources for type checking and type construction.
compiler-constraint-resources = The compiler ran out of resources for interface and constraint processing.
effect-core-unavailable = The compiler tried to lower effect syntax through its pure Core path.
evidence-unavailable-implementation = The compiler selected an implementation that is not available in the module containing this use.
core-validation-dialect = The compiler stored a Core node from a different dialect than the selected program.
core-validation-root = The compiler selected a root node that is not valid in this Core arena.
core-validation-cycle = The compiler constructed a cycle in the Core expression graph.
core-validation-unreachable = The compiler retained a Core node that cannot be reached from the program root.
core-validation-resource = The compiler could not complete Core validation within its work or storage limits.
core-validation-handler = The compiler produced inconsistent handler or capture-safety information in Core.
core-validation-handler-node = { core-validation-handler } Core node: { $node }.
elaboration-invalid-state = The compiler could not construct typed Core because its elaboration state is inconsistent.
core-validation-node-type = The compiler produced inconsistent type information for a Core node or its checked evidence.
core-validation-node-type-node = { core-validation-node-type } Core node: { $node }.
core-validation-application-type = The compiler produced a Core application that does not match its checked function or argument information.
core-validation-application-type-node = { core-validation-application-type } Core node: { $node }.
core-validation-registry = The compiler's Core declaration or module registry is inconsistent.
core-validation-registry-node = { core-validation-registry } Core node: { $node }.
evidence-unknown-identity = The compiler could not match linked interface evidence to a unique declaration with the expected owner.
evidence-invalid-root = The compiler's selected evidence does not establish the interface requirement at this location.
core-validation-resource-node = { core-validation-resource } Core node: { $node }.
core-validation-dialect-node = { core-validation-dialect } Core node: { $node }.
core-validation-root-node = { core-validation-root } Core node: { $node }.
core-validation-cycle-node = { core-validation-cycle } Core node: { $node }.
core-validation-unreachable-node = { core-validation-unreachable } Core node: { $node }.
core-validation-missing-child = The compiler stored a Core node whose declared child edge cannot be read.
core-validation-missing-child-node = { core-validation-missing-child } Core node: { $node }.
core-validation-foreign-arena = The compiler stored a Core node reference from a different arena.
core-validation-foreign-arena-node = { core-validation-foreign-arena } Core node: { $node }.
core-validation-missing-node = The compiler stored a Core node reference outside the program's stored nodes.
core-validation-missing-node-node = { core-validation-missing-node } Core node: { $node }.
core-validation-identity-range = The compiler cannot represent a stored Core node's index as a node identity.
core-validation-identity-range-node = { core-validation-identity-range } Core node: { $node }.
core-validation-empty-match = The compiler retained a Core match with no arms.
core-validation-empty-match-node = { core-validation-empty-match } Core node: { $node }.
core-validation-redundant-arm = The compiler retained Core match arm { $arm }, which is already covered by earlier arms.
core-validation-redundant-arm-node = { core-validation-redundant-arm } Core node: { $node }.
core-validation-non-exhaustive = The compiler retained a Core match that does not cover all possible inputs.
core-validation-non-exhaustive-node = { core-validation-non-exhaustive } Core node: { $node }.
core-validation-missing-origin = The compiler retained a Core node without its source origin.
core-validation-missing-origin-node = { core-validation-missing-origin } Core node: { $node }.
core-validation-origin-depth = The compiler retained a Core source-origin chain deeper than the supported limit.
core-validation-origin-depth-node = { core-validation-origin-depth } Core node: { $node }.
core-validation-related-origin-source = The compiler attached a related Core origin from a different source than its primary origin.
core-validation-related-origin-source-node = { core-validation-related-origin-source } Core node: { $node }.
core-validation-unadmitted-origin-source = The compiler retained a Core origin referring to a source not admitted to this compilation.
core-validation-unadmitted-origin-source-node = { core-validation-unadmitted-origin-source } Core node: { $node }.
core-validation-origin-range = The compiler retained Core origin byte range { $start }..{ $end }, beyond the source length of { $length } bytes.
core-validation-origin-range-node = { core-validation-origin-range } Core node: { $node }.
core-validation-origin-code-point = The compiler retained a Core origin whose byte offset { $offset } splits a UTF-8 character.
core-validation-origin-code-point-node = { core-validation-origin-code-point } Core node: { $node }.
core-validation-origin-text-limit = The compiler cannot represent the admitted source length while checking a Core origin.
core-validation-origin-text-limit-node = { core-validation-origin-text-limit } Core node: { $node }.
core-validation-origin-index = The compiler cannot represent a Core origin's byte offset as a source index.
core-validation-origin-index-node = { core-validation-origin-index } Core node: { $node }.
core-validation-empty-recursive-group = The compiler retained a Core recursive group with no members.
core-validation-empty-recursive-group-node = { core-validation-empty-recursive-group } Core node: { $node }.
core-validation-recursive-function-initializer = The compiler retained a recursive function whose initializer is not a function value.
core-validation-recursive-function-initializer-node = { core-validation-recursive-function-initializer } Core node: { $node }.
core-validation-recursive-type-abstraction = The compiler retained a polymorphic recursive function without its type abstraction.
core-validation-recursive-type-abstraction-node = { core-validation-recursive-type-abstraction } Core node: { $node }.
core-validation-recursive-type-parameters = The compiler retained a recursive type abstraction whose parameters disagree with the binding's type.
core-validation-recursive-type-parameters-node = { core-validation-recursive-type-parameters } Core node: { $node }.
core-validation-recursive-function-body = The compiler retained a recursive type abstraction whose body is not a function value.
core-validation-recursive-function-body-node = { core-validation-recursive-function-body } Core node: { $node }.
core-validation-recursive-value-type = The compiler retained a recursive binding whose type is neither a supported function type nor a nominal data type.
core-validation-recursive-value-type-node = { core-validation-recursive-value-type } Core node: { $node }.
core-validation-recursive-unknown-constructor = The compiler retained a recursive data initializer whose constructor is absent from the registry.
core-validation-recursive-unknown-constructor-node = { core-validation-recursive-unknown-constructor } Core node: { $node }.
core-validation-recursive-constructor-owner = The compiler retained a recursive data initializer using a constructor of a different nominal type.
core-validation-recursive-constructor-owner-node = { core-validation-recursive-constructor-owner } Core node: { $node }.
core-validation-recursive-missing-payload = The compiler retained a recursive data constructor without its required payload.
core-validation-recursive-missing-payload-node = { core-validation-recursive-missing-payload } Core node: { $node }.
core-validation-recursive-unexpected-payload = The compiler supplied a payload to a recursive data constructor that takes none.
core-validation-recursive-unexpected-payload-node = { core-validation-recursive-unexpected-payload } Core node: { $node }.
core-validation-recursive-data-root = The compiler retained a recursive data initializer that is not rooted in a constructor.
core-validation-recursive-data-root-node = { core-validation-recursive-data-root } Core node: { $node }.
core-validation-recursive-payload-call = The compiler retained a recursive data payload that uses recursive bindings in a call to a non-constructor.
core-validation-recursive-payload-call-node = { core-validation-recursive-payload-call } Core node: { $node }.
core-validation-recursive-payload-form = The compiler retained a recursive data payload that uses recursive bindings outside the permitted guarded forms.
core-validation-recursive-payload-form-node = { core-validation-recursive-payload-form } Core node: { $node }.
core-validation-foreign-binder-arena = The compiler retained a Core binder owned by a different arena.
core-validation-foreign-binder-arena-node = { core-validation-foreign-binder-arena } Core node: { $node }.
core-validation-duplicate-binder = The compiler declared the same Core binder identity more than once.
core-validation-duplicate-binder-node = { core-validation-duplicate-binder } Core node: { $node }.
core-validation-unknown-variable-binder = The compiler retained a Core variable whose binder is not declared.
core-validation-unknown-variable-binder-node = { core-validation-unknown-variable-binder } Core node: { $node }.
core-validation-non-lexical-scope-owner = The compiler used a non-lexical nominal identity as a local Core scope owner.
core-validation-non-lexical-scope-owner-node = { core-validation-non-lexical-scope-owner } Core node: { $node }.
core-validation-unknown-scope-owner = The compiler retained a local Core scope whose nominal owner is absent from the registry.
core-validation-unknown-scope-owner-node = { core-validation-unknown-scope-owner } Core node: { $node }.
core-validation-local-scope-type = The compiler retained a local Core scope whose result type differs from its body's type.
core-validation-local-scope-type-node = { core-validation-local-scope-type } Core node: { $node }.
core-validation-local-scope-effects = The compiler retained a local Core scope whose effects differ from its body's effects.
core-validation-local-scope-effects-node = { core-validation-local-scope-effects } Core node: { $node }.
core-validation-incomplete-scope-analysis = The compiler's scope analysis did not cover every stored Core node.
core-validation-incomplete-scope-analysis-node = { core-validation-incomplete-scope-analysis } Core node: { $node }.
core-validation-unbound-core-binder = The compiler retained a Core use without an enclosing scope for its binder.
core-validation-unbound-core-binder-node = { core-validation-unbound-core-binder } Core node: { $node }.
core-validation-unbound-local-nominal = The compiler retained a local nominal type requirement without its enclosing Core scope.
core-validation-unbound-local-nominal-node = { core-validation-unbound-local-nominal } Core node: { $node }.
core-validation-unexpected-local-scope = The compiler retained a local Core scope not listed among the registry's lexical nominal identities.
core-validation-unexpected-local-scope-node = { core-validation-unexpected-local-scope } Core node: { $node }.
core-validation-duplicate-local-scope = The compiler introduced the same local nominal identity in more than one Core scope.
core-validation-duplicate-local-scope-node = { core-validation-duplicate-local-scope } Core node: { $node }.
core-validation-missing-local-scope = The compiler retained a lexical nominal identity without a corresponding Core scope.
core-validation-missing-local-scope-node = { core-validation-missing-local-scope } Core node: { $node }.
core-validation-missing-capture-requirement = A compiler-recorded implementation capture is absent from the initializer's scope requirements.
core-validation-missing-capture-requirement-node = { core-validation-missing-capture-requirement } Core node: { $node }.
core-validation-missing-root-requirements = The compiler has no retained scope-analysis result for the Core root.
core-validation-missing-root-requirements-node = { core-validation-missing-root-requirements } Core node: { $node }.
core-validation-missing-node-requirements = The compiler needs a Core node's scope-analysis result before it is available.
core-validation-missing-node-requirements-node = { core-validation-missing-node-requirements } Core node: { $node }.
core-validation-missing-generated-type-binder = The compiler retained a generated Core type variable without its declared kind.
core-validation-missing-generated-type-binder-node = { core-validation-missing-generated-type-binder } Core node: { $node }.
core-validation-unresolved-core-inference = The compiler retained an unresolved inference variable in a Core type.
core-validation-unresolved-core-inference-node = { core-validation-unresolved-core-inference } Core node: { $node }.
core-validation-missing-type-root-requirements = The compiler has no retained type-scope requirements for the Core root.
core-validation-missing-type-root-requirements-node = { core-validation-missing-type-root-requirements } Core node: { $node }.
core-validation-unbound-core-type-variables = The compiler retained free type-variable requirements at the Core root.
core-validation-unbound-core-type-variables-node = { core-validation-unbound-core-type-variables } Core node: { $node }.
core-validation-missing-type-use-count = The compiler has no child-use count needed for Core type-scope analysis.
core-validation-missing-type-use-count-node = { core-validation-missing-type-use-count } Core node: { $node }.
core-validation-exhausted-type-use-count = The compiler consumed a Core child's type-scope requirements more times than recorded.
core-validation-exhausted-type-use-count-node = { core-validation-exhausted-type-use-count } Core node: { $node }.
core-validation-missing-type-requirement-slot = The compiler has no type-scope result slot for a referenced Core child.
core-validation-missing-type-requirement-slot-node = { core-validation-missing-type-requirement-slot } Core node: { $node }.
core-validation-missing-type-requirements = The compiler needs a Core child's type-scope requirements before they are available.
core-validation-missing-type-requirements-node = { core-validation-missing-type-requirements } Core node: { $node }.
core-validation-unresolved-core-row = The compiler retained an unresolved inference tail in a Core effect row.
core-validation-unresolved-core-row-node = { core-validation-unresolved-core-row } Core node: { $node }.
core-validation-unknown-core-row-binder = The compiler retained a Core effect-row tail without a declared binder kind.
core-validation-unknown-core-row-binder-node = { core-validation-unknown-core-row-binder } Core node: { $node }.
core-validation-non-row-tail-kind = The compiler retained a Core effect-row tail whose binder is not of kind EffectRow.
core-validation-non-row-tail-kind-node = { core-validation-non-row-tail-kind } Core node: { $node }.
kind-resources = The compiler ran out of resources while checking type kinds.
resolve-type-resources = The compiler ran out of resources while resolving types.
resolve-constraint-resources = The compiler ran out of resources while resolving interfaces and constraints.
kind-internal-missing-effect = The compiler has no canonical registry entry for a local effect.
kind-internal-duplicate-effect = The compiler retained a duplicate identity in the checked effect registry.
kind-internal-nested-effect-row = The compiler retained EffectRow beneath a kind arrow, where it is not admitted.
kind-internal-duplicate-binder = The compiler retained a duplicate type-variable identity in an owner's binder list.
kind-internal-owner-effect-row = The compiler retained an EffectRow parameter for an owner that cannot bind one.
kind-internal-missing-owner-binder = The compiler has no canonical registry entry for a linked owner binder.
kind-internal-implementation-binder-count = The compiler retained different binder counts in the source and checked implementation head.
kind-internal-implementation-binder-identity = The compiler retained different binder identities in the source and checked implementation head.
kind-internal-scheme-binder-count = The compiler retained different binder counts in a linked source scheme and its checked scheme.
kind-internal-scheme-binder-identity = The compiler retained different binder identities in a linked source scheme and its checked scheme.
kind-internal-retained-binder-kind = The compiler retained a binder kind that disagrees with its canonical registry entry.
kind-internal-unused-implementation-binder = The compiler retained an unused rigid binder in a linked implementation head.
kind-internal-unused-scheme-binder = The compiler retained an unused owner binder in a linked value scheme.
kind-internal-invalid-dependent-allowance = The compiler retained an invalid allowance for dependent-only binders in a linked global definition.
kind-internal-linked-value-type = The compiler retained a linked source type that disagrees with its checked value type.
kind-internal-linked-computation-row = The compiler retained a source computation row that disagrees with its checked row.
kind-internal-duplicate-constructor-mirror = The compiler retained two mirrors for one linked constructor domain.
kind-internal-missing-nominal-kind = The compiler has no canonical kind for a nominal type.
kind-internal-duplicate-nominal-kind = The compiler registered more than one canonical kind for a nominal type.
kind-internal-missing-inference-kind = The compiler has no fixed kind for an inference variable.
kind-internal-duplicate-inference-kind = The compiler registered more than one fixed kind for an inference variable.
kind-internal-missing-interface-parameters = The compiler has no canonical parameter records for an interface.
kind-internal-interface-parameter-count = The compiler retained conflicting canonical parameter counts for an interface.
kind-internal-interface-parameter-records = The compiler retained conflicting canonical parameter records for an interface.
kind-internal-invalid-type-provenance = The compiler retained invalid source provenance for a resolved type.
kind-internal-type-provenance-owner = The compiler paired a resolved type with source provenance belonging to a different owner.
kind-internal-atomic-type-provenance = The compiler attached composite-type provenance to an atomic resolved type.
kind-internal-application-provenance = The compiler paired a resolved type application with provenance for a different type form.
kind-internal-function-provenance = The compiler paired a resolved function type with provenance for a different type form.
kind-internal-tuple-provenance = The compiler paired a resolved tuple type with provenance for a different type form.
kind-internal-incomplete-tuple-provenance = The compiler retained incomplete source provenance for a resolved tuple type.
kind-internal-tuple-child-provenance = The compiler retained incomplete element provenance for a resolved tuple type.
kind-internal-effect-type-provenance-owner = The compiler paired an effect-bearing type with provenance belonging to a different owner.
kind-internal-effect-type-provenance-shape = The compiler paired an effect-bearing type with provenance for a different type structure.
kind-internal-effect-tuple-provenance = The compiler retained provenance that does not match the elements of an effect-bearing tuple type.
kind-internal-effect-function-provenance = The compiler retained incomplete provenance for an effectful function type.
kind-internal-pure-computation-provenance = The compiler retained effect-argument provenance for a pure computation.
kind-internal-computation-missing-arguments = The compiler retained a computation row with a missing or invalid effect-argument provenance record.
kind-internal-computation-surplus-arguments = The compiler retained surplus effect-argument provenance records for a computation row.
kind-internal-row-missing-arguments = The compiler retained too few argument provenance records for an effect row.
kind-internal-row-surplus-arguments = The compiler retained surplus argument provenance records for an effect row.
kind-internal-hook-argument-source = The compiler retained a hook argument without its source occurrence.
kind-internal-hook-argument-provenance = The compiler retained different numbers of hook arguments and argument provenance records.
kind-internal-hook-missing-effect = The compiler has no canonical effect declaration for a hook target.
kind-internal-constructor-moved-provenance = The compiler retained constructor payload provenance that disagrees with the moved payload.
kind-internal-constructor-owner = The compiler retained a canonical constructor owned by a different nominal type.
kind-internal-payload-cardinality = The compiler retained the wrong number of outer provenance records for a constructor payload.
kind-internal-payload-identity = The compiler paired constructor payload provenance with the wrong constructor identity.
kind-internal-nominal-payload-provenance = The compiler retained different numbers of nominal constructors and payload provenance records.
kind-internal-newtype-payload = The compiler retained an ordinary constructor payload for a newtype constructor.
kind-internal-newtype-constructor-count = The compiler retained a newtype without exactly one constructor identity.
kind-internal-newtype-representation-count = The compiler retained a newtype without exactly one representation provenance record.
kind-internal-newtype-representation = The compiler failed to retain a newtype's canonical representation.
kind-internal-newtype-field-provenance = The compiler retained a newtype representation without exactly one field provenance record.
kind-internal-lexical-nominal = The compiler retained a lexical nominal record that is not a lexical newtype.
kind-internal-lexical-newtype-constructor = The compiler retained a lexical newtype constructor with invalid ownership or an ordinary payload.
kind-internal-lexical-newtype-count = The compiler retained a lexical newtype without exactly one constructor identity.
kind-internal-lexical-newtype-representation = The compiler failed to retain a lexical newtype's canonical representation.
kind-internal-lexical-newtype-provenance = The compiler failed to retain representation provenance for a lexical newtype.
kind-internal-imported-nominal-parameters = The compiler retained an imported nominal type whose parameter records disagree with its parameter count.
kind-internal-payload-scheme-function = The compiler retained a payload constructor scheme without an outer function type.
kind-internal-declaration-order = The compiler retained duplicate or out-of-order declaration indices.
kind-internal-declaration-coverage = The compiler's declaration order omits local declarations.
kind-internal-kind-preflight-global = The compiler encountered an invalid global-definition index during interface-application kind preflight.
kind-internal-kind-preflight-implementation = The compiler encountered an invalid implementation index during interface-application kind preflight.
kind-internal-preflight-global = The compiler encountered an invalid global-definition index during interface-application preflight.
kind-internal-preflight-implementation = The compiler encountered an invalid implementation index during interface-application preflight.
kind-internal-missing-canonical-binder = The compiler has no canonical kind for a type binder.
kind-internal-conflicting-declaration-binder = The compiler retained a declaration binder that conflicts with its canonical registry record.
kind-internal-missing-declaration-binder = The compiler has no canonical registry record for a declaration binder.
kind-internal-scheme-in-determination = The compiler passed a polymorphic scheme to global determination discovery, which requires a monotype.
kind-internal-scheme-in-monotype = The compiler passed a polymorphic scheme to resolved monotype kind checking.
kind-internal-empty-method-binders = The compiler retained an empty explicit method binder list.
kind-internal-missing-interface-kind = The compiler has no canonical interface-kind entry for a resolved interface application.
kind-internal-empty-interface-parameters = The compiler retained a resolved interface without type parameters.
kind-internal-missing-variable-kind = The compiler has no canonical kind for a resolved type variable.
kind-internal-resource-identity-kind = The compiler retained a resource identity whose kind is not Type.
kind-internal-determinant-position = The compiler retained a determinant position outside its complete interface application.
kind-internal-source-determination-key = The compiler retained an invalid determination key in authenticated source data.
kind-internal-summary-determination-key = The compiler retained an invalid determination key in an authenticated summary.
kind-internal-effect-argument-kind = The compiler retained an effect-row argument with the wrong canonical kind.
kind-internal-effect-argument-count = The compiler retained an effect-row instance with the wrong canonical argument count.
kind-internal-missing-row-effect = The compiler retained an effect row referring to an effect without a canonical checked declaration.
kind-internal-non-owner-row-tail = The compiler retained an effect-row tail that is not bound by its owner.
kind-internal-row-tail-kind = The compiler retained an effect-row tail whose kind is not EffectRow.
kind-internal-missing-row-binder-kind = The compiler has no canonical binder kind for an effect-row tail.
kind-internal-missing-row-inference-kind = The compiler has no fixed inference kind for an effect-row tail.
kind-internal-implementation-row-binder = The compiler retained an EffectRow parameter on an implementation owner that cannot bind one.
kind-internal-preflight-arity-changed = The compiler observed different interface-application argument counts between kind preflight passes.
kind-internal-method-row-binder = The compiler retained an EffectRow parameter on an interface method that cannot bind one.
kind-internal-row-inference-determination = The compiler encountered row inference during global determination discovery.
kind-internal-body-free-constructor-owner = The compiler retained a constructor scheme referring to a variable outside its owner parameters.
kind-internal-body-free-interface-kind = The compiler has no canonical parameter kinds for an interface occurrence checked without a body.
kind-internal-body-free-constructor-kind = The compiler retained a checked constructor scheme whose resulting kind is not Type.
kind-internal-body-free-function-kind = The compiler retained a function-type component with the wrong kind during body-free checking.
kind-internal-body-free-interface-arity = The compiler retained an interface application with the wrong argument count during body-free checking.
kind-internal-body-free-interface-argument = The compiler retained an interface argument with the wrong kind during body-free checking.
kind-internal-body-free-determinant-seed = The compiler retained an empty or all-parameter determinant seed for a checked interface.
kind-internal-body-free-method-kind = The compiler retained a checked interface method whose resulting kind is not Type.
kind-internal-body-free-required-seed = The compiler retained a checked interface method with an empty required-parameter seed.
kind-internal-body-free-method-function = The compiler retained a checked interface method without a function type.
kind-internal-body-free-missing-parameter = The compiler retained a checked interface method that omits a required parameter.
kind-internal-body-free-method-duplicate-parameter = The compiler retained a duplicate type parameter in a checked interface method.
kind-internal-body-free-interface-duplicate-parameter = The compiler retained a duplicate type parameter in a checked interface.
kind-internal-body-free-seed-order = The compiler retained an interface parameter seed that is not a unique subset in declaration order.
kind-internal-body-free-monotype-kind = The compiler retained a checked monotype with the wrong canonical kind.
kind-internal-body-free-tuple-kind = The compiler retained a tuple element with the wrong kind during body-free checking.
kind-internal-body-free-application-argument = The compiler retained a type application with the wrong argument kind during body-free checking.
kind-internal-body-free-non-function-kind = The compiler retained a type application whose operator does not have a function kind.
kind-internal-body-free-value-kind = The compiler retained a checked value scheme whose resulting kind is not Type.
kind-internal-body-free-source-diagnostic = The compiler tried to retain a source diagnostic while checking kinds without source bodies.
kind-internal-lookup-lexical-constructor = The compiler retained a lexical newtype referring to a missing canonical constructor.
kind-internal-lookup-lexical-parameters = The compiler has no canonical parameter records for a lexical nominal type.
kind-internal-lookup-lexical-nominal = The compiler retained a lexical nominal marker referring to a missing canonical record.
kind-internal-lookup-nominal-parameters = The compiler has no canonical parameter records for a local nominal type.
kind-internal-lookup-newtype-constructor = The compiler retained a newtype referring to a missing canonical constructor.
kind-internal-lookup-payload-provenance = The compiler has no declaration-ordered payload provenance for a nominal type.
kind-internal-lookup-nominal-constructor = The compiler retained a nominal type referring to a missing canonical constructor.
kind-internal-lookup-effect-index = The compiler's declaration order contains an invalid effect index.
kind-internal-lookup-global-index = The compiler's declaration order contains an invalid global-definition index.
kind-internal-lookup-implementation-index = The compiler's declaration order contains an invalid implementation index.
kind-internal-lookup-interface-index = The compiler's declaration order contains an invalid interface index.
kind-internal-lookup-nominal-index = The compiler's declaration order contains an invalid nominal-type index.
evidence-kind-use = Kind validation failed while checking evidence at this use.
elaboration-kind-use = Kind validation failed while checking this expression or declaration.
resolve-kind-use = Kind validation failed while checking imported information at this location.
core-validation-conversion-unknown-owner = The compiler retained a newtype conversion whose owner is absent from the registry.
core-validation-conversion-unknown-owner-node = { core-validation-conversion-unknown-owner } Core node: { $node }.
core-validation-conversion-ordinary-owner = The compiler used an ordinary nominal type as the owner of a newtype conversion.
core-validation-conversion-ordinary-owner-node = { core-validation-conversion-ordinary-owner } Core node: { $node }.
core-validation-conversion-missing-representation = The compiler retained a newtype conversion whose owner has no representation type.
core-validation-conversion-missing-representation-node = { core-validation-conversion-missing-representation } Core node: { $node }.
core-validation-conversion-missing-parameters = The compiler retained a newtype conversion without its owner's parameter declaration.
core-validation-conversion-missing-parameters-node = { core-validation-conversion-missing-parameters } Core node: { $node }.
core-validation-conversion-excess-arguments = The compiler applied more type arguments than the newtype conversion's owner declares.
core-validation-conversion-excess-arguments-node = { core-validation-conversion-excess-arguments } Core node: { $node }.
core-validation-conversion-nominal-owner = The nominal side of a compiler-retained newtype conversion does not name its declared owner.
core-validation-conversion-nominal-owner-node = { core-validation-conversion-nominal-owner } Core node: { $node }.
core-validation-conversion-missing-arguments = The compiler applied fewer type arguments than the newtype conversion's owner declares.
core-validation-conversion-missing-arguments-node = { core-validation-conversion-missing-arguments } Core node: { $node }.
core-validation-conversion-invalid-argument = The compiler retained a newtype conversion with a type argument that has no valid monotype kind.
core-validation-conversion-invalid-argument-node = { core-validation-conversion-invalid-argument } Core node: { $node }.
core-validation-conversion-argument-kind = A newtype conversion's type argument has a different kind from its declared parameter.
core-validation-conversion-argument-kind-node = { core-validation-conversion-argument-kind } Core node: { $node }.
core-validation-conversion-representation-mismatch = The representation side of a compiler-retained newtype conversion differs from its instantiated representation type.
core-validation-conversion-representation-mismatch-node = { core-validation-conversion-representation-mismatch } Core node: { $node }.
core-validation-unknown-core-effect = The compiler retained an effect identity absent from the Core registry.
core-validation-unknown-core-effect-node = { core-validation-unknown-core-effect } Core node: { $node }.
core-validation-core-operation-owner = The compiler used an operation belonging to a different effect declaration.
core-validation-core-operation-owner-node = { core-validation-core-operation-owner } Core node: { $node }.
core-validation-core-effect-argument-count = The compiler retained an effect instance with a different number of type arguments from its declaration.
core-validation-core-effect-argument-count-node = { core-validation-core-effect-argument-count } Core node: { $node }.
core-validation-core-effect-invalid-argument = The compiler retained an effect type argument that has no valid monotype kind.
core-validation-core-effect-invalid-argument-node = { core-validation-core-effect-invalid-argument } Core node: { $node }.
core-validation-core-effect-argument-kind = An effect instance's type argument has a different kind from its declared parameter.
core-validation-core-effect-argument-kind-node = { core-validation-core-effect-argument-kind } Core node: { $node }.
core-validation-unknown-core-operation = The compiler retained an operation identity absent from its effect declaration.
core-validation-unknown-core-operation-node = { core-validation-unknown-core-operation } Core node: { $node }.
core-validation-core-operation-signature = The compiler retained an effect operation whose instantiated signature is not a function type.
core-validation-core-operation-signature-node = { core-validation-core-operation-signature } Core node: { $node }.
core-validation-unsupported-resource-module = The compiler retained a resource acquisition whose built-in module has no supported provider API.
core-validation-unsupported-resource-module-node = { core-validation-unsupported-resource-module } Core node: { $node }.
core-validation-resource-provider-method-count = The compiler retained a resource acquisition with a different number of methods from its provider API.
core-validation-resource-provider-method-count-node = { core-validation-resource-provider-method-count } Core node: { $node }.
core-resource-escape = The compiler retained a value that depends on a resource beyond that resource's scope.
core-resource-escape-node = { core-resource-escape } Core node: { $node }.
core-discard-unknown = The compiler retained a discard without proof that the captured continuation has no unfinished obligations.
core-discard-unknown-node = { core-discard-unknown } Core node: { $node }.
core-discard-clause = The compiler retained a discard that skips a clause with an unfinished completion obligation.
core-discard-clause-node = { core-discard-clause } Core node: { $node }.
core-discard-cleanup = The compiler retained a discard that skips a cleanup action that must complete.
core-discard-cleanup-node = { core-discard-cleanup } Core node: { $node }.
core-cleanup-context = The compiler retained a discard that removes a handler required by cleanup.
core-cleanup-context-node = { core-cleanup-context } Core node: { $node }.
core-validation-missing-tuple-kinds = The compiler's Core kind analysis has fewer tuple-element results than required.
core-validation-missing-tuple-kinds-node = { core-validation-missing-tuple-kinds } Core node: { $node }.
core-validation-missing-argument-kind = The compiler's Core kind analysis has no result for a type application's argument.
core-validation-missing-argument-kind-node = { core-validation-missing-argument-kind } Core node: { $node }.
core-validation-missing-function-kind = The compiler's Core kind analysis has no result for a type application's function.
core-validation-missing-function-kind-node = { core-validation-missing-function-kind } Core node: { $node }.
core-validation-missing-codomain-kind = The compiler's Core kind analysis has no result for a function type's codomain.
core-validation-missing-codomain-kind-node = { core-validation-missing-codomain-kind } Core node: { $node }.
core-validation-missing-domain-kind = The compiler's Core kind analysis has no result for a function type's domain.
core-validation-missing-domain-kind-node = { core-validation-missing-domain-kind } Core node: { $node }.
core-validation-core-kind-result-count = The compiler's Core kind analysis did not finish with exactly one result.
core-validation-core-kind-result-count-node = { core-validation-core-kind-result-count } Core node: { $node }.
core-validation-duplicate-generated-type-binder = The compiler declared the same generated type-variable identity in more than one Core type abstraction.
core-validation-duplicate-generated-type-binder-node = { core-validation-duplicate-generated-type-binder } Core node: { $node }.
core-validation-effect-abstraction-body = The compiler retained an effect-Core type abstraction whose body is not an inert value or type application.
core-validation-effect-abstraction-body-node = { core-validation-effect-abstraction-body } Core node: { $node }.
core-validation-expected-type-abstraction = The compiler recorded a Core type abstraction at a node of a different form.
core-validation-expected-type-abstraction-node = { core-validation-expected-type-abstraction } Core node: { $node }.
core-validation-expected-type-application = The compiler recorded a Core type application at a node of a different form.
core-validation-expected-type-application-node = { core-validation-expected-type-application } Core node: { $node }.
core-validation-adapter-parameter-identity = The compiler used a non-generated type parameter in a method adapter.
core-validation-adapter-parameter-identity-node = { core-validation-adapter-parameter-identity } Core node: { $node }.
core-validation-abstraction-binder-owner = A Core type abstraction does not own one of its recorded type parameters.
core-validation-abstraction-binder-owner-node = { core-validation-abstraction-binder-owner } Core node: { $node }.
core-validation-method-instantiation-identity = The compiler instantiated a different method from the checked method occurrence.
core-validation-method-instantiation-identity-node = { core-validation-method-instantiation-identity } Core node: { $node }.
core-validation-method-type-argument-count = The compiler retained a method instantiation with a different type-argument count from the checked occurrence.
core-validation-method-type-argument-count-node = { core-validation-method-type-argument-count } Core node: { $node }.
core-validation-method-type-argument = A Core method type argument differs from its checked argument after scope substitution.
core-validation-method-type-argument-node = { core-validation-method-type-argument } Core node: { $node }.
core-validation-method-instantiation-result = A Core method instantiation's result type differs from its checked result after scope substitution.
core-validation-method-instantiation-result-node = { core-validation-method-instantiation-result } Core node: { $node }.
core-validation-method-instantiation-role = The compiler has no instantiation-role expectation for this Core method use.
core-validation-method-instantiation-role-node = { core-validation-method-instantiation-role } Core node: { $node }.
core-validation-missing-method-producer = The compiler has no retained producer anchor for this Core method instantiation.
core-validation-missing-method-producer-node = { core-validation-missing-method-producer } Core node: { $node }.
core-validation-method-instantiation-producer = A Core method instantiation does not use its recorded producer or binder.
core-validation-method-instantiation-producer-node = { core-validation-method-instantiation-producer } Core node: { $node }.
core-validation-type-abstraction-scheme = A Core type abstraction does not carry a universally quantified type.
core-validation-type-abstraction-scheme-node = { core-validation-type-abstraction-scheme } Core node: { $node }.
core-validation-empty-type-abstraction = The compiler retained a Core type abstraction without type parameters.
core-validation-empty-type-abstraction-node = { core-validation-empty-type-abstraction } Core node: { $node }.
core-validation-abstraction-nominal-parameter = A Core type abstraction reuses a type parameter owned by a nominal declaration.
core-validation-abstraction-nominal-parameter-node = { core-validation-abstraction-nominal-parameter } Core node: { $node }.
core-validation-abstraction-parameters = A Core type abstraction's parameters differ in identity, order or kind from its quantified type.
core-validation-abstraction-parameters-node = { core-validation-abstraction-parameters } Core node: { $node }.
core-validation-abstraction-body-type = A Core type abstraction's body type differs from the body of its quantified type.
core-validation-abstraction-body-type-node = { core-validation-abstraction-body-type } Core node: { $node }.
core-validation-nested-type-abstraction = The compiler retained nested type quantification without method-evidence authentication.
core-validation-nested-type-abstraction-node = { core-validation-nested-type-abstraction } Core node: { $node }.
core-validation-abstraction-type-kind = A Core type abstraction's quantified type is not well-kinded.
core-validation-abstraction-type-kind-node = { core-validation-abstraction-type-kind } Core node: { $node }.
core-validation-type-application-scheme = The compiler applied type arguments to a Core expression without a quantified type.
core-validation-type-application-scheme-node = { core-validation-type-application-scheme } Core node: { $node }.
core-validation-type-application-arity = A Core type application supplies a different number of arguments from its quantified parameters.
core-validation-type-application-arity-node = { core-validation-type-application-arity } Core node: { $node }.
core-validation-type-application-rows = The compiler retained effect-row arguments in a Core dialect that does not permit them.
core-validation-type-application-rows-node = { core-validation-type-application-rows } Core node: { $node }.
core-validation-missing-row-argument = A Core type application has no row argument for an EffectRow parameter.
core-validation-missing-row-argument-node = { core-validation-missing-row-argument } Core node: { $node }.
core-validation-missing-type-argument = A Core type application has no ordinary type argument for its next parameter.
core-validation-missing-type-argument-node = { core-validation-missing-type-argument } Core node: { $node }.
core-validation-type-argument-invalid = A Core type application's argument has no valid monotype kind.
core-validation-type-argument-invalid-node = { core-validation-type-argument-invalid } Core node: { $node }.
core-validation-type-argument-kind = A Core type application's argument kind differs from its parameter kind.
core-validation-type-argument-kind-node = { core-validation-type-argument-kind } Core node: { $node }.
core-validation-type-substitution-ambiguous = Core type application would strengthen or equate unrelated open effect-row tails.
core-validation-type-substitution-ambiguous-node = { core-validation-type-substitution-ambiguous } Core node: { $node }.
core-validation-type-substitution-missing = Core type application tried to remove an effect instance absent from the substituted row.
core-validation-type-substitution-missing-node = { core-validation-type-substitution-missing } Core node: { $node }.
core-validation-type-substitution-infinite = Core type application would make an effect-row tail contain itself.
core-validation-type-substitution-infinite-node = { core-validation-type-substitution-infinite } Core node: { $node }.
core-validation-type-application-result = A Core type application's recorded result differs from the instantiated type.
core-validation-type-application-result-node = { core-validation-type-application-result } Core node: { $node }.
core-validation-pattern-depth = The compiler retained a Core pattern deeper than the validation limit.
core-validation-pattern-depth-node = { core-validation-pattern-depth } Core node: { $node }.
core-validation-pattern-type-mismatch = A Core pattern's recorded type differs from the type it must match.
core-validation-pattern-type-mismatch-node = { core-validation-pattern-type-mismatch } Core node: { $node }.
core-validation-pattern-invalid-type = The compiler retained a Core pattern without a valid monotype.
core-validation-pattern-invalid-type-node = { core-validation-pattern-invalid-type } Core node: { $node }.
core-validation-pattern-binder-invalid-type = The compiler retained a pattern or operation binder without a valid monotype.
core-validation-pattern-binder-invalid-type-node = { core-validation-pattern-binder-invalid-type } Core node: { $node }.
core-validation-pattern-binder-arena = A Core pattern binder belongs to a different arena.
core-validation-pattern-binder-arena-node = { core-validation-pattern-binder-arena } Core node: { $node }.
core-validation-pattern-binder-type = A Core pattern binder's type differs from the type it must match.
core-validation-pattern-binder-type-node = { core-validation-pattern-binder-type } Core node: { $node }.
core-validation-pattern-duplicate-binder = The compiler bound the same identity more than once in a Core pattern.
core-validation-pattern-duplicate-binder-node = { core-validation-pattern-duplicate-binder } Core node: { $node }.
core-validation-pattern-tuple-type = The compiler used a tuple pattern to match a non-tuple type.
core-validation-pattern-tuple-type-node = { core-validation-pattern-tuple-type } Core node: { $node }.
core-validation-pattern-tuple-arity = A Core tuple pattern has a different number of elements from its expected type.
core-validation-pattern-tuple-arity-node = { core-validation-pattern-tuple-arity } Core node: { $node }.
core-validation-pattern-hidden-constructor = The compiler exposed a hidden resource constructor in a Core pattern.
core-validation-pattern-hidden-constructor-node = { core-validation-pattern-hidden-constructor } Core node: { $node }.
core-validation-pattern-nominal-type = The compiler used a constructor pattern to match a type without a nominal head.
core-validation-pattern-nominal-type-node = { core-validation-pattern-nominal-type } Core node: { $node }.
core-validation-pattern-unknown-constructor = A Core pattern names a constructor absent from the registry.
core-validation-pattern-unknown-constructor-node = { core-validation-pattern-unknown-constructor } Core node: { $node }.
core-validation-pattern-newtype-constructor = The compiler retained a newtype constructor in an ordinary Core constructor pattern.
core-validation-pattern-newtype-constructor-node = { core-validation-pattern-newtype-constructor } Core node: { $node }.
core-validation-pattern-constructor-owner = A Core pattern's constructor belongs to a different nominal type from the expected type.
core-validation-pattern-constructor-owner-node = { core-validation-pattern-constructor-owner } Core node: { $node }.
core-validation-pattern-missing-parameters = The compiler has no nominal parameter declaration for a Core constructor pattern's expected type.
core-validation-pattern-missing-parameters-node = { core-validation-pattern-missing-parameters } Core node: { $node }.
core-validation-pattern-nominal-arity = A Core constructor pattern's expected type has a different argument count from its nominal declaration.
core-validation-pattern-nominal-arity-node = { core-validation-pattern-nominal-arity } Core node: { $node }.
core-validation-pattern-argument-spine = The compiler could not read a recorded nominal type argument while instantiating a pattern payload.
core-validation-pattern-argument-spine-node = { core-validation-pattern-argument-spine } Core node: { $node }.
core-validation-pattern-missing-payload = A Core constructor pattern omits a payload required by its constructor.
core-validation-pattern-missing-payload-node = { core-validation-pattern-missing-payload } Core node: { $node }.
core-validation-pattern-unexpected-payload = A Core constructor pattern supplies a payload for a constructor that has none.
core-validation-pattern-unexpected-payload-node = { core-validation-pattern-unexpected-payload } Core node: { $node }.
core-validation-pattern-boolean-type = The compiler used a Boolean pattern to match a non-Boolean type.
core-validation-pattern-boolean-type-node = { core-validation-pattern-boolean-type } Core node: { $node }.
core-validation-pattern-unit-type = The compiler used a Unit pattern to match a type other than Unit.
core-validation-pattern-unit-type-node = { core-validation-pattern-unit-type } Core node: { $node }.
core-validation-match-scrutinee-type = The compiler retained a Core match whose scrutinee has no valid monotype.
core-validation-match-scrutinee-type-node = { core-validation-match-scrutinee-type } Core node: { $node }.
core-validation-unbound-continuation = The compiler retained a continuation use without its enclosing operation clause.
core-validation-unbound-continuation-node = { core-validation-unbound-continuation } Core node: { $node }.
core-validation-continuation-branch-usage = Core match branches disagree about which continuations they consume or how many times they consume them.
core-validation-continuation-branch-usage-node = { core-validation-continuation-branch-usage } Core node: { $node }.
core-validation-missing-clause-consumption = A Core operation clause does not consume its continuation.
core-validation-missing-clause-consumption-node = { core-validation-missing-clause-consumption } Core node: { $node }.
core-validation-repeated-clause-consumption = A Core operation clause does not consume its continuation exactly once.
core-validation-repeated-clause-consumption-node = { core-validation-repeated-clause-consumption } Core node: { $node }.
core-validation-foreign-clause-continuation = A Core operation clause retains a use of another clause's continuation.
core-validation-foreign-clause-continuation-node = { core-validation-foreign-clause-continuation } Core node: { $node }.
core-validation-captured-continuation = The compiler retained a continuation requirement across a boundary that forbids continuation capture.
core-validation-captured-continuation-node = { core-validation-captured-continuation } Core node: { $node }.
core-validation-resume-use-state = The compiler retained a resume operation without a consumed-continuation state.
core-validation-resume-use-state-node = { core-validation-resume-use-state } Core node: { $node }.
core-validation-discard-use-state = The compiler retained a discard operation without a consumed-continuation state.
core-validation-discard-use-state-node = { core-validation-discard-use-state } Core node: { $node }.
core-validation-discard-result-type = A Core discard operation has a result type other than Unit.
core-validation-discard-result-type-node = { core-validation-discard-result-type } Core node: { $node }.
core-validation-discard-missing-contract = The compiler has no operation-clause contract for a Core discard's handler and continuation owner.
core-validation-discard-missing-contract-node = { core-validation-discard-missing-contract } Core node: { $node }.
core-validation-resume-missing-contract = The compiler has no operation-clause contract for a Core resume's handler and continuation owner.
core-validation-resume-missing-contract-node = { core-validation-resume-missing-contract } Core node: { $node }.
core-validation-resume-handler-shape = A Core continuation contract points to a node that is not a handler.
core-validation-resume-handler-shape-node = { core-validation-resume-handler-shape } Core node: { $node }.
core-validation-resume-missing-clause = A Core continuation contract points to a clause absent from its handler.
core-validation-resume-missing-clause-node = { core-validation-resume-missing-clause } Core node: { $node }.
core-validation-resume-argument-type = A Core resume argument's type differs from the operation's result type.
core-validation-resume-argument-type-node = { core-validation-resume-argument-type } Core node: { $node }.
core-validation-resume-result-type = A Core resume's result type differs from its handler's result type.
core-validation-resume-result-type-node = { core-validation-resume-result-type } Core node: { $node }.
core-validation-resume-effect-row = A Core resume's effect row differs from the union of its argument and handler output rows.
core-validation-resume-effect-row-node = { core-validation-resume-effect-row } Core node: { $node }.
core-validation-resume-argument-effects = A Core resume argument has effects outside the resume node's row.
core-validation-resume-argument-effects-node = { core-validation-resume-argument-effects } Core node: { $node }.
core-cleanup-effect-row = The compiler retained a discard whose effect row does not match its cleanup obligations.
core-cleanup-effect-row-node = { core-cleanup-effect-row } Core node: { $node }.
core-validation-row-union-ambiguous = Core effect-row union would strengthen or equate unrelated open tails.
core-validation-row-union-ambiguous-node = { core-validation-row-union-ambiguous } Core node: { $node }.
core-validation-row-union-missing = Core effect-row union requires an effect instance that is absent.
core-validation-row-union-missing-node = { core-validation-row-union-missing } Core node: { $node }.
core-validation-row-union-infinite = Core effect-row union would make a row tail contain itself.
core-validation-row-union-infinite-node = { core-validation-row-union-infinite } Core node: { $node }.
core-validation-row-removal-ambiguous = Core effect removal cannot establish the required relation with an open row tail.
core-validation-row-removal-ambiguous-node = { core-validation-row-removal-ambiguous } Core node: { $node }.
core-validation-row-removal-missing = The compiler tried to remove an effect instance absent from a Core row.
core-validation-row-removal-missing-node = { core-validation-row-removal-missing } Core node: { $node }.
core-validation-row-removal-infinite = Core effect removal would make a row tail contain itself.
core-validation-row-removal-infinite-node = { core-validation-row-removal-infinite } Core node: { $node }.
core-validation-pure-dialect-row = The compiler retained effects in a Core dialect that requires empty rows.
core-validation-pure-dialect-row-node = { core-validation-pure-dialect-row } Core node: { $node }.
core-validation-resource-scope-row = A Core resource scope's effects differ from its initializer and outward body effects.
core-validation-resource-scope-row-node = { core-validation-resource-scope-row } Core node: { $node }.
core-validation-request-argument-type = A Core effect request's operand type differs from its operation's domain.
core-validation-request-argument-type-node = { core-validation-request-argument-type } Core node: { $node }.
core-validation-request-result-type = A Core effect request's result type differs from its operation's result type.
core-validation-request-result-type-node = { core-validation-request-result-type } Core node: { $node }.
core-validation-request-effect-row = A Core effect request's row differs from the union of its operand effects and requested effect.
core-validation-request-effect-row-node = { core-validation-request-effect-row } Core node: { $node }.
core-validation-linked-root-effects = The compiler retained unhandled effects at the linked Core program's root.
core-validation-linked-root-effects-node = { core-validation-linked-root-effects } Core node: { $node }.
core-validation-row-owner-inference = The compiler tried to authenticate row exclusions using an unresolved inference tail.
core-validation-row-owner-inference-node = { core-validation-row-owner-inference } Core node: { $node }.
core-validation-missing-row-owner = The compiler has no type-binder owner for a row exclusion check.
core-validation-missing-row-owner-node = { core-validation-missing-row-owner } Core node: { $node }.
core-validation-row-owner-kind = The compiler used a binder of a kind other than EffectRow to authenticate row exclusions.
core-validation-row-owner-kind-node = { core-validation-row-owner-kind } Core node: { $node }.
core-validation-row-owner-scheme = The owner of a Core row tail has no quantified type from which to authenticate exclusions.
core-validation-row-owner-scheme-node = { core-validation-row-owner-scheme } Core node: { $node }.
core-validation-unproved-row-lacks = A Core row reports an effect exclusion not established by its binder's contract.
core-validation-unproved-row-lacks-node = { core-validation-unproved-row-lacks } Core node: { $node }.
core-validation-pure-node-effect-row = A Core node's recorded effects differ from its evaluated children and latent function effects.
core-validation-pure-node-effect-row-node = { core-validation-pure-node-effect-row } Core node: { $node }.
core-validation-missing-child-row = The compiler needs a child's inferred handler-output row before it is available.
core-validation-missing-child-row-node = { core-validation-missing-child-row } Core node: { $node }.
core-validation-missing-row-slot = The compiler has no result slot for a node's inferred handler-output row.
core-validation-missing-row-slot-node = { core-validation-missing-row-slot } Core node: { $node }.
core-validation-missing-root-row = The compiler has no inferred output row for the handler root.
core-validation-missing-root-row-node = { core-validation-missing-root-row } Core node: { $node }.
core-validation-handler-body-type = A Core handler's body type differs from its result type.
core-validation-handler-body-type-node = { core-validation-handler-body-type } Core node: { $node }.
core-validation-handler-body-effects = A Core handler's body has outward effects absent from the handler's output row.
core-validation-handler-body-effects-node = { core-validation-handler-body-effects } Core node: { $node }.
core-validation-handler-output-row = A Core handler's recorded output row differs from its least inferred output row.
core-validation-handler-output-row-node = { core-validation-handler-output-row } Core node: { $node }.
core-validation-cleanup-action-shape = The compiler retained a cleanup action that is not a callback application.
core-validation-cleanup-action-shape-node = { core-validation-cleanup-action-shape } Core node: { $node }.
core-validation-cleanup-function-shape = A Core cleanup action does not refer to its callback through a variable.
core-validation-cleanup-function-shape-node = { core-validation-cleanup-function-shape } Core node: { $node }.
core-validation-cleanup-function-type = A Core cleanup callback does not have a function type.
core-validation-cleanup-function-type-node = { core-validation-cleanup-function-type } Core node: { $node }.
core-validation-cleanup-callback-identity = A Core cleanup action refers to a different callback from its scope's recorded callback.
core-validation-cleanup-callback-identity-node = { core-validation-cleanup-callback-identity } Core node: { $node }.
core-validation-cleanup-argument-shape = A Core cleanup action does not supply the Unit value to its callback.
core-validation-cleanup-argument-shape-node = { core-validation-cleanup-argument-shape } Core node: { $node }.
core-validation-cleanup-domain-type = A Core cleanup callback's domain is not Unit.
core-validation-cleanup-domain-type-node = { core-validation-cleanup-domain-type } Core node: { $node }.
core-validation-cleanup-result-type = A Core cleanup callback's result type is not Unit.
core-validation-cleanup-result-type-node = { core-validation-cleanup-result-type } Core node: { $node }.
core-validation-cleanup-body-type = A Core cleanup scope's result type differs from its body's type.
core-validation-cleanup-body-type-node = { core-validation-cleanup-body-type } Core node: { $node }.
core-validation-cleanup-scope-effects = A Core cleanup scope's effects differ from its body and cleanup action effects.
core-validation-cleanup-scope-effects-node = { core-validation-cleanup-scope-effects } Core node: { $node }.
core-validation-cleanup-scope-origin = A Core cleanup scope's source origin differs from its recorded scope span.
core-validation-cleanup-scope-origin-node = { core-validation-cleanup-scope-origin } Core node: { $node }.
core-validation-cleanup-action-origin = A Core cleanup action or its callback/argument has an origin different from the recorded action span.
core-validation-cleanup-action-origin-node = { core-validation-cleanup-action-origin } Core node: { $node }.
core-validation-registration-handler-shape = A Core registration scope's body is not a handler.
core-validation-registration-handler-shape-node = { core-validation-registration-handler-shape } Core node: { $node }.
core-validation-registration-missing-contract = A Core registration scope's handler has no registration contract.
core-validation-registration-missing-contract-node = { core-validation-registration-missing-contract } Core node: { $node }.
core-validation-registration-has-root = The compiler used a hook-root handler as a registration handler.
core-validation-registration-has-root-node = { core-validation-registration-has-root } Core node: { $node }.
core-validation-registration-handler-identity = A Core registration scope records a different handler identity from its body.
core-validation-registration-handler-identity-node = { core-validation-registration-handler-identity } Core node: { $node }.
core-validation-registration-callback-identity = A Core registration scope and its handler contract name different callbacks.
core-validation-registration-callback-identity-node = { core-validation-registration-callback-identity } Core node: { $node }.
core-validation-registration-contract-span = A Core registration scope and its handler contract retain different scope spans.
core-validation-registration-contract-span-node = { core-validation-registration-contract-span } Core node: { $node }.
core-validation-registration-scope-origin = A Core registration scope's origin differs from its recorded span.
core-validation-registration-scope-origin-node = { core-validation-registration-scope-origin } Core node: { $node }.
core-validation-registration-result-type = A Core registration scope's result type differs from its handler's result type.
core-validation-registration-result-type-node = { core-validation-registration-result-type } Core node: { $node }.
core-validation-registration-scope-effects = A Core registration scope's effects differ from its handler's effects.
core-validation-registration-scope-effects-node = { core-validation-registration-scope-effects } Core node: { $node }.
core-validation-duplicate-handler-identity = The compiler declared the same Core handler identity more than once.
core-validation-duplicate-handler-identity-node = { core-validation-duplicate-handler-identity } Core node: { $node }.
core-validation-handler-argument-count = A Core handler supplies a different number of effect arguments from its declaration.
core-validation-handler-argument-count-node = { core-validation-handler-argument-count } Core node: { $node }.
core-validation-handler-clause-count = A Core handler has a different number of clauses from its effect's operations.
core-validation-handler-clause-count-node = { core-validation-handler-clause-count } Core node: { $node }.
core-validation-duplicate-clause-continuation = The compiler assigned the same continuation owner to more than one clause of a Core handler.
core-validation-duplicate-clause-continuation-node = { core-validation-duplicate-clause-continuation } Core node: { $node }.
core-validation-handler-operation-range = A Core handler operation's ordinal cannot be represented as an index.
core-validation-handler-operation-range-node = { core-validation-handler-operation-range } Core node: { $node }.
core-validation-handler-operation-slot = A Core handler clause refers to an operation outside its coverage table.
core-validation-handler-operation-slot-node = { core-validation-handler-operation-slot } Core node: { $node }.
core-validation-duplicate-handler-operation = A Core handler contains more than one clause for the same operation.
core-validation-duplicate-handler-operation-node = { core-validation-duplicate-handler-operation } Core node: { $node }.
core-validation-handler-clause-coverage = A Core handler clause's pattern does not cover every operation argument.
core-validation-handler-clause-coverage-node = { core-validation-handler-clause-coverage } Core node: { $node }.
core-validation-handler-clause-type = A Core handler clause's body type differs from the handler's result type.
core-validation-handler-clause-type-node = { core-validation-handler-clause-type } Core node: { $node }.
core-validation-handler-clause-effects = A Core handler clause has effects absent from the handler's output row.
core-validation-handler-clause-effects-node = { core-validation-handler-clause-effects } Core node: { $node }.
core-validation-callback-scope-missing-parent = A Core callback scope or registration handler has no enclosing owner.
core-validation-callback-scope-missing-parent-node = { core-validation-callback-scope-missing-parent } Core node: { $node }.
core-validation-callback-scope-binding-shape = A Core callback scope is not enclosed by its callback binding.
core-validation-callback-scope-binding-shape-node = { core-validation-callback-scope-binding-shape } Core node: { $node }.
core-validation-callback-scope-parent-count = A Core callback scope or registration handler does not have exactly one incoming ownership edge.
core-validation-callback-scope-parent-count-node = { core-validation-callback-scope-parent-count } Core node: { $node }.
core-validation-callback-scope-binding-body = A Core callback scope is not the body of its enclosing binding.
core-validation-callback-scope-binding-body-node = { core-validation-callback-scope-binding-body } Core node: { $node }.
core-validation-callback-scope-binding-identity = A Core callback scope names a different callback from its enclosing binding.
core-validation-callback-scope-binding-identity-node = { core-validation-callback-scope-binding-identity } Core node: { $node }.
core-validation-cleanup-binding-origin = A Core cleanup callback binding's origin differs from the recorded cleanup-action span.
core-validation-cleanup-binding-origin-node = { core-validation-cleanup-binding-origin } Core node: { $node }.
core-validation-cleanup-action-index = A Core cleanup action's node identity cannot be represented as an index.
core-validation-cleanup-action-index-node = { core-validation-cleanup-action-index } Core node: { $node }.
core-validation-cleanup-action-parent-count = A Core cleanup action does not have exactly one incoming ownership edge.
core-validation-cleanup-action-parent-count-node = { core-validation-cleanup-action-parent-count } Core node: { $node }.
core-validation-registered-handler-parent-shape = A Core registration handler is not enclosed by a registration scope.
core-validation-registered-handler-parent-shape-node = { core-validation-registered-handler-parent-shape } Core node: { $node }.
core-validation-registered-handler-parent-body = A Core registration handler is not the body recorded by its enclosing registration scope.
core-validation-registered-handler-parent-body-node = { core-validation-registered-handler-parent-body } Core node: { $node }.
core-validation-hook-operation-count = A Core hook contract requires an effect declaration with exactly one operation.
core-validation-hook-operation-count-node = { core-validation-hook-operation-count } Core node: { $node }.
core-validation-hook-operation-type = A Core hook contract's operation has no function signature.
core-validation-hook-operation-type-node = { core-validation-hook-operation-type } Core node: { $node }.
core-validation-hook-clause-count = A Core hook contract requires exactly one handler clause.
core-validation-hook-clause-count-node = { core-validation-hook-clause-count } Core node: { $node }.
core-validation-hook-input-pattern = A Core hook clause does not bind its input with a binder pattern.
core-validation-hook-input-pattern-node = { core-validation-hook-input-pattern } Core node: { $node }.
core-validation-hook-root-resume-shape = A Core hook-root clause does not directly resume its continuation.
core-validation-hook-root-resume-shape-node = { core-validation-hook-root-resume-shape } Core node: { $node }.
core-validation-hook-root-value-shape = A Core hook root does not resume with a variable referring to its input.
core-validation-hook-root-value-shape-node = { core-validation-hook-root-value-shape } Core node: { $node }.
core-validation-hook-target-instance = A Core hook contract targets a different effect instance from its handler.
core-validation-hook-target-instance-node = { core-validation-hook-target-instance } Core node: { $node }.
core-validation-hook-operation-spelling = A Core hook contract's operation is not named publish.
core-validation-hook-operation-spelling-node = { core-validation-hook-operation-spelling } Core node: { $node }.
core-validation-hook-operation-endomorphism = A Core hook operation has different input and output types.
core-validation-hook-operation-endomorphism-node = { core-validation-hook-operation-endomorphism } Core node: { $node }.
core-validation-hook-contract-operation = A Core hook contract names a different operation from its declaration.
core-validation-hook-contract-operation-node = { core-validation-hook-contract-operation } Core node: { $node }.
core-validation-hook-clause-operation = A Core hook clause handles a different operation from its contract.
core-validation-hook-clause-operation-node = { core-validation-hook-clause-operation } Core node: { $node }.
core-validation-hook-input-identity = A Core hook clause binds a different input identity from its contract.
core-validation-hook-input-identity-node = { core-validation-hook-input-identity } Core node: { $node }.
core-validation-hook-root-input-use = A Core hook root resumes with a variable other than its recorded input.
core-validation-hook-root-input-use-node = { core-validation-hook-root-input-use } Core node: { $node }.
core-validation-hook-clause-continuation = A Core hook clause has a different continuation owner from its contract.
core-validation-hook-clause-continuation-node = { core-validation-hook-clause-continuation } Core node: { $node }.
core-validation-hook-resume-owner = A Core hook resume names a different continuation owner from its contract.
core-validation-hook-resume-owner-node = { core-validation-hook-resume-owner } Core node: { $node }.
core-validation-hook-resume-handler = A Core hook resume names a different handler from its enclosing handler.
core-validation-hook-resume-handler-node = { core-validation-hook-resume-handler } Core node: { $node }.
core-validation-hook-resume-use-state = A Core hook resume does not carry the consumed-continuation state.
core-validation-hook-resume-use-state-node = { core-validation-hook-resume-use-state } Core node: { $node }.
core-validation-hook-scope-origin = A Core hook handler's origin differs from its contract's scope span.
core-validation-hook-scope-origin-node = { core-validation-hook-scope-origin } Core node: { $node }.
core-validation-hook-target-span = A Core hook contract's target span is not contained in its scope span in the same source.
core-validation-hook-target-span-node = { core-validation-hook-target-span } Core node: { $node }.
core-validation-hook-generated-origins = Generated Core hook nodes or binders have origins different from the contract's target span.
core-validation-hook-generated-origins-node = { core-validation-hook-generated-origins } Core node: { $node }.
core-validation-hook-missing-effect = The compiler has no effect declaration for a Core hook registration contract.
core-validation-hook-missing-effect-node = { core-validation-hook-missing-effect } Core node: { $node }.
core-validation-hook-duplicate-binders = A Core hook registration contract reuses an identity among its callback, input, previous and next binders.
core-validation-hook-duplicate-binders-node = { core-validation-hook-duplicate-binders } Core node: { $node }.
core-validation-hook-previous-binding-shape = A Core hook registration clause does not begin with its previous-result binding.
core-validation-hook-previous-binding-shape-node = { core-validation-hook-previous-binding-shape } Core node: { $node }.
core-validation-hook-next-binding-shape = A Core hook registration does not bind the next result after the previous result.
core-validation-hook-next-binding-shape-node = { core-validation-hook-next-binding-shape } Core node: { $node }.
core-validation-hook-forward-request-shape = A Core hook registration's previous-result initializer is not an effect request.
core-validation-hook-forward-request-shape-node = { core-validation-hook-forward-request-shape } Core node: { $node }.
core-validation-hook-callback-application-shape = A Core hook registration's next-result initializer is not a callback application.
core-validation-hook-callback-application-shape-node = { core-validation-hook-callback-application-shape } Core node: { $node }.
core-validation-hook-registration-resume-shape = A Core hook registration does not resume after binding the callback result.
core-validation-hook-registration-resume-shape-node = { core-validation-hook-registration-resume-shape } Core node: { $node }.
core-validation-hook-forward-effect = A Core hook registration forwards a different effect instance from its contract target.
core-validation-hook-forward-effect-node = { core-validation-hook-forward-effect } Core node: { $node }.
core-validation-hook-previous-binder = A Core hook registration binds the previous result with an identity different from its contract.
core-validation-hook-previous-binder-node = { core-validation-hook-previous-binder } Core node: { $node }.
core-validation-hook-next-binder = A Core hook registration binds the next result with an identity different from its contract.
core-validation-hook-next-binder-node = { core-validation-hook-next-binder } Core node: { $node }.
core-validation-hook-forward-operation = A Core hook registration forwards a different operation from its contract.
core-validation-hook-forward-operation-node = { core-validation-hook-forward-operation } Core node: { $node }.
core-validation-hook-forward-input = A Core hook registration's forwarded request does not use its recorded input at the target span.
core-validation-hook-forward-input-node = { core-validation-hook-forward-input } Core node: { $node }.
core-validation-hook-callback-use = A Core hook registration does not call its recorded callback at the target span.
core-validation-hook-callback-use-node = { core-validation-hook-callback-use } Core node: { $node }.
core-validation-hook-previous-use = A Core hook registration does not pass its recorded previous result to the callback at the target span.
core-validation-hook-previous-use-node = { core-validation-hook-previous-use } Core node: { $node }.
core-validation-hook-next-use = A Core hook registration does not resume with its recorded next result at the target span.
core-validation-hook-next-use-node = { core-validation-hook-next-use } Core node: { $node }.
runtime-missing-node = The runtime could not find a node in the validated program.
runtime-unexpected-primitive-value = A primitive received a value outside its validated type.
runtime-unexpected-function-value = A validated function call received a value that is not a function.
runtime-missing-binding = The runtime could not find a variable's lexical binding.
runtime-unexpected-recursive-binding = A recursive binding does not have its validated initializer form.
runtime-environment-capacity = The runtime cannot retain another lexical binding.
runtime-invalid-control-state = The runtime reached an inconsistent control state.
runtime-heap-capacity = The runtime heap cannot hold another cell.
runtime-captured-control-capacity = The runtime cannot retain another captured control frame.
runtime-resource-capacity = The runtime cannot represent another live resource or fresh activation.
runtime-invalid-location = The runtime tried to access a heap location outside this evaluation.
runtime-uninitialized-location = The program tried to use a recursive value before it was initialized.
runtime-alias-loop = The runtime found a cycle of heap aliases without a constructed value.
runtime-impossible-match = A match validated as exhaustive did not select an arm.
runtime-capacity-exhausted = A configured or representational resource limit cannot admit the request.
runtime-allocator-refused = The host allocator refused a storage reservation.
runtime-storage-reservation-failed = A host storage reservation failed; its underlying cause is undetermined.
runtime-work-budget-exhausted = The runtime work budget cannot admit the requested work.
runtime-phase-acquisition = resource acquisition
runtime-phase-capture = continuation capture or restoration
runtime-phase-evaluation = program evaluation
runtime-phase-cleanup = source cleanup
runtime-phase-access = effect access
runtime-phase-teardown = host teardown
runtime-phase-diagnostic-preparation = diagnostic preparation
runtime-resource-type-disposal = type disposal tasks
runtime-resource-kind-disposal = kind disposal tasks
runtime-resource-environment-disposal = environment disposal entries
runtime-resource-captured-disposal = captured disposal frames
runtime-resource-work-units = runtime work units
runtime-resource-resource-owners = resource owners
runtime-resource-cleanup-owners = cleanup owners
runtime-resource-registration-owners = registration owners
runtime-resource-registration-keys = representable registration keys
runtime-resource-registration-invocations = registration invocations
runtime-resource-activation-keys = representable activation keys
runtime-resource-environment-bindings = representable environment bindings
runtime-resource-frame-storage = control frames
runtime-resource-effect-trace = effect trace events
runtime-resource-evaluation-trace = evaluation trace events
runtime-resource-result-heap-cells = result heap cells
runtime-resource-heap-cells = runtime heap cells
runtime-resource-instantiation-entries = instantiation entries
runtime-resource-instantiation-storage = instantiation storage cells
runtime-resource-capture-inspection = capture inspection entries
runtime-resource-registration-identities = registration identities
runtime-cleanup-complete = Host cleanup completed.
runtime-cleanup-incomplete = Host cleanup stopped before all retained state was released.
runtime-cleanup-unknown = Host cleanup completion has not been established.
runtime-label-cause = Detected cause
runtime-label-phase = Phase
runtime-label-resource = Resource
runtime-label-requested = Requested additional units
runtime-label-available = Available additional units
runtime-label-teardown = First teardown failure
runtime-label-cleanup = Cleanup status
invocation-usage = Expected: ash [--message-format human|short|json] [--locale NAME] [--root name=path]... <entry-file>. Options must precede the entry file; format and locale may each be supplied only once.
output-write = Ash could not write the program result to standard output.
resolve-dependency-summary-mismatch = The compiler received incomplete or mismatched checked information for this module's imports.
resolve-dependency-summary-invalid = The compiler could not validate the checked information for this imported module.
resolve-missing-file-scope = The compiler lost the file's name-resolution scope.
resolve-missing-lexical-scope = The compiler lost the current lexical scope while resolving a binding.
resolve-missing-nominal-scope = The compiler lost the scope for local nominal types.
resolve-missing-constructor-scope = The compiler lost the scope for local constructors.
resolve-declaration-order = The compiler's declaration order is invalid for { $kind ->
    [nominal] nominal types
    [interface] interfaces
    [effect] effects
    [global] global values
   *[implementation] implementations
    }: { $problem ->
    [invalid-index] a declaration index is out of range.
    [repeated-or-reordered] a declaration is repeated or out of order.
    [skipped-or-reordered] a declaration is skipped or out of order.
    [omitted] a declaration is missing.
   *[repeated-skipped-or-reordered] a declaration is repeated, skipped, or out of order.
    }
resolve-work-state = The compiler's name-resolution state { $problem ->
    [missing] is missing
    [extra] unexpectedly retains
    [wrong] has the wrong value for
    [not-single] does not retain exactly one value for
    [mismatch] contains conflicting information for
    [empty] is empty for
    [duplicate] repeats
    [unvalidated] cannot validate
   *[incomplete] is incomplete for
    } { $part ->
    [equation] an equation
    [operational-pattern] an operational parameter pattern
    [operational-parameter] an operational parameter
    [operational-body] an operational body
    [tuple-type-element] a tuple type element
    [effect-row-argument] an effect-row type argument
    [function-codomain] a function result type
    [function-domain] a function argument type
    [type-argument] a type argument
    [type] a type
    [block] a block
    [binding-pattern] a binding pattern
    [binding-initializer] a binding initializer
    [recursive-member] a recursive group member
    [block-result] a block result
    [block-binding] a block binding
    [function-body] a function body
    [tuple-element] a tuple element
    [hook-body] a hook body
    [registration-body] a registration body
    [registration-initializer] a registration initializer
    [cleanup-body] a cleanup body
    [cleanup-initializer] a cleanup initializer
    [resource-initializer] a resource initializer
    [resource-body] a resource body
    [lexical-evidence-application] a lexical evidence application
    [lexical-method-body] a lexical method body
    [lexical-method-group] a lexical method group
    [request-operand] a request operand
    [private-constructor] a private constructor
    [opaque-constructor] an opaque constructor
    [public-constructor] a public constructor
    [export-effect-fact] checked effect information for an exported module
    [effective-route-rank] the ordering rank of an effective implementation route
    [public-route-rank] the ordering rank of a public implementation route
    [route-selected-fact] the selected implementation information for a route rank
    [implementation-interface-fact] the defining interface information for an implementation
    [implementation-capture-effect] effect metadata referenced by an implementation capture graph
    [public-implementation-fact] the selected public implementation information
    [export-capture-effect] effect metadata referenced by an exported capture graph
    [export-scheme-effect] effect metadata referenced by an exported type scheme
    [export-scheme-nominal] nominal metadata referenced by an exported type scheme
    [opaque-scheme-representation] the canonical representation of an opaque newtype scheme
    [route-nominal-closure] the nominal dependency closure retained for an alternate import route
    [opaque-export-representation] the canonical representation of an exported opaque newtype
    [transparent-constructor] a constructor of an exported transparent type
    [constructor-nominal-metadata] nominal metadata referenced by an exported constructor
    [constructor-owner-metadata] owner metadata referenced by an exported constructor
    [nominal-identity] a nominal declaration identity
    [global-binder-slot] a global binder slot
    [implementation-plan] an implementation plan
    [global-binder] a global binder
    [hidden-method-binder] a hidden method binder
    [newtype-representation] the representation of a resolved newtype
    [newtype-representation-origin] source provenance for a resolved newtype representation
    [pure-effect-origin] effect-argument provenance on a pure function
    [method-parameters] method parameters
    [resource-builtin-origin] the source origin of a resource builtin
    [public-nominal-visibility] visibility of a nominal type in public exports
    [projected-newtype-constructor] the constructor of a projected newtype
    [projected-newtype-representation] the representation of a projected newtype
    [effect-preparation] effect preparation records
    [operation-identities] operation identities
    [interface-parameters] the parameter vector of a projected interface
    [interface-preparation] interface preparation records
    [interface-method-preparation] interface method preparation records
    [prepared-method-binder] a prepared binder in an interface method's type scope
    [implementation-head-arguments] the argument vector of a projected implementation head
    [export-term-name] a term name in checked module information
    [export-interface-name] an interface name in checked module information
    [export-effect-name] an effect name in checked module information
    [alternate-effect-fact] canonical effect information from alternate import routes
    [interface-visibility] the visibility boundary of an imported interface identity
    [alternate-interface-fact] checked interface information from alternate import routes
    [method-interface-owner] interface ownership of an imported method
    [imported-method-authority] an imported method and its checked authority information
    [implementation-authorization] an imported implementation's authorization route
    [alternate-implementation-fact] checked implementation information from alternate import routes
    [implementation-prerequisite] an imported implementation's prerequisite identity
    [implementation-method-relation] an imported implementation's method relation
    [implementation-method-scheme] an imported implementation's method type scheme
    [implementation-route-rank] an implementation route rank
    [public-implementation-route-rank] a public implementation route rank
    [alternate-global-fact] checked global information from alternate import routes
    [alternate-nominal-metadata] nominal metadata retained through alternate import routes
    [opaque-data-representation] a canonical representation for an opaque type that is not a newtype
    [alternate-constructor-fact] checked constructor information from alternate import routes
    [constructor-route-nominal] nominal metadata retained through alternate constructor routes
    [interface-arguments] the argument vector of a projected interface application
    [definition-clause] a clause of an equational definition
    [implementation-method-group] an implementation method group
    [implementation-plans] implementation plans
    [method-group-range] a method-group range
    [method-group] a method group
    [method-group-source] source-file ownership within an implementation method group
    [local-nominal-kind] the newtype declaration kind required for a block-local nominal
    [method-equation-source] source-file ownership of method equations
    [imported-nominal-metadata] nominal metadata from imported routes
    [imported-fact-comparison] retained state used to compare imported information
   *[expression] an expression
    [match-pattern] a match pattern
    [function-pattern] a function parameter pattern
    [handler-pattern] a handler parameter pattern
    [right-operand] a right operand
    [left-operand] a left operand
    }.
