# CP-0022: Ash-authored foreign interfaces

- ID: `CP-0022`
- Status: accepted
- Related: [DN-0037](../design/DN-0037-ash-authored-foreign-library-interfaces.md),
  [DN-0042](../design/DN-0042-native-interaction-and-efficient-data.md),
  [AD-0013](../decisions/AD-0013-generated-native-bridges-and-program-builds.md),
  [GitHub issue #1](https://github.com/dikini/ash-lang/issues/1)

> This accepted proposal authorizes the bounded implementation tasks. It is not
> current Ash before the complete verified transition is integrated into Main.

The semantic contract was accepted on 2026-10-10 after frontend/operational and
build-boundary review. Acceptance includes the private state payload, both report
codecs, finite copy-window restrictions and blocked-dependent retention rule.

## Current behavior

The [specification](../../spec/README.md) has passive source modules, mathematical
`Int`, evaluator-managed ordinary values, exact effect identities, checked
capture/discard, and compiler-owned `cell` and `native_buffer` resources. It has
no general foreign declarations, C layout guarantee, source address arithmetic
or Ash binary ABI.

DN-0036 code is retained on Main as an experiment. Its Rust manifests and
`ExecutableForeignModule` implementations admit library resources and execute
SQLite and Arena programs. Their presence does not make the experiment normative.
The [readiness review](../design/foreign-authoring/dn-0036-readiness.md) identifies
the transferable evidence and policy still in Rust. This proposal adopts only
the bounded resource/copying mechanisms described below. Experimental typed
Arena storage and unfinished wider cases remain outside the product claim.

## Proposed behavior

An author declares a native library's ABI facts and foreign assumptions in Ash,
then writes conversion, protocol, error and resource policy in ordinary Ash.
Common tools check those declarations and build an executable whose generated
Rust bridges call the declared symbols and whose existing evaluator runs checked
Core. Adding a library inside the supported profile requires no library-specific
Rust manifest, Rust adapter, C shim or compiler dispatch change.

Imports stay passive. A library is an ordinary Ash source dependency. The entry
module and build configuration select a program, target and native link inputs;
an import never opens a database, allocates an arena or shuts down a library.

### Bounded ABI profile

The first profile is `x86_64-unknown-linux-gnu`, with the platform C calling
convention. Native link inputs may be static archives or ordinary shared-library
dependencies. Dynamic loading is excluded. A build rejects other targets rather
than assuming compatible widths or calling conventions.

The profile admits `void` results; signed and unsigned scalar representations of
8, 32 and 64 bits; `size_t`; opaque object addresses; byte addresses; nullable
addresses; typed output slots; and the non-callable function-address sentinel
needed by SQLite. Their uses are position-specific:

| Foreign role | Ash meaning and admission |
| --- | --- |
| Integer scalar | Mathematical `Int`, narrowed with a checked range before the call and widened exactly on return. This introduces no machine-integer arithmetic. |
| `void` result | `Unit` after the native call. `void` is not an argument value, object storage type or array element. A no-argument C function has zero operands. |
| `void *` | Opaque address in a declared owner/access role. It is not `Unit`, an integer or a generic Ash value. |
| Opaque object address | A sealed owner or non-owning access tied to its defining foreign type and live activation. Null is represented separately. |
| Byte/string input | Stable temporary bytes with explicit extent; NUL termination and interior-NUL rejection are separate conversions. C array parameters are pointer-plus-contract uses, not by-value Ash arrays. |
| Output slot | Private, aligned native storage of one declared representation, initialized as specified below; its address never becomes an ordinary value. |
| Function-address sentinel | A declared target bit pattern passed in a non-callable role. It is never formed as a Rust function value and cannot be called, converted to `Int` or supplied to a callable role. |

Foreign representation is not Ash meaning. `String` stores validated UTF-8 and
`Bytes` stores immutable independent bytes. Conversion can fail for range,
encoding, bounds or allocation. A foreign pointer is not evidence of extent,
initialization, alignment, ownership or lifetime. Only its checked contract and
live runtime access establish those facts.

Aggregate-by-value ABI, arbitrary layouts, variadics, function callbacks,
asynchronous native calls and pointer arithmetic are excluded. A declaration
with an unsupported shape is rejected before bridge generation or acquisition.

### Source contract and public identity

Add a module declaration `foreign library Name { ... }`. Members declare the
profile, foreign representations, literal constants/sentinels, native symbols
with complete ABI signatures, and their access/initialization/ownership
assumptions. Members are line-separated, like current declarations. The
declaration has no executable initialization body. Visibility follows current
module publication rules; aliases preserve defining identities.

The following grammar defines foreign declarations and bounded copy-window
expressions. Existing `type`, `type_parameters`, `block`, identifiers, string and
integer literals, and `line_end` retain their current meanings. `member_reference`
is a local or module-qualified defining member. `source_position` selects a
leaf in the source argument product by a zero-based dotted integer path;
`native_position` selects a zero-based ABI argument or `result`. `outcome_test`
uses raw results and initialized outputs, never ordinary Ash computations.
Contract lines are checked for exact coverage and consistency as described below.
Here `integer_literal` is the existing unsigned `integer` token with an optional
leading minus for constant values; positions and widths must be nonnegative.
`string_literal` uses the bounded String syntax adopted from DN-0036 below.

```ebnf
foreign_library ::= [ "pub" ] "foreign" "library" upper_identifier
  "{" line_end foreign_member { line_end foreign_member } [ line_end ] "}" ;
foreign_member ::= profile_member | representation_member | constant_member
  | symbol_member | access_member | owner_member ;
profile_member ::= "profile" string_literal ;
representation_member ::= "repr" upper_identifier "=" foreign_representation ;
foreign_representation ::= "signed" "(" integer_literal ")"
  | "unsigned" "(" integer_literal ")" | "size_t" | "opaque"
  | "bytes" | "function_address" ;
constant_member ::= "const" upper_identifier ":" member_reference "=" integer_literal
  | "sentinel" upper_identifier ":" member_reference "=" "all_bits_one" ;
owner_member ::= "owner" upper_identifier type_parameters
  "{" line_end "representation" member_reference line_end
  "owned" upper_identifier line_end [ "retains" identifier_list line_end ]
  "teardown" member_reference [ line_end ] "}" ;
access_member ::= "access" upper_identifier type_parameters
  "{" line_end "window" upper_identifier line_end
  "owner" type line_end "extent" extent_contract line_end
  "preserves" member_reference { "," member_reference } [ line_end ] "}" ;
extent_contract ::= "bytes" | "nul" ;
symbol_member ::= "symbol" upper_identifier [ type_parameters ] ":" type
  "{" line_end "name" string_literal line_end
  "abi" "(" [ abi_operand { "," abi_operand } ] ")" "->" abi_representation
  line_end call_contract { line_end call_contract } [ line_end ] "}" ;
abi_operand ::= abi_representation | "out" "(" abi_representation ")" ;
abi_representation ::= member_reference | "void" | "pointer" "(" member_reference ")" ;
call_contract ::= "operand" native_position "from" source_position operand_role
  | "operand" native_position "from" "constant" member_reference
  | "operand" native_position "from" "null"
  | "output" native_position "as" output_role
  | "outcome" outcome_test "{" outcome_fact { "," outcome_fact } "}"
  | "retained_dependents" "block" ;
operand_role ::= "scalar" | "current" | "enclosing" | "view"
  | "bytes" "(" source_position ")" input_discipline
  | "nul" input_discipline | "sentinel" ;
input_discipline ::= "call_borrow" | "copy" ;
output_role ::= "scalar" | "owner" "(" type ")"
  | "view" "(" type [ "," source_position_list ] ")"
  | "extent_of" "(" source_position [ "," source_position_list ] ")"
  | "offset_into" "(" source_position ")" ;
outcome_test ::= outcome_atom { "and" outcome_atom } | "otherwise" ;
outcome_atom ::= native_position "==" member_reference
  | native_position "null" | native_position "nonnull" ;
outcome_fact ::= "readable" native_position | "unreadable" native_position
  | "consumed" source_position | "retained" source_position
  | "initialized_bytes" native_position "from" source_position ;
native_position ::= integer_literal | "result" ;
source_position ::= integer_literal { "." integer_literal } ;
source_position_list ::= source_position { "," source_position } ;
identifier_list ::= upper_identifier { "," upper_identifier } ;
member_reference ::= upper_identifier | upper_identifier "." upper_identifier ;
copy_window_expression ::= "copy_window" type "from" primary_expression block ;
```

Representation members occupy an ABI namespace: a scalar representation does
not introduce a new ordinary Ash integer type. Constants publish checked `Int`
values; sentinel members publish only a non-callable operand role. Owner members
introduce opaque, identity-indexed state types and access members introduce
opaque window-indexed view types, neither with source constructors. A symbol
introduces an exact native effect with one `call` operation of its declared source
function type; use existing `perform Module.Symbol<arguments>.call operands`.
Every symbol's complete source type and kinded parameters are checked, including
parameters that contribute dependencies but no native operand.

The library declaration establishes a defining native-library identity without
adding a nested source namespace. Its members participate in their module's
ordinary namespaces and inherit the declaration's publication mode; imports and
qualified uses therefore keep the current `Module.Member` form. A module may
declare more than one library only with disjoint member spellings. Native build
configuration maps exact library identities to link inputs; it cannot replace a
checked signature or assumption.

All ABI input positions map exactly once to a source leaf, constant or explicit null. All
non-void results/output slots have one result role and total readability facts.
Pointers to input scratch use `bytes`/`nul`, owner addresses use `current` or
`enclosing`, and view addresses use their admitted access family. `void` is legal
only as the result. ABI scalar widths are restricted by the profile; negative
indices, unsupported pointer depths and by-value opaque objects reject.
An `out(pointer(...))` is a private output slot, not an additional source operand.
`from null` supplies a null address only to a nullable address ABI position,
without creating owner/access authority. It is distinct from a non-null empty
input and permits SQLite's optional VFS operand. It cannot supply an integer,
an owned current state or a function-address sentinel.
The clause explicitly assumes that null is acceptable to the foreign callee at
that position; pointer representation alone does not imply this assumption.

`copy_window Family<W, Owners...> from state { body }` introduces a fresh `W` in
the body. The family declares its owner argument and access-compatible operations;
the `window` member identifies the family's fresh Type-kind argument and the
state expression must denote an authenticated live, pending-acquisition or
completing guard under its permitted direct provider phase. View-producing
calls in the body return views indexed by that `W`; no view exists before its
producing call. The fresh binder is a lexical identity, like a resource identity,
not a globally selectable type argument. Every returning path closes the window.

| Member role | Required checked contents |
| --- | --- |
| Profile | Exact profile identity; no implicit host fallback. |
| Representation | Defining identity and one admitted scalar, opaque-address, byte-address or non-callable-sentinel shape. All foreign type applications preserve declared kinds and ordered arguments. |
| Constant | Literal mathematical value and checked scalar representation, or literal sentinel bits and non-callable role. Header evaluation is not needed to obtain its executable value. |
| Symbol | Defining library/symbol identities, native spelling, calling convention, ordered operand/result representations, corresponding Ash types, and complete call contract. |
| Access family | Owner positions/dependencies, nullable and extent rules, and a finite validity window with the exact original operations that preserve it. |
| Owner family | Acquisition output position, dependency positions, finish disposition rule and host-destruction symbol/contract. A name or ordinary result constructor grants no ownership. |

A call contract lists which operands are copied inputs, call-duration borrows,
current/enclosing owner views or initialized output slots. It states whether
native code retains an input, which live output windows it preserves or
invalidates, which outputs are readable for each raw status, and which owner is
established, consumed or retained for each raw status. The first profile rejects
retained input borrows. It may pass input storage only to a declaration promising
that the callee uses it during the call or makes its own independent copy.

`call_borrow` declares use only until the native call returns. `copy` declares
that accepted inputs become independent native copies. Both forbid retention
of the prepared input address on every outcome. Output `view` and independent
copied Bytes/String remain separate types. A retained-input discipline is not
silently accepted as either of these forms.

Outcome predicates are total finite alternatives over the raw returned scalar,
nullness and initialized output values: equality to a declared literal, null or
nonnull, with a final otherwise branch. Overlap, gaps, incompatible ownership
dispositions and reading an output before its initialization condition holds
are declaration errors. Arbitrary Ash code does not decide native disposition.
Ash code uses the admitted disposition to decide how to report it.

Non-null readable outputs with an `owner` role always create a pending guard,
including on error statuses. A nullable output yields no guard when null. A
teardown member references a symbol with exactly one current owned operand,
only already-live dependency/scalar operands and no owner-producing outputs.
Its outcome cases must describe consumed versus retained for every result.
`retained_dependents block` forbids the native call when any transitive dependent
guard remains retained; its sealed result is retention. This rule is mandatory
on all consuming finish/destruction symbols in this profile.

These predicates and access promises are **foreign assumptions**, supplied by
the author. Checking establishes their consistency and subsequent Ash use, not
their truth of an external binary. Optional header checks establish agreement
of the chosen ABI declarations/constants with supplied headers, not native
behavior, version identity or memory safety.

The checked public contract includes complete source arguments, kinds, identity
roles, representations, assumptions and defining origins. Native bridge operand
arrays are Type-only projections of the complete ordered Type/EffectRow source
vector; their mapping is authenticated. A row is never silently dropped or
reinterpreted as a native ABI type. Imported clients check from public summaries
without replaying library bodies or selecting their implementations again.

Each native call returns a common `Foreign.Call<T>`: `Returned(T)` or
`ConversionFailed(Foreign.ConversionError)`. The latter denotes an explicit
pre-call conversion refusal; internal work/storage exhaustion is terminal.
`T` is the canonical result product: the non-void ABI result first, then output
slots in ABI order; zero fields use `Unit` and one field is unwrapped. Each slot
uses `Foreign.Output<U> = Unreadable | Readable(U)`. A raw pointer result uses
the same wrapper; a raw scalar result must always be readable and is bare.
Nullable addresses use
`Foreign.Nullable<U> = Null | NonNull(U)`. Scalars are `Int`, offsets are `Int`,
owned addresses become opaque state tokens and borrowed addresses become views.
An `extent_of` scalar result becomes the sealed matching extent type described
below. Input-relative addresses become nullable independent offsets; no native
address survives that extraction.
The source symbol type must equal this reconstructed shape. No custom Rust
codec is required to return it.

One call may produce at most one new owned output or finish one current owner;
it cannot do both. Multi-owner acquisition belongs to later work. Borrowed
views/offsets and scalar slots may accompany that one owner.

For a finishing symbol, wrap the canonical result in
`Foreign.Disposition<T> = Consumed(T) | Retained(T) | BlockedDependent`.
The runtime chooses this witnessed variant from the contract before ordinary
payload allocation; constructors alone confer no phase permission. A source
finish maps its error payload while preserving this admitted disposition. A
blocked dependent does not have a fabricated C status; the library maps that
distinct case to its own retained-completion error. Post-call output extraction
failures preserve the witnessed native outcome, dispose unpublished guards,
and terminate rather than constructing a successful raw reply.

### Common primitives and library policy

Common primitives provide checked scalar conversion; stable copied inputs;
zero/null-initialized output slots; nullable owner adoption; bounded byte/NUL
copies and UTF-8 conversion; bounded input-relative offset extraction; byte
read/write; and calls under admitted access.
They also provide the sealed acquisition/finish evidence consumed by the
resource machine. The implementation exposes no raw pointer as an Ash `Int`,
no ownership-cloning operation and no generic unchecked cast.

Primitives have explicit failure results and work/storage charges. Before a
native call, prepare operand conversions, scratch, output storage and guard
slots fallibly. Native side effects occur once and cannot in general be rolled
back. A failed later conversion cannot replay the call or undo its disposition.

Library Ash code defines ordinary error ADTs, conversions, constants, protocol
and handlers. It can inspect copied raw statuses and admitted nullable outputs,
call the common primitives and branch into acquisition or completion reports.
It cannot manufacture an owner by constructing an ordinary ADT or claiming a
successful status. The runtime guard table holds ownership; source state and
handles hold non-owning, authenticated activation references.

The bounded state model pairs the compiler-owned native guard slot with one
ordinary Ash payload of declared type `D`. Add `data D` to a resource definition.
Successful direct acquire returns `Acquired(state, payload)` under a checked
acquisition codec with that field order; `Refused(error)` has one field. The state
must be the same pending guard lineage produced by its acquiring call. A refused
path disposes any pending partial owner. This creates no owning source value.

Controlled, fully applied `Provider.data_of state` returns the current payload;
`Provider.replace_data (state, payload)` prepares admission fallibly, then replaces
it and returns `Unit`. It changes no native guard. These privileged methods use
an exact sealed state/data relation supplied by the descriptor, like
`StateAccess`; ordinary implementations cannot manufacture it. A payload's type
and stored dependencies are checked against `D` and the resource's admitted
retained identities. Payloads cannot contain state tokens, native views or the
closing resource identity. Replacement completes before handler resume and
preserves the previous value if preparation fails. Terminal failure still owns
the guard and invokes safe destruction. This supplies private resource state,
not general mutable variables, mutable ordinary records or new cell semantics.

Acquire and finish have sealed lifecycle permissions; provider handlers get
borrowed state only. Direct blocks, matches and local aliases preserve lineage.
Ordinary global/lambda/evidence-method bodies clear privileged authority, as in
P-1. Ordinary pure helpers over payload values and client helpers using public
associated effects remain legal. The first lifecycle profile has empty outward
rows after exact native interpretation: no source capture/handlers, resume/discard,
hooks, cleanup or nested resources in acquire/finish. Each normally returning
finish path uses its one current completion permission.

Owner-free symbols with only independent scalar/input/offset results need no
provider state authority and may occur in ordinary Ash functions. Their exact
native effect stays in the function's row. At program admission, a mandatory
foreign interpreter discharges precisely the independently checked owner-free
native effects with linked bridges; the remaining entry row must be empty.
It cannot discharge an ordinary source effect or grant lifecycle permission.
Resource-native effects are interpreted only under the descriptor's controlled
phase. Acquiring/finishing/state/view operations remain subject to the callable
barrier. `handle` cannot replace a native symbol's sealed interpreter with a
source clause; public library-associated effects retain ordinary user-handler
precedence. Existing non-foreign empty-row entry programs keep their behavior.

### Temporary input and output access

Input preparation creates stable storage for one synchronous call. The callee
contract chooses a byte extent or NUL-terminated convention. The wrapper cannot
reuse a borrowed address after the call; input scratch is destroyed after the
call and output extraction. Independently copied Ash inputs remain ordinary
values. SQLite's transient sentinel means that SQLite makes its own copy; this
does not admit a retained Ash input pointer. `offset_into(input)` extraction
checks that a readable non-null address denotes a byte offset in that prepared
input, including its end position but excluding unrelated storage. It returns
an independent `Int` before destroying scratch; no source pointer arithmetic is
available. This permits `sqlite3_prepare_v2` tail checks against the original
copied SQL and rejection of trailing statements. Invalid offsets are conversion
failures and trigger disposal of a partial statement guard.

A returned borrowed address is accessible only inside a fresh lexical copy
window `W`, tied to its authenticated guard lineage and declared access family. Its
type carries `W` and that owner identity. A copied `Bytes`, `String` or `Int`
loses that native dependency. A nullable result remains distinct from a zero
extent non-null result; neither fabricates initialized memory.

A view-producing output captures the declared scalar key leaves (for example,
the column index) together with its exact owner lineage and window. A length
query with `extent_of(view_position, key_positions)` receives that view as an
additional source operand, with no extra ABI operand. Before calling, its owner
and scalar keys must match those recorded in the view. Its declared scalar
result produces sealed `Foreign.Extent<Family<W,Owners...>>` evidence tied to
that exact view, not an arbitrary `Int`. Bounded copying requires the view and
its extent evidence. A pointer for column 0 and a length for column 1 cannot
establish a copy bound, even if both native symbols preserve the window. A
statically demonstrable mismatch rejects; dynamic mismatches refuse before
the query. NUL access instead uses the admitted bounded scan rule below.

An owned allocation's `initialized_bytes(output, source_leaf)` outcome fact
records an initialized byte region of that checked nonnegative source extent.
Generic byte read/write checks this recorded extent, live lineage and byte range
before accessing memory; an ordinary `data D` length cannot grant memory access.
The fact is an explicit foreign promise about allocation/initialization and
writability of this owned byte region, not
an inferred consequence of non-nullness. This suffices for `calloc(n,1)` without
typed layouts or general pointer arithmetic.

Within a window, pure Ash work and native operations explicitly declared to
preserve that exact family are permitted. An operation on the same relevant
owner/dependency that is not listed as preserving invalidates the window and
cannot occur before copying/window closure. Calls on unrelated owners do not
establish access to it. Compatibility compares original operation identities
and exact owner arguments, never symbol names. A pointer/length query sequence
must be expressed by those contracts; one live owner is insufficient.

The initial profile prohibits capture, suspension, owner completion and escape
of an open copy window. Window references cannot leave in values, closures,
evidence, rows, output slots or captured control. Ordinary callable helpers may
only receive independent copied values, not window/state access or privileged
native effects. Direct provider code performs the finite query/copy sequence;
imported client row helpers use public associated effects, whose handlers open
their own windows. This limited temporary access is
distinct from general retained borrowing or zero-copy public values.

Copy requires a declared initialized extent bounded by the configured work and
storage limits. Bounded NUL copying examines at most the admitted payload bound
plus one terminator byte; missing termination is a conversion failure, not
truncation. Each examined address must be valid under the foreign assumption.
An invalid UTF-8 result is an explicit error, not an implicit replacement string.

During controlled acquire, a diagnostic window may root in the pending guard
before client publication, so failed open can copy its diagnostic then refuse.
During finish, a witnessed retained reply preserves only sealed completing
access for listed borrowed diagnostic/query/copy operations, with no second
finish or client access. A consumed reply invalidates every same-owner view
and alias immediately. Still-live enclosing dependencies remain available for
diagnostics after statement consumption. A blocked-dependent result permits
no native access to the blocked owner; source maps its own independent error.

Output slots are initialized to zero/null before the call and never exposed as
Ash addresses. The callee's outcome contract authorizes reading each result.
Successful status alone does not authorize an unmentioned output. Non-null
owned outputs, including partial owners on a failure status, enter guard storage
before diagnostics, copying or ordinary result allocation. An unreadable output
cannot be treated as a newly acquired owner.

### Library-defined resources

Adopt the selected P-1 resource-definition/instance distinction, complete
Type/EffectRow owner arguments, specialization, handler and capture obligations
from the [experimental semantics](../design/provider-experiments/semantics.md),
as bounded below. The source/evidence baseline is Main
`a59c65300d06361479c6b2ccd0bab9346dddc8d1`; later changes to an informative design
note do not change this proposal's contract.

A resource definition declares its family and complete kinds; initializer and
identity-indexed state types; retained identity roles; associated provider,
effects and handlers; acquire and finish clauses; and report codec. The
definition is not an instance and does not acquire state. A resource instance
evaluates its typed initializer once in the preceding scope, infers dependencies
from that value, then introduces a fresh identity and non-owning access inside
its body. Dependent values, effects, evidence and hidden closure captures cannot
escape. Each execution creates a fresh runtime activation even at the same
source occurrence.

Use the following definition grammar, adopting the P-1 assembly while adding
explicit private data and codec references. `effect_instance`, `pattern`,
`expression` and `type_parameters` retain their existing meanings, extended with
complete tagged Type/Row arguments. `result` binds its indicated body-result
parameter. `interpret` lists only exact native symbol effects defined by admitted
foreign declarations. The instance spelling is `resource Family<arguments> handle
= initializer { body }`; the owned argument is a fresh binder, checked before
body admission, and inherited arguments are ordinary actuals.

```ebnf
resource_declaration ::= [ "pub" ] "resource" upper_identifier type_parameters
  "{" line_end "owned" upper_identifier line_end
  "input" type line_end "state" type line_end
  "data" type line_end "acquisition" type line_end "completion" type line_end
  "result" type "for" type_parameters line_end "codec" report_codec line_end
  "provider" type line_end "effect" effect_instance line_end
  "interpret" effect_instance { "," effect_instance } line_end
  "acquire" pattern "=>" expression line_end
  "finish" pattern "=>" expression line_end
  "handlers" pattern "{" line_end handler_clause { line_end handler_clause }
  [ line_end ] "}" [ line_end ] "}" ;
report_codec ::= "scope" | "acquired_only" ;
```

`acquisition` references a nominal `Acquire<State,D,I>` with exact defining-order
roles `Acquired(State,D)` then `Refused(I)`. `completion` references a nominal
`Finish<State,E>` with `Consumed`, `ConsumedFailure(E)`, then `Retained(State,E)`.
These declarations are ordinary library ADTs; their checked identities/field
positions, not their spellings, bind the codec. Successful acquisition paths
return the same witnessed native state; normally returning finish paths preserve
the witnessed disposition, including a blocked-retention outcome. A forged
constructor or another activation's state does not authorize a transition.

`owned` selects one Type-kind formal parameter whose instance position introduces
the fresh identity. It must coincide with the state family's declared owned
argument; other identities follow the inherited-role and initializer-dependency
checks. This selection is explicit and cannot be inferred from a matching method
name. Row parameters remain row arguments and are never fresh owner identities.

Common modules supply generic primitives and their sealed relationships;
library symbols and policy remain source-authored. Primitive operations have
the following bounded type roles. The displayed `Result` is the common
independent conversion-result codec, and each native `State`/`View` retains its
exact owner/family arguments:

| Primitive | Source type role and permission |
| --- | --- |
| `copy_bytes` | `(View<W,...>, Extent<W,...>) -> Result<Bytes, ConversionError>`; evidence must originate from that view; direct provider window only. |
| `copy_nul` | `(View<W,...>, Int) -> Result<Bytes, ConversionError>`; NUL family and checked scan bound; direct provider window only. |
| `decode_utf8` | `Bytes -> Result<String, ConversionError>`; ordinary independent values, no native permission. |
| `extent_value` | `Extent<W,...> -> Int`; exposes a copied length, not authority to read another view. |
| `byte_read` | `(State<R,...>, Int) -> Result<Int, ConversionError>`; initialized owned byte region, live borrowed state and checked index. |
| `byte_write` | `(State<R,...>, Int, Int) -> Result<Unit, ConversionError>`; additionally checked byte range and pre-mutation result admission. |
| `data_of` / `replace_data` | Exact descriptor-supplied `State`/`D` relation; controlled state access/update, never an owning value. |

`codec scope` requires the exact P-1 `Scope`/`Completion` roles below. The
`acquired_only` codec requires a nominal result with defining-order roles
`Success(T)` then `Failure(I)` and normal completion that only consumes. It
supports native-buffer compatibility without inventing a nested completion value.
A retained/failed destruction in that codec is a terminal resource failure,
never `Success`; no report silently loses a completion error. No arbitrary
executable codec callbacks or constructor-name dispatch are admitted.

The product source forms above replace the experiment's Rust-generated native
modules/reserved registration imports. Common primitive/evidence modules remain
compiler-provided generic infrastructure. Experimental fixtures remain labeled
as such until their source-library migrations are verified; retaining their old
spelling temporarily supplies comparison evidence, not a second product FFI.

Use one ordered, kind-preserving Type/Row actual-argument path. Checked templates
are immutable; specialization retains original occurrence, certificate and
selected-evidence authority, freshens copied local identities and relocates
catalog references. It does not replay source checking or reselect an `impl`.
Principal row conditions and inherited identity roles follow the actual complete
arguments. Handler rows derive from the actual body and per-request captured
control; equal substitutions and scalar body rows do not imply equal capture
demands. Preserve higher-kinded Type behavior and established lacks conditions.

The library report codec has exact defining identities and constructor roles:
`Completion<E> = Closed | ConsumedError(E) | RetainedError(E)` and
`Scope<I,E,T> = NotAcquired(I) | Completed(T, Completion<E>)`. A body `Result`
stays nested. Acquisition refusal executes no body. Normal completion invokes
the admitted source finish once after body and inner cleanup; native disposition
then determines whether the owner was consumed or retained. Ordinary report
construction cannot decide that fact.

Source handles/state views borrow an activation and never clone its owner.
Current versus Enclosing access is authenticated by the descriptor and lexical
identity/dependency relationship. An outer state can be used by an inner
acquisition or cleanup while its owner is live. Ordinary user handlers retain
precedence over provider handlers.

Capture/resume moves the scope ownership with the continuation and resumes the
same activation without acquisition. Owned discard executes required source
completion in structural order while needed outer resources remain live. It
creates neither an abandoned body value nor a fabricated `Scope` result. Running
completion cannot be abandoned, and a required outside interpreter cannot be
skipped. This control behavior applies outside finite copy windows.

Consumed-error completion records consumption even if error conversion fails.
Retained-error completion removes all source access and quarantines the same
owner with its dependencies until host destruction is safe. There is no
automatic source retry, `close_v2` substitution or successful-close fiction.

If a retained child keeps an enclosing owner alive, quarantine revokes ordinary
access but preserves a sealed completion view for that owner's pending scope
frame. Its source finish still runs once; its finishing call observes
`BlockedDependent` before making a native call and maps it to retained completion.
No consuming call may occur and then be rejected after it has freed dependency
memory. Host teardown applies the same pre-call check and keeps an unresolved
dependency closure alive until process termination if a child remains retained.

### Host destruction contract

Every owning foreign output supplies an authenticated native destruction
contract. It refers to a declared synchronous symbol, the owner and admitted
dependency views, and a total disposition rule. Destruction uses already reserved
scalar/address operands; it allocates no Ash result and runs no source handler
or finish template. This permits safe destruction even after a terminal Ash
allocation/conversion failure. Library authors supply the declaration in Ash;
generated bridges apply it without Rust per-library policy.

An unpublished owner is destroyed once on refusal/publication failure before
failure delivery. A retained owner is inaccessible to source and destroyed in
dependency order at host teardown, after dependents are disposed. Destruction
may report consumed or retained. If destruction still retains an owner, its guard
and dependent storage remain quarantined until process termination; the host
reports incomplete destruction and does not retry or free dependent live memory.
Safe host destruction does not imply a successful source completion report.

The foreign author must state which symbol is safe in these states. SQLite
statement finalization consumes even on error; failed connection close retains.
The common runtime derives those actions from declarations and contains no
SQLite names or allocator-specific policy.

### Strict operational transitions

Extend the existing explicit small-step machine. Let `M` contain the expression
and continuation stack, guard store `G`, live access/window store `V`, independent
ordinary store and work counters. `d` is an independently validated descriptor,
`a` a fresh runtime activation, `g` a non-cloneable native guard, `K` a continuation,
`v` a body value and `i` a refused acquisition payload. `finish_d` denotes the
checked source finish under its sealed lifecycle permission, not a native retry.
`completion_guard(a)` resolves the same lineage in either the live or quarantined
store; it does not restore ordinary source access.

These rules describe entry, refusal and publication. `prepared(d)` includes binding,
conversion and capacity checks before acquisition; `guarded(d,g)` authenticates
the original native output and dependency lineage. `publishable` checks the exact
state/report codec and reserves body publication. On any fallible publication
failure, the separate failure transition destroys the unpublished guard and
never starts the body. `Acquiring` is a controlled stack frame; its source
template executes using ordinary small steps. Returning refusal enters a
`Refusing` phase that disposes pending guards before delivering a report.

```sequent
E-ForeignEnter :=
  prepared(d)   initializer = evaluated value
  ===>
  scope(d, initializer, body), M -> acquire_template_d(initializer), M[K := Acquiring(d, body, K)]

E-ForeignRefuse :=
  Refusing(d, i, K) is next
  all partial guards have been disposed or quarantined
  ===>
  M -> return NotAcquired(i), M[K := K]

E-ForeignPublish :=
  Acquiring(d, body, K) is next   returned state has pending guard g
  guarded(d, g)   publishable(d, g)   fresh(a)
  ===>
  return Acquired(state, payload), M -> body[access(a)], M[G[a := g], K := ScopeFrame(d, a, K)]
```

An initializer in these rules is an already evaluated value; its evaluation
precedes fresh identity admission. `Acquired`/`Refused` denote the codec's source
constructor roles; the pending guard and phase receipt, not their names or
ordinary construction, authorize publication. The resulting value in the
refusal rule is the selected report codec's refusal constructor.

Native calls use `CallReady`, `CallReturned` and `CallRecorded` machine states.
`CallReady` contains admitted stable operands, initialized output/guard slots
and the exact original symbol/bridge certificate. One native step produces raw
status/outputs. The next step records all ownership and output-initialization
facts before any Ash conversion or allocation. Only then may copying and ordinary
report construction occur. A terminal failure in any later phase preserves
recorded consumption/retention and safely destroys unpublished owners. It never
returns to `CallReady`. Foreign side effects survive a reporting failure.

These native-call rules name the two distinct steps. `native` denotes one
synchronous external call under the declared assumptions; `record` uses guard
slots and work reserved before it. Recording has no fallible result allocation.
Ordinary conversion/report steps follow `CallRecorded`. `raw` contains native
representations, not invented Ash outputs; output slots have their admitted
initialization conditions.

```sequent
E-NativeCall :=
  CallReady(d, operands) is next   admitted(d, operands)
  native(d.original_symbol, operands) = raw
  ===>
  M -> M[K := CallReturned(d, raw)]

E-NativeRecord :=
  CallReturned(d, raw) is next   record(d, raw, G, V) = (G', V', disposition)
  ===>
  M -> M[G := G', V := V', K := CallRecorded(d, raw, disposition)]
```

Normal completion is sequenced by the following rule. After `finish_d` terminates,
the machine records its native disposition, revokes access and constructs the
appropriate `Completion` and `Completed` report; report-allocation failure is
terminal and does not invoke finish a second time.

```sequent
E-ForeignComplete :=
  ScopeFrame(d, a, K) is next   completion_guard(a) = g   all owned inner cleanup is complete
  ===>
  return(v), M -> finish_d(completion_view(a)), M[K := Completing(d, a, v, K)]
```

`Completing` owns `g`; its access is restricted to the checked finish template.
Closed and consumed-error remove `g`. Retained-error moves `g` and its dependency
closure to quarantine and revokes every source access. Resuming a captured frame
moves it back to the live stack with the same `a`. Discard replaces the abandoned
frames with their structurally ordered finish computations and then returns the
discarding clause's result, never `Completed(v, ...)` for an abandoned `v`.

A copy step requires a live `W` in `V`, initialized extent and remaining work;
it reads native bytes into fresh ordinary storage. Window closure revokes all
access indexed by `W`; independent copied storage survives. An incompatible
call, closing owner, stale activation or missing initialization is rejected
before memory access. Statically malformed Core is never executed.

### Core obligations

For source typing, let `Gamma` be the ordinary environment, `Phi` the controlled
phase/lineage facts, `args` the complete tagged actual vector and `row(F,args)`
the exact generated native effect instance. `Sig(F,args) = A -> B` is the checked
canonical source signature; `Permitted` checks owned/current/enclosing/window
roles against `Phi`. With empty `Phi`, only owner-free operations qualify.
These rules retain call effects and reject unsaturated or incorrectly kinded
arguments before any native execution. A checked interpreter removes only its
listed exact native effects; it does not erase ordinary outward effects.

```sequent
T-ForeignCall :=
  Sig(F, args) = A -> B   kinds_and_saturation(F, args)
  Gamma; Phi |- operand : A ! epsilon   Permitted(F, args, operand, Phi)
  ===>
  Gamma; Phi |- perform F<args>.call operand : B ! (epsilon union {row(F, args)})

T-ForeignInterpret :=
  Gamma; Phi |- body : T ! epsilon   checked_native_set(S, Phi)
  ===>
  Gamma; Phi |- interpret S in body : T ! (epsilon minus S)
```

`interpret S in body` in the second rule denotes the Core/native interpreter
installed by a resource descriptor or the owner-free program boundary, rather
than an additional source expression. Principal conditions on row tails and
capture remain part of the surrounding resource/handler derivation. Empty-row
entry admission is checked after that explicit reconstructed interpretation.

Add generic foreign call, temporary-access and scoped-provider descriptors to
Effect Core. The Pure dialect stays closed. Final executable Core has no
unresolved provider recipe, unchecked symbol/ABI authority or source-owned
pointer. Each descriptor references the canonical original contract, complete
source arguments, authenticated Type-only native projection, exact guard roles,
window/initialization transitions and source template correspondence.

Independent Core validation reconstructs kinds, argument tags/saturation,
lexical dependencies, exact operation/handler table coverage, body/handler/finish
rows, per-request capture demands, output readability, owner lineage and access
compatibility. It checks codec constructor identities rather than recognizing
names. A transform may change structure only with corresponding valid
reconstruction; a stale receipt or same-typed donor dictionary does not suffice.
Module checking and every executable transform preserve this boundary.

### Three library deliveries and migration

| Library | Required Ash policy and observable behavior |
| --- | --- |
| Native buffer | Declare `calloc`/`free`, initialization, bounds/byte conversions and handlers. Preserve the current length/refusal/read/write and normal/discard behavior, including nested results, accounting and pre-mutation checks. Replace the compiler-owned source API with an explicit Ash-library import; publish mechanical caller migration. Keep `cell` unchanged. |
| Minimal arena | Declare native allocation/release and source configuration/state. `(64,4)` really allocates backing and reports `(0,64,0,4)`; source configuration records capacity/slots and zero usage before any allocation API exists. Test nested/repeated, zero capacity, refusal and exactly-once native release. Do not present counters as proof of typed object allocation. |
| Copying SQLite | Declare all required symbols, constants, transient sentinel, output and owner/access contracts. Ash code implements preparation/step/reset protocol, diagnostics, scalar/blob/text conversions, partial acquisition and completion. Run all retained realistic copying/persistence programs. |

Native buffer may preserve its existing success/failure report shape through its
explicit checked codec; migration must not silently wrap it in P-1 `Scope`.
Source compatibility is intentionally broken only by the builtin-to-library
import/resource spelling migration. Bytes/String and their required bounded
operations become product capabilities for copying libraries; no general vector
or contiguous typed storage API follows.

Minimal arena configuration rejects negative/out-of-profile capacities and
object-slot counts before allocation. Zero logical capacity requests one backing
byte so an actual guard/release exists while the admitted logical region is empty.
This is a source-library policy, not compiler dispatch. Native-buffer length
validation retains its current positive-length requirement.

SQLite column access requires row/index/type checks, the admitted pointer query,
an immediate error-code query for suspect results, matching length query and
independent bounded copy before step/reset/finalize. NULL, empty and conversion
failure stay distinct. Its diagnostic window uses its own validity/order contract;
it does not inherit the column window merely because both contain bytes.
Finalization precedes connection close. The basic nested session returns
`Completed(Completed(Ok(42), Closed), Closed)`.

## Semantic delta

1. Add source foreign contracts, position-sensitive native representations and
   explicit foreign assumptions; no address becomes an ordinary Ash scalar.
2. Adopt bounded library-defined resource families, complete owner arguments,
   identity-bound access, private replaceable state payloads, report codecs and
   lifecycle/control rules. The private payload is a new semantic addition;
   unchanged integer cells do not already supply it.
3. Add initialized native output storage and finite copy windows, with independent
   Bytes/String results and explicit conversion failures.
4. Execute authenticated generic native calls with disposition recorded before
   fallible reporting; retain ownership through capture and quarantine.
5. Migrate native buffer to a source library; retain cell behavior and ordinary
   effect/module semantics. Add mandatory interpretation of admitted owner-free
   native effects at program entry; this is not permission to handle arbitrary
   entry effects. Build/link mechanisms are governed by AD-0013.

## Affected specification areas

- [Syntax](../../spec/syntax.md): foreign/library resource declarations, bounded
  access forms and explicit native-buffer migration.
- [Static semantics](../../spec/static-semantics.md): representation positions,
  complete owner applications, fresh identities, access/initialization and rows.
- [Dynamic semantics](../../spec/dynamic-semantics.md): call phases, guarded
  publication, copy-window validity, finish/discard/quarantine and host failure.
- [Elaboration](../../spec/elaboration.md): defining authority, source-to-Core
  descriptors and independent reconstruction before/after transforms.
- [Core elaboration](../../spec/elaboration.md): generic foreign/access/provider
  carriers and independent checks.
- [Overview](../../spec/README.md): bounded product capabilities and exclusions.

These files change with implemented product checkpoints, not with this proposal.

## Resulting specification truth

After complete verified integration into Main, a supported library can be authored
in Ash and built from native inputs without handwritten per-library host glue.
The specified profile and temporary-copy discipline apply; unsafe native behavior
outside declared assumptions is not made safe by typing. General borrowing,
experimental wider Arena storage and other host ABIs remain unsupported claims.

## Interactions

Preserve passive imports, exact defining origins, higher-kinded Type behavior,
open-row lacks conditions, ordinary handler precedence and explicit first-order
control. Reuse current small-step/Core/evaluator boundaries. Public existing
non-foreign `run_path` callers remain valid; new compile/build/execute APIs are
additive except the documented native-buffer source migration.

Preparation can share immutable checked contracts keyed by exact source/target
inputs. It must not cache activations, owners or foreign side effects. Bounded
work, fallible allocation, iterative traversal/disposal and existing depth limits
remain obligations; adding FFI is no reason to raise limits to admit a fixture.

## Non-goals

Files, serialization, general borrowing/storage, typed arena allocation, Layout
families, references/containment/graphs, owner transport, numeric language
additions, efficient vectors, SIMD, callbacks, concurrency, async calls, dynamic
loading, stable Ash ABI, separately compiled Ash libraries, native Ash code
generation and Lean proofs. Syntax convenience beyond a coherent authoring
grammar is deferred. The paused proof/Core workstreams are not dependencies.

## Required evidence

Before acceptance, review the concrete member/access/resource grammar, sealed
data construction/replacement and both report codecs against the actual
copying/native-buffer/arena cases. Reconcile any counterexample here. The
proposed private state payload, blocked-retention rule and copy-window restriction
are semantic choices for acceptance; tasks cannot substitute local alternatives.

Delivery evidence belongs to
[the milestone](https://github.com/dikini/ash-lang/milestone/1), its issues, tasks
and delivering PRs. Reuse existing connected integration cases where they can
observe the new path; add regressions for missing boundaries rather than copy
the corpus. Required observations are:

- Real native calls, independent copies and all realistic SQLite programs;
  static and shared program linkage, including the sentinel without a C shim.
- Acquisition refusal without body entry, partial acquisition guard disposal,
  finalization before close, exactly-once buffer/arena release, zero capacities
  and repeated/nested activations.
- Resume without reacquisition, owned discard/outer-resource cleanup,
  consumed versus retained completion, quarantine/dependency teardown and
  conversion failure after irreversible calls.
- Rejection of invalidation during copying, uninitialized output reads,
  stale/current-versus-enclosing access, dependent escape, forged origins,
  unsupported kinds/representations and malformed/transformed Core.
- Open-Delta Ash callback under the established lacks conditions and the
  separate equal-substitution/body-row witness with different capture demands.
- Explicit native-buffer source migration and unchanged cell behavior.
- A reproducible authoring/build/run walkthrough using only Ash sources,
  native binaries and common tools. Optional C/header checks test exact declared
  facts separately and cannot supply executable constants or authority.

Record source pins, commands, target/link inputs, native observations and failure
injection separately. Preserve measured work and report any admitted calibration
deficit rather than claiming a complexity improvement. Use one Cargo job,
connected checks during development and the full architecture/workspace gate on
integrated delivery. No formal proof claim follows from these executed cases.
