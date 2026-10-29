# CP-0030: Checked network codec

- ID: `CP-0030`
- Status: accepted
- Related: [CP-0027](CP-0027-pinned-workers-and-copied-channels.md), [CP-0028](CP-0028-checked-functional-network-ledger.md), [CP-0029](CP-0029-exact-base-256-integer-split.md), [TASK-0058](../tasks/TASK-0058-pinned-worker-network.md), [issue #79](https://github.com/dikini/ash-lang/issues/79)

> This accepted transition is not current Ash. Acceptance does not establish
> product implementation, actual-definition evidence, or release permission.

## Current behavior

The current [byte module](../../spec/name-resolution.md#independent-byte-and-string-modules)
provides immutable `Bytes`, canonical `empty`, `length`, `at` and `append_byte`
with checked read/append result constructors and terminal work/storage refusal.
Current mathematical integer operations are `+`, `*` and integer equality;
there is no current division, remainder, integer ordering or general byte-array
literal. Canonical builtin identity survives imports and reexports; spelling
and an ordinary same-typed function do not establish the builtin operation.
The ordinary user library currently contains no protocol codec. DN-0041 is
exploratory and supplies no accepted codec or parser semantics.

Accepted [CP-0027](CP-0027-pinned-workers-and-copied-channels.md)
describes authenticated `Application | Control` kind and peer from the actual
channel; bytes do not supply either fact. N2's implemented send path emits
Application, while the checked N4 `send_control` producer and confinement still
need their own implementation and evidence. Accepted
[CP-0028](CP-0028-checked-functional-network-ledger.md)
requires a separately accepted codec extension and its actual-definition
soundness before codec-dependent release. Its N3 invariant and modeled network
coverage take codec correspondence as a premise. The open [N4 issue #79](https://github.com/dikini/ash-lang/issues/79)
still requires this extension and actual-definition evidence. Before this
transition, no accepted codec schema or implementation was found in the
relevant proposals or source.

The missing rule is a *definition-bound conditional codec law*: checked
encoder and decoder bodies, all selected helpers, actual byte intrinsic
identities, argument and returned values, provider/capture closure, and their
composition with actual transport. A source signature, name, constructor,
annotation, round-trip test or assumed theorem cannot issue it. The byte
operations themselves and N3's ledger laws do not establish framing, integer
representation, total consumption or sender honesty.

## Proposed behavior

The following is one deliberately narrow ordinary-Ash format to make the
contract testable. Byte values below are hexadecimal; field order and tags
are proposed, not current Ash semantics or a transport format mandated by
CP-0027. A different encoding needs its own accepted, checked derivation.

For nonnegative mathematical `n`, use little-endian base-256 digits. A group
is byte `01` followed by one byte `d` in `00` through `ff`; byte `00` in the
next group-marker position terminates the scalar. Zero is the empty digit
sequence `00`. For a nonzero value, the last, most-significant digit must be
nonzero; all other digits may be zero. Thus every natural has one finite
representation `U(n)`, including `U(1) = 01 01 00` and
`U(256) = 01 00 01 01 00`. An unknown group marker, a missing digit or
terminator, or a nonempty sequence ending in digit zero is invalid. A digit
byte may itself be `00` or `01`; marker and digit positions are distinct.
No machine-word limit is part of this representation.

Writing these digits from an arbitrary current `Int` needs the separately
accepted [CP-0029: exact base-256 integer split](CP-0029-exact-base-256-integer-split.md).
It returns mathematical quotient/remainder without truncation and gives an
ordinary negative result. The codec is not implementable under this proposal
until that operation has its own accepted semantics, implementation and
verification. Keeping radix digits alongside the ledger counter is an
alternative, not selected: it changes the ledger representation and its
invariant. Do not silently introduce that state.

Use `ID(Root) = 10` and `ID(Work(a, s)) = 11 U(a) U(s)`. Let
`Addr(owner, id) = U(owner) ID(id)`. A full frame is:

- Application Work: `20 ID(child) Addr(parent) U(length(payload)) payload`.
- Control Ack: `21 Addr(parent) ID(child)`.

Payload is exactly the declared number of following bytes, including zero
bytes. Successful decoding requires the cursor to equal the actual full input
length. Every unknown tag, malformed ID, noncanonical scalar, truncated
frame or payload, extra suffix, unrepresentable value and failure supplies no
decoded protocol fact. `Root` is a representable ID, but the ledger and driver
must separately enforce role-specific rules such as non-root work children.
Persistent byte append may copy an accumulated prefix; measure the actual
fixture and its data before proposing any bulk byte feature.

### Context and whole-message identity

Let `Γ` be the independently authenticated actual activation, sender side,
receiver side and envelope kind for one matched send/receive delivery. It is a
proof context from N1/N4's actual operations and control path, not a source
integer or a field self-reported by the bytes. Relate the relevant ledger
owner/allocator labels to that activation and the authenticated sides. Define
`canonical_Γ(m, b)` only for admitted messages whose kind and endpoints agree
with `Γ`: Work uses Application, and its omitted `WorkOut.destination` is the
actual authenticated receiver of `Γ`; Ack uses Control, and the encoded parent
address identifies that actual receiving owner. The checked driver separately
establishes these relations and the expected current ledger output; encoding an
owner or child integer cannot authenticate it.

The proposed ordinary decoder can return the parsed Work fields and payload;
the checked driver attaches the receiver from `Γ` when relating the result to
the whole Work message. Its frame has no explicit destination field. Thus
whole-message roundtrip is a law *within this fixed context and admitted
message domain*, not an uncontextual claim that bytes recover destination.
The same `Γ` must relate the actual encoded send and copied receive, including
correct polarity and peer. A wrong side, sender, kind or activation supplies
no protocol fact even when the bytes parse. The Ack sender must additionally
match the recorded child destination under the N4 transition/peer rule.

### Proposed law

Let `encode` and `decode` denote actual nominated linked functions. Define
`parsed_wire(fields, b)` independently of `Γ`: the exact returned fields and
payload parse from the canonical tagged frame above, with the whole input
consumed. Let `canonical_Γ(m, b)` be the contextual whole-message relation
above. For each admitted input and actual normal return:

1. If actual encoding of admitted whole message `m` returns `b`, the encoder
   judgment derives its exact canonical wire fields and bytes. Given the
   independently established context/domain relation, this yields
   `canonical_Γ(m, b)`. If actual decoding of `b` succeeds with `fields`, the
   decoder judgment itself derives `parsed_wire(fields, b)` and complete
   consumption; neither `parsed_wire` nor `canonical_Γ` is a caller premise.
   Given independently established `Γ` and its domain/endpoint premises, the
   checked driver attaches the actual receiver where required and derives the
   corresponding `canonical_Γ(m, b)`. Malformed or noncanonical input, failure
   or absence of a normal return emits no decoded protocol fact.
2. For a fixed authenticated context, the mathematical relation is functional
   in both directions over its admitted domain: every admitted whole message
   has one byte sequence and every accepted sequence has one whole message.
   With sufficient resources and established provider/control premises,
   decoding an encoded admitted message returns the same fields; attaching the
   same actual receiver gives the same whole message. Allocation or evaluation
   failure does not imply a successful decode or re-encode.
3. The actual committed transport copy preserves those exact encoded bytes, and
   the decoded result is attached to its actual `Message` and authenticated
   kind/peer. N4 separately proves reservation, emission, actual completion,
   transition and driver confinement. The codec supplies data correspondence,
   not honest acknowledgement, release or settlement.

This is normal-return soundness, not unconditional termination. For finite
nonnegative mathematical inputs and absent limits, the digit writer terminates
by strict decrease of the quotient, and the reader by advancing its bounded
cursor. Runtime work/storage refusal, selected interpreters and nonreturn remain
observable. Negative/unrepresentable values and unsupported forms confer no
successful protocol fact.

## Minimum actual-definition reconstruction

Nominate the actual linked encoding/decoding functions for the Work and Ack
variants and their helper closure. The checked definition may recognize
the following ordinary functions, using the separately accepted integer
split dependency and without new protocol primitives:

| Actual linked component | Required checked relationship |
| --- | --- |
| Natural writer | On `n == 0`, append marker `00`; otherwise apply the exact separately checked split to the same `n`, append marker `01` and actual remainder byte, and recurse on the actual quotient. Each positive quotient is strictly smaller than the input. The returned whole Bytes is the original prefix followed by exactly `U(n)`. Negative or failed split is no success. |
| Natural reader | At the actual advancing cursor, read a group marker with `Bytes.at`. `00` ends the scalar, accepting no digits as zero or a nonzero final most-significant digit; `01` requires one following digit and advances again. Accumulate the value using the actual digit and canonical mathematical `+` and `*`, keeping the correct power of 256. Reject a malformed marker, missing digit, noncanonical final zero, or `InvalidIndex`. Finite remaining bytes establish progress. |
| ID/address functions | Match the actual nominal constructors and write/read the distinct tags, then exact allocator, serial and owner fields in order. Check the actual nested helper arguments, branch defaults and returned constructor operands. |
| Payload copy | Use canonical `length` and `at`, and `append_byte`, on the actual input and destination. Iterate with a checked counter, preserve exact whole byte values/order, and stop only at the declared length; a short input or failed operation supplies no successful result. |
| Frame encoder/decoder | Check variant tag, all field/cursor threading and every result branch. The decoder accepts only at actual cursor equality with actual `Bytes.length`; it cannot ignore, reinterpret or silently skip a suffix. Bind its actual returned whole message and the encoder's actual returned Bytes. |

These definition shapes describe a supported route, not an existing implementation
or an exhaustive specification of alternative algorithms. Require the validator to
reconstruct exact linked nodes, nominal identities, strict operand order,
helper/capture binding, actual success and failure branches, and acyclic helper
dependencies. Recursion is admissible only with a checked progress measure and
its established finite/nonnegative premise. At each byte primitive and integer split check the
canonical intrinsic and its actual result constructors, live bytes and indices,
selected allocation provider and all intervening effects/reentry. Reuse the
existing linked-initializer, match/constructor, helper dependency, budget and
provider/control analysis where their present rules apply; add only the byte,
integer-cursor and complete-frame judgments needed for this codec. No second
Core evaluator or general source-program equivalence checker is proposed.
Unsupported helper, selection, transformation or captured call rejects before
an N4 fact is consumed.

The actual-definition evidence must connect each accepted judgment to the
existing Core evaluation and M2 allocation/byte-operation behavior, including
`RegionBuffer` lowering where applicable, and prove the normal-return laws
above for each supported rule. Record the exact trusted Rust-to-model mapping;
a Lean theorem about an ideal codec is not a proof of that mapping, the Rust
checker or native transport. Recheck linked bodies, imports, specialization and
other supported transformations before use. Charge discovery, traversal,
recursion, byte lengths, arithmetic, result allocation and retained facts to the
existing cumulative budgets before proportional work or allocation; exhaustion
cannot publish a partial claim or restart with a hidden allowance.

## Semantic delta

This accepted proposal extends CP-0028's conditional checked
ledger contract with the specified canonical framing and actual-definition
codec correspondence. It adds no inference from byte contents to authenticated
peer, envelope kind, completion or release. The fixed framing is proposed for
this restricted codec; CP-0027's channel still transports opaque bytes.

## Affected specification areas

The eventual integrated change affects [name resolution](../../spec/name-resolution.md)
for the linked canonical builtin identities, [static semantics](../../spec/static-semantics.md)
for the bounded checked facts and their control and lifetime premises,
[elaboration](../../spec/elaboration.md) for actual linked reconstruction, and
[dynamic semantics](../../spec/dynamic-semantics.md) for the corresponding
ordinary byte, allocation and operation behavior. The separately accepted
integer dependency identifies its own additional semantic delta.

## Resulting specification truth

After acceptance, completed implementation and Main integration, only a
checked actual definition satisfying the stated premises may establish the
normal-return codec correspondence. Its use is conditional on the actual
transport, context, provider and control relations. It does not establish
completion or release by itself. Until then this proposal describes no current
Ash semantics.

## Interactions

CP-0029 must be implemented and verified before dependent codec implementation.
The N3 ledger facts and N4 driver supply independent state, peer and control
premises. Existing authenticated envelope kind is
Application or Control; the N2 send path produces Application. N4 still needs
a checked Control producer and confinement. Measure persistent byte append
cost on the actual fixture before proposing a bulk-byte change.

## Non-goals

No general serialization library, native codec, general byte cursor API,
scheduling progress, universal transport of Ash objects, automatic trust in
decoded data, or N4/N5 completion. If the measured cost, available semantics
or checked fragment cannot support the driver, return to proposal review.

## Required evidence

At a frozen linked input, demonstrate valid Work and Ack encoding/decoding,
Root and Work IDs, zero, 255, 256 and numbers beyond host word size, parent and
child field identity, and exact payload bytes. Reject a noncanonical final zero
(for example `01 00 00`), an invalid group marker, wrong authenticated context
and actual linked same-typed altered
body, wrong helper/capture/nominal identity, wrong field order, invalid and
truncated tags/scalars/payloads, ambiguous or noncanonical encodings, suffixes,
negative or unrepresentable values, wrong selected provider, failure and
exact/one-short/already-spent budgets with no partial publication. Include
independent imports, reexports and supported transformations, and demonstrate the
actual copied transport bytes and tagged peer relationship in the integrated
driver. Review the proof, implementation mapping and tests independently at
matching source/configuration pins. This list states acceptance evidence, not a
claim that any such test was run here.

Independent review of the accepted metadata and its retention precedes
implementation. Required implementation and evidence remain open; none is
claimed here.
