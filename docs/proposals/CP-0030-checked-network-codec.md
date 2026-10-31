# CP-0030: Network codec

- ID: `CP-0030`
- Status: accepted
- Related: [CP-0027](CP-0027-pinned-workers-and-copied-channels.md), [CP-0028](CP-0028-checked-functional-network-ledger.md), [CP-0029](CP-0029-exact-base-256-integer-split.md), [TASK-0058](../tasks/TASK-0058-pinned-worker-network.md), [issue #79](https://github.com/dikini/ash-lang/issues/79)

> On 2026-10-31 the user superseded the compiler-derived codec-law approach.
> The accepted direction is ordinary Ash protocol code and ordinary error
> handling over the existing network bridge. This proposed transition is not
> current Ash or a claim that the codec and driver are integrated.

## Current behavior

The [byte module](../../spec/name-resolution.md#independent-byte-and-string-modules)
provides immutable `Bytes` and checked byte operations. Accepted
[CP-0029](CP-0029-exact-base-256-integer-split.md) supplies the proposed exact
base-256 split; its implementation must be available on the delivery branch.
The existing [`network_codec.ash`](../../libraries/network_codec.ash) and
[`network_types.ash`](../../libraries/network_types.ash) are ordinary library
code, not a completed network delivery. Transport authenticates envelope kind
and peer, not the meaning of bytes.

## Proposed behavior

Use the following ordinary-Ash format for this Work/Ack program; it is not a
new language or native transport format. Byte values are hexadecimal.
For a nonnegative mathematical integer `n`, `U(n)` is little-endian base-256:
each digit is `01` followed by its byte, and `00` terminates. Zero is `00`;
the most significant digit of a nonzero value is nonzero. For example,
`U(1) = 01 01 00` and `U(256) = 01 00 01 01 00`.
There is no machine-word bound in the representation.

Let `ID(Root) = 10`, `ID(Work(a, s)) = 11 U(a) U(s)`, and
`Addr(owner, id) = U(owner) ID(id)`. Frames are:

- Application Work: `20 ID(child) Addr(parent) U(length(payload)) payload`.
- Control Ack: `21 Addr(parent) ID(child)`.

The declared payload length is exact and successful decoding consumes the
whole frame. Unknown markers or tags, noncanonical scalars, truncation, extra
suffixes, negative or unrepresentable inputs, and byte-operation failures
produce ordinary encoding or decoding failure. Root is representable; the
program's work and Ack handling must use values appropriate to their roles.

The Work encoding omits destination. The receiver is obtained from the actual
transport context, not inferred from bytes. Ack handling uses the actual
sending peer with the stored child destination. A successful parse does not
by itself imply an authentic peer, completed work, permission to release or
host settlement. Allocation and evaluation failures remain observable.

## Semantic delta

The former requirement that the compiler nominate linked bodies and derive
conditional codec laws, provider/capture closure and protocol facts is
superseded. No compiler evaluation, transformation, lifting or runtime
verification framework replaces it. Codec behavior is implemented and tested
as ordinary code, with ordinary failure handling. The byte and integer
operations retain their own existing or separately accepted contracts.

## Affected specification areas

The eventual specification update describes implemented byte/integer and
network behavior only where changed, after integration. This proposal does not
make any new Ash semantics current.

## Resulting specification truth

The delivered implementation can document the actual codec format and its
errors at its library boundary. It must distinguish application interpretation
from the existing transport's authenticated origin and settlement.

## Interactions and non-goals

CP-0029 is a dependency of the selected encoder. CP-0028 supplies the ordinary
Work/Ack program and its completion outcomes. This proposal does not add a
native codec, new parser primitive, source proof, automatic trust in decoded
bytes, or scheduling and completion guarantees.

## Required evidence

Exercise actual Work and Ack encoding and decoding, both ID forms, zero, 255,
256 and values beyond a host word, exact payload and fields; exercise invalid
markers and tags, noncanonical digits, truncation, suffixes, failed byte and
integer operations, and wrong envelope kind or peer in the connected program.
Observe actual copied bytes through the native bridge. Test imports and the
supported production build path as applicable; malformed protocol data is an
ordinary runtime error or no-op, while generic static failures remain static.
Record focused commands, frozen inputs and results, and independently review
the connected public path. Prior codec model and checker receipts transfer only
within their original scope.
