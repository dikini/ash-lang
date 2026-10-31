# Checked codec normal-return correspondence

> Historical evidence for the superseded codec checker; it does not govern
> the ordinary Ash codec retained on the milestone.

This is an argument for the accepted CP-0030 transition, scoped to the linked
codec matcher retained at `b94895c4db210cfd1817b21daed72e36ed7e4ee1`. It is not
current Main semantics or an independent proof about Rust. The actual invocation
must still satisfy the checked provider, capture, control and normal-return
premises. The matcher alone issues no protocol or completion fact.

## Scalar correspondence

Write `U(n)` for CP-0030's marker/digit representation of a nonnegative
mathematical integer. The checked writer's zero branch appends the terminator.
For a positive input, CP-0029's split gives `n = r + 256*q`, `0 <= r < 256`
and `q < n`. The checked `check_nat_writer` and `check_digits_writer` paths
append marker 1 and the actual remainder, then recurse on the actual quotient.
Induction on `(n, phase)` yields the original output prefix followed by `U(n)`.
Use phase 0 for the natural helper and phase 1 for the digit helper: natural
`n` calls digit `q < n`, and digit `q` calls natural `q` with phase decreasing.
For positive `n`, the final positive quotient input has quotient zero and a
positive remainder, so its final emitted digit is nonzero. Negative input
follows the checked failure path.

For the checked reader, after exactly `k` groups let the digits be
`d[0] ... d[k-1]`. The actual cursor is `c0 + 2*k`, the accumulator is
`sum(d[i] * 256^i)`, the power is `256^k`, and the last-digit state is the
last actual digit when `k > 0`. The entry initializes these to `0`, `1`, false
and `0`. Each successful marker/digit pair reads the actual input at that
cursor and cursor+1, updates the accumulator and power, then advances two.
Assume the actual caller supplies `0 <= c0 <= input.length`. Use phase 1 for
the marker step and phase 0 for the digit step: the step-to-digit call lowers
the phase at the same cursor; digit-to-step advances two and decreases remaining
bytes. The actual end branch consumes marker zero, accepts the
empty sequence for zero, and accepts a nonempty sequence only if its final
digit is nonzero. Unknown markers, missing bytes and a zero final digit return
invalid. Induction on remaining bytes and phase therefore derives `U(value)`
for the consumed prefix; canonicality is not a caller premise.

## Frames and actual Core

`check_identity`, `check_work_identity` and `check_address` reconstruct the
actual nominal tags, scalar calls, field order and returned cursors. The decoded payload
loop starts from the actual empty destination, reads one actual source byte,
appends it and increments both copied count and cursor. Induction on the
remaining declared length yields the exact source slice in order. The encoder
starts its corresponding copy with the already written header and appends the
whole actual payload to that prefix. Failure to read or append yields no
successful frame.

`check_work`, `check_ack` and `check_decode` thread those actual values through
the Work and Ack branches. Work's final cursor follows the declared payload;
Ack's follows its child ID. Both success branches compare that cursor to the
length of the actual original input, so success derives complete consumption.
`NoParent` and failed constructor/primitive branches do not return an encoded
success. The corresponding writer checks thread returned buffers in the same order:
Work is `20 ID(child) Addr(parent) U(payload length) payload`; Ack is
`21 Addr(parent) ID(child)`. These tags are hexadecimal. The scalar argument,
field order, exact payload and final comparison compose to equal decoded fields
for an admitted encoded frame on normal return. Quotient/remainder uniqueness,
distinct scalar markers and nominal tags, and the declared payload length give
a unique complete frame parse. Work destination is absent from the bytes; one
fixed authenticated receiver supplies the unique destination in that context.

The matcher reconstructs actual linked initializer, closure, captures, nominal
constructors, operands, branches and returns. Its source rules are in
[`src/core/codec.rs`](https://github.com/dikini/ash-lang/blob/b3e16b7c31d55850ab6f879286a594b4f6cb2540/src/core/codec.rs); the ordinary definitions
are in [`libraries/network_codec.ash`](../../../../libraries/network_codec.ash).
The trusted implementation correspondence uses the existing call-by-value
application order, `lower_buffer_intrinsic`, `return_region_buffer`, and
`prepare_buffer`: actual operands are evaluated before operation entry; byte
read/append use the actual bytes and checked index or byte; split uses the
mathematical integer and CP-0029 quotient/remainder order. Successful results
must be allocated and published under the selected saved Region owner. This
mapping assumes the separately checked linked Core, authentic provider and
nonreentrant control; work/storage refusal and nonreturn supply no result.

## Transport and context obligations

The N1 model moves one entry, including its bytes and identity, from queue to
received; it explicitly leaves Rust byte-copy and admission correspondence to
separate review. In the retained runtime, `NetworkTransport::try_send` copies
before enqueue. `reserve_receive` selects the opposite direction's FIFO head;
the same `ReceiveGuard` carries its sender, kind and snapshot. The machine checks
the sender against the opposite authenticated worker side, builds the Message
kind and bytes from that guard, and commits only after the receiver copy and
result construction succeed. These are concrete correspondence cases, not a
formal Rust proof or a conclusion about an arbitrary source-constructed Message.

A checked driver must still bind that actual committed occurrence and its bytes
to the decoded result, pair both actual worker initialization labels with their
activation and sides, and relate it to the corresponding checked send. Work is
Application and receives its destination from that context; Ack is Control and
its parent owner must identify the actual receiver. Ack's recorded child
destination must match the authenticated sender. Complete driver confinement,
current-state succession, copied-delivery correspondence, import/transform
revalidation and whole-program verification remain open. The retained private
receive fixture uses an Empty arm that returns false and does not establish
convergence for Empty retries.
