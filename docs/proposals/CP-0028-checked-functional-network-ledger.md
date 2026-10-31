# CP-0028: Functional network ledger

- ID: `CP-0028`
- Status: accepted
- Related: [CP-0027](CP-0027-pinned-workers-and-copied-channels.md), [CP-0030](CP-0030-checked-network-codec.md), [AD-0017](../decisions/AD-0017-pinned-worker-host-and-transport.md), [TASK-0058](../tasks/TASK-0058-pinned-worker-network.md), [issue #79](https://github.com/dikini/ash-lang/issues/79)

> On 2026-10-31 the user superseded this proposal's compiler protocol-checker
> approach: implement the protocol as ordinary Ash code using ordinary error
> handling and the existing network bridge. This accepted direction authorizes
> the transition below; it is not current Ash or a claim of implementation.
> Further semantic gaps return to proposal work.

## Current behavior

[Retained-control checking](../../spec/static-semantics.md#scoped-retained-control)
checks actual local completion and release. A Boolean or a copied identifier
alone does not discharge it. [CP-0027](CP-0027-pinned-workers-and-copied-channels.md)
is an accepted transition, not current language truth. Its network operations
provide copied transport and authenticated envelope origin; they do not
establish the meaning of application bytes or complete an Ash computation.
The retained N2 work implements part of that transition on the milestone branch.

The earlier revision proposed reconstructing linked protocol bodies, current
ledger facts, and codec laws in the compiler. Its N3 proof and checker evidence
are historical evidence for the model and the tested implementation only. They
do not establish the revised delivery or its native settlement.

## Proposed behavior

Implement Work, Ack, and drain in ordinary Ash using the existing language,
ordinary library functions and error handling, and the N2 native bridge. The
protocol's local data and transitions are program behavior, not new compiler
facts or a new verification framework. The existing
[`network_types.ash`](../../libraries/network_types.ash) and
[`network_codec.ash`](../../libraries/network_codec.ash) are starting points,
not evidence of a complete protocol. The linked driver must use the actual
transport kind and peer; payload bytes do not authenticate either.

Each worker maintains its local records, child obligations and pending output
using ordinary Ash values. A worker creates a fresh child identifier and
records both the child obligation and its outgoing Work before attempting
publication. A full channel leaves the output pending while the worker
continues receiving and servicing control. Receipt installs its local work
before processing. A parent remains covered while a child is outstanding.

After the actual local work and its cleanup finish, the worker closes that
work. A closed non-root record with no outstanding children can retire and
queue the corresponding Ack. The recipient removes a child obligation only for
the matching parent, child and transport peer; an unknown, duplicate or wrong
Ack leaves the obligation intact or produces an ordinary error. Once root
admission ends, the driver drains work and pending output, observes genuine
transport End, completes worker cleanup and uses the existing host settlement
path. A protocol error or a failed send must not be treated as successful work,
Ack, End, cleanup or settlement. Errors after publication or receipt must
preserve the applicable native outstanding-delivery and failure contracts.
These are required behaviors of the program and host, not assertions that a
new monitor proves them.

Use the actual current local state when continuing the ordinary program; a
copied older value is not a replacement for a later state. The first slice must
make its entry points, ownership and data flow concrete using existing Ash and
N2 facilities. It must not assume that hiding a constructor revokes an already
copied raw worker, that an arbitrary callback cannot retain an alias, or that a
new capability, version, reentry monitor or proof token exists. If existing
operations cannot express the required lifecycle, return the gap to this
proposal rather than weakening generic release checking or inventing a local
semantic rule.

## Semantic delta

This revision supersedes the former protocol-specific linked-Core discovery,
AST/body recognition, trace and current-state reconstruction, and their
pre-execution rejection and protocol release-fact requirements, including the
corresponding CP-0027 dependent checker requirement. It proposes no compile-time
execution, lifting, erasure, refinement or proof-token mechanism, and no new
runtime checking machinery beyond ordinary error handling. Generic type,
effect, resource and retained-control rules remain applicable. An ordinary
protocol result does not waive them or certify host settlement.

## Affected specification areas

The eventual integrated implementation must update the relevant network and
runtime sections of the specification, and any generic language section only
if an independently accepted semantic change requires it. This proposal does
not make CP-0027 or the revised protocol current on Main.

## Resulting specification truth

After implementation, review, verification and Main integration, the
specification can describe the implemented network and host behavior at its
actual boundary. It must not say that the compiler proves an ordinary
application protocol or that a successful ordinary result authorizes release.

## Interactions and non-goals

[CP-0030](CP-0030-checked-network-codec.md) describes the ordinary wire codec;
[CP-0029](CP-0029-exact-base-256-integer-split.md) supplies its integer
operation. Existing host transport, Store cleanup and carrier settlement remain
separate from application protocol state. No general network verification,
new protocol primitive, runtime checking framework, liveness, fairness,
deadlock-freedom, recovery or native memory-safety proof follows.

## Required evidence

Run an ordinary public capacity-one two-worker program where Work cleanup
produces a registered descendant, its Ack permits parent retirement and
upstream Ack, and the driver drains to actual End and host settlement,
returning `42`. Exercise Full and progress while
servicing reverse traffic, malformed input and unmatched or duplicate Ack,
failure without early release, actual cleanup, and native settlement with
outstanding obligations. Separately exercise existing generic static type,
effect, resource and retained-control failures. Reuse N2 and earlier receipts
only for the same tested boundary and matching inputs. Review the ordinary
program and connected native execution independently; record source pins,
commands, results, limits and performance under the task's plan. Producing
cleanup and final integration remain distinct gates.
