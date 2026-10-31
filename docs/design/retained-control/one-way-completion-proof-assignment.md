# One-way receive completion: bounded checker and proof assignment

> Historical assignment: the one-way protocol completion checker was
> superseded on 2026-10-31 and is not a current release requirement.

This assignment specifies the one-way section of
[CP-0027](https://github.com/dikini/ash-lang/blob/b3e16b7c31d55850ab6f879286a594b4f6cb2540/docs/proposals/CP-0027-pinned-workers-and-copied-channels.md#one-way-receive-completion-refinement),
independently reviewed at `1e336f6c0c292b48696e5bf61a24408d7a98268f` and
accepted as a contract at that checkpoint. Its allocation-free caller cut and
rule-by-rule bounded proof were proposed for that transition; this assignment is not a proof, implementation,
language restriction or permission to release a network. The retained
[worker/channel model](worker-channel-correspondence.md) supplies the target
transitions, and [C3 correspondence](drain-correspondence.md) describes the
existing actual Store and completion analysis. N3/N4 remain independent.

## Finite domain and identity

Reconstruct the actual linked Core after transformations, including imports,
resolved definitions, selected evidence, effect instances, handler selection,
captures and reachable control successors. Analyze one actual receiver owner
and its lexical network acquisition at a time. A certificate is bound to the
current `N`, receiver polarity, actual sealed operation and full control
successor, not merely to a type, port, source name, function signature or result
constructor. Runtime activations may repeat the same static acquisition: the
soundness relation must instantiate the abstract owner to the actual fresh
activation and may not equate distinct activations.

A finite full analysis state contains:

- the actual control node, calling/handler/cleanup context as represented by
  the existing normalized capture graph, and the associated `N` and side;
- a receive fact `none`, `message`, `empty` or `end`, with its actual sealed
  operation/result edge; only the last represents genuine End;
- a delivery phase `clear`, `processing`, `pending`, or `unknown`. In
  `processing`, a symbolic current delivery stands for the fresh actual held
  entry and its matching C1 branch/root; `pending` covers a retained root,
  callback, cleanup or other unfinished processing. A phase is not a runtime
  delivery identifier or a source value;
- the existing C3 work projection for the same Store (`Empty`, `ActiveOnly`, `Pending` or
  `Unknown`), plus the selected active root, handler/clause continuation,
  captures, live slots and cleanup/callback dependencies needed to validate it;
- an escape bit and the finite set of message-derived value/capture sites and
  reachable checked caller suffixes. Unknown aliasing, target, capture or
  dependency sets the bit. C3 work and this data are analysis facts, not a new
  language resource state.

`clear` means that this loop frame has no outstanding delivery, not that every
network or Store is globally empty. Entry is `clear` with no End fact, and only
when the selected C3 Store entry satisfies the existing admission checks. The
finite analysis must not merge two owners or two full caller/handler contexts
because their projected work or ports match. Dynamic recursive frames need not
be counted: each frame is separately related to the same finite checked summary
and must satisfy the cut and inert-suffix rules before it recurses. The proof
must induct over actual frames, rather than assume a bounded runtime stack.

## Transfer and normal-return rules

The following are acceptance rules; a proposed implementation must prove that
its actual evaluator and capture graph follow them. Where a rule's preconditions
cannot be established, reject the completion path. An ordinary runtime failure
continues through its own failure/settlement path and establishes no successful
End or release fact.

1. **Receive.** A checked sealed receive at the matching `N` and side splits
   only into its actual `Message`, `Empty`, `End` and failure outcomes. A
   successful Message commit moves `clear` to `processing` with a fresh
   symbolic delivery and the actual receiver-held identity; payload-derived
   aliases start in the message-derived set. Empty preserves `clear` and cannot
   create End. End preserves `clear` and records the authenticated control
   edge only after the host has observed sealed-and-empty End. Failure forgets
   all success facts. A receive from another owner or a source handler's value
   is not this event.
2. **Processing.** Follow every reachable branch and actual call in the
   processing region, propagating the message-derived set through values,
   arguments and captures. Any store into an outer cell, returned value,
   unknown callee, saved closure, asynchronous callback or other location
   reachable after the cut sets escape. A call may preserve a clean state only
   with an independently checked summary for its actual target and evidence;
   native bindings may do so only on their actual synchronous return under the
   binding premises. A Retain, unresolved callback, live cleanup or C3 work
   that is not proven finished sets `pending` or `unknown`; `ActiveOnly` still
   denotes the currently executing fresh root and cannot authorize the cut.
   A later transfer clears outstanding work only at its corresponding actual
   completion, never at issuance, handler disappearance, polling or another
   receive.
3. **Cut.** On a normal processing successor, move `processing` to `clear`
   only if the *same* delivery's actual selected root reaches the C1 finish
   marker, its active branch and consumer match, and the C3 query for that
   Store establishes Empty after the actual handler/clause suffixes and owned
   cleanups return. No message-derived value, capture, callback, slot, cell or
   returned value may escape, and the still-reachable caller suffix must pass
   rule 4. All normal predecessors of a join must establish these conditions.
   No static position or guessed `ReadyToFinish` is sufficient. A failed or
   incomplete marker supplies no normal cut.
4. **Inert recursive suffix.** The continuation after the loop call may consist
   only of actual checked allocation-free Core aliases, construction and
   projection used to forward the distinguished End-success return to its
   matching caller, followed by normal return. Every operand must be independent
   of the message and its captures. No admitted node may allocate, invoke a
   provider, perform an effect, call arbitrary code, access mutable state or
   run an endpoint operation, callback, cleanup or saved continuation. Analyze
   all actual branch successors and free variables. A source constructor that
   lowers to allocation or provider control is not admitted by apparent purity;
   it requires a separately reviewed nonreentry rule. Processing within the
   completed root may allocate under its own checked rules. Unsupported nodes
   and unknown captures fail the check; neither tail syntax nor a constructed
   value mints the End control fact.
5. **Loop and return.** A Message arm can call the same checked loop only after
   rule 3 and with rule 4 established. Empty may call it from `clear` under the
   same inert-suffix restriction. The End arm may return End-success only with
   the authentic current End fact, `clear`, no escape, and C3 Empty. A matched
   return may propagate that control fact through a rule-4 suffix to the actual
   call successor of the same activation and side. A helper's value, a normal
   return on a different branch, a different call site or an unmatched frame
   cannot propagate it. At `finish_receive`, every reachable normal predecessor
   must carry that fact for the current side, have `clear`, no escape and no
   unresolved C3 work or older uncertified frame. Invalidate the fact on an
   unknown call, changed owner/side, unsupported capture, failure, endpoint
   operation that consumes it, or any unverified successor.

The fragment does not claim arbitrary safe helper programs are rejected as
unsafe at runtime; it rejects their normal completion proof until another
sound rule is accepted. It does not infer termination from an Empty retry or a
recursive call. In particular an unreturning loop has no End-success return.

## Joins, calls and fixed point

At a join, intersect authenticated facts: `end` survives only if every
reachable predecessor has the same owner, side and sealed End provenance;
otherwise it becomes `none`. Union possible message dependencies and escape
bits. Join unequal phases conservatively: `clear` with any outstanding phase
is outstanding; ambiguous roots, targets or pending kinds become `unknown`.
The C3 projection joins using its existing conservative work rules. No join may
combine one predecessor's End with another's cleared obligation.

A call summary is indexed by its actual resolved linked target and selected
evidence, normalized full entry context, owner/side and finite input state.
Its possible normal returns are pairs of that full entry with a matching full
return context, returned control fact and output state. It is not a Boolean
attached to a function name. Snapshot actual argument/capture reads before
formal assignment; discard stale aggregate origins at calls and returns as C3
requires. Recompute or invalidate on changed value closure, selected evidence,
call target, capture or control successor; requeue all dependent requests.
Unresolved calls or operands and unsupported imports/transforms refuse the cut.

Initialize the set of possible normal-return pairs to **empty**. Add only
pairs justified by an actual normal-return successor or by composition with an
already established matching pair. Iterate the monotone successor and summary
rules over the finite normalized state and finite pair universe to the least
fixed point, replaying value-dependent call/owner requests after every relevant
revision. A cycle, including mutual recursion, supplies no return by itself.
A reachable failure is represented separately and never upgrades a successful
summary. At successful queue exhaustion, all final-closure one-step successors
and matching return requests from visited states must be accounted for. Charge
all construction, propagation, joins and replay to the existing cumulative Core
budget; allocation failure, exhaustion or unresolved closure gives no proof.
This is a bounded query, not a termination claim for source execution.

## Required proof and correspondence

Mechanize the finite analysis and its real control-step relation, not an
abstract successor with the desired invariant assumed. Establish:

1. The seed and every actual reachable matching successor are represented;
   revision replay and finite closure cover all final-closure call targets,
   returns, captures, branch and failure edges. Prove least-fixed-point and
   matching-entry/return soundness, including arbitrary finite recursive frame
   nesting. An empty initial return relation grants no fact from a bare cycle.
2. Each receive transfer is tied to the sealed interpreter's actual `N`, side,
   committed delivery identity and genuine End event. Relate each live actual
   delivery to a distinct held entry; preserve this relation through queue,
   copy, processing, callback, cleanup, capture, recursion and failure steps.
3. For each accepted processing and cut rule, show that the selected actual
   control steps reach the matching C1 `Step.finish` with `ReadyToFinish`, and
   that the existing C3 same-Store predecessor and suffix/cleanup conditions
   imply the required actual completion. Show rule 4 excludes future work
   derived from that delivery in *all* older recursive frames, including
   values and captures. No premise may state the desired cut, release or
   successor invariant as a substitute for these proofs.
4. Map the cut to `WorkerChannel.NetworkStep.finishProcessing` for that same
   held `e`, branch and consumer, with its existing preconditions; use its
   preservation theorem to remove that entry once. Prove all other accepted
   transitions preserve the held-obligation relation and that failure cannot
   fabricate a successful finish. For finish_receive, derive every earlier
   held delivery discharged and actual End from the full-state trace, rather
   than treating empty queue or helper return as completion. Explicitly audit
   any difference between the model's one active C1 capture and actual runtime
   concurrency; missing correspondence refuses this proof.
5. Independently reconstruct the actual linked analysis after each supported
   transform and import, then prove accepted call/return summaries apply to
   those exact definitions, evidence and successors. Runtime mapping of the
   actual completion marker, native binding synchrony/visibility, transport
   commit and wake behavior remain explicit independently validated premises;
   they are not established by Lean source compilation.

The source gate, runtime/OS/native correspondence, independent proof review,
product tests and N-core gate are separate. Failure of any yields no release
permission. No built-in ledger, source proof syntax or new general resource
state is introduced by this assignment.

## Required source and Core controls

A positive fixture has a receiver loop with `Empty` retry; each `Message` is
fully processed inside a completed local root before recursion, with an inert
caller suffix; genuine End returns the distinguished End-success path and the
caller finishes. Include an imported helper and a synchronous native call
under its actual binding premises. Exercise multiple messages and recursive
frames, including Empty before and between them. A loop with no normal-return
base must produce no End-success summary.

Reject normal completion when a message is processed after the recursive call,
a nested `finish_receive`, or an End return; when any older arm has such a
suffix; when message data escapes through a cell, result, saved closure,
callback or Store entry; or when cleanup, a callback, a retained slot or active
C3 work remains. Reject a fake End, wrong activation/side, intercepted receive,
helper return with later work, an allocating or provider-invoking forwarding
suffix, unknown callee or a same-typed substituted helper whose actual body
violates the fragment. Include changed selected
evidence, imports, transformations, stale state and finite-budget exhaustion.
Check failure paths independently: a failed send, receive, marker, callback or
native operation must never manufacture normal completion or release. Tests
must assert the actual linked definition and source shape that triggered each
result, not just compare function names or precomputed summary flags.
