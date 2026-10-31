# N3 network ledger and checker proof assignment

> Historical assignment: the protocol-specific compiler checker was
> superseded on 2026-10-31 and is not a current product requirement.

This bounded assignment supported the then-accepted [CP-0028](https://github.com/dikini/ash-lang/blob/b3e16b7c31d55850ab6f879286a594b4f6cb2540/docs/proposals/CP-0028-checked-functional-network-ledger.md) and [TASK-0058](../../tasks/TASK-0058-pinned-worker-network.md). It is not current language semantics or evidence that a theorem has been proved. [DN-0056](../DN-0056-scoped-continuation-retention-and-library-scheduling.md#minimal-library-core-ledger-and-inductive-invariant) supplies the paper argument and [DN-0058](../DN-0058-pinned-worker-host-and-channel.md#proof-and-verification-obligations) sets the four N3 obligations. The then-proposed product implementation required an active assignment and the required evidence.

## Question and comparison

Can a bounded checker reconstruct the finite functional ledger laws and
successor-state facts from actual linked ordinary Ash definitions, and can its
accepted derivations be shown sound for modeled Core evaluation? Compare a
valid implementation with mutants that keep the same types and names but
change results, fields, control, dependencies, identities or state flow.
Success requires the complete laws and the checker soundness theorem below;
accepting the valid removal function alone is insufficient. Rejecting an
unsupported but correct implementation is permitted, provided the product
pipeline preserves a checkable form or refuses it. Retain the model and the
correspondence only if independently reviewed and reproducibly checked at a
frozen input; otherwise keep it as explicitly provisional evidence or discard
it. No experimental result alone authorizes product behavior.

## Model and theorem obligations

Use finite mathematical sequences of whole values for records, children and
outputs. Model nominal constructors and IDs, unique fixed worker allocator
labels within an activation, and unbounded integers. Define equality, lookup,
insert, update, `erase`, result status and ledger transitions explicitly. Do
not equate Ash's recursive type with finiteness: the correspondence must prove
that actual initialized state and each admitted successor have finite acyclic
representations. State the connection between modeled sequence equality and
actual whole-entry values without assuming decidable equality of payloads.

Prove the following, naming all preconditions in the theorem statements:

1. **Collections.** For finite unique keys, lookup returns precisely the
   matching whole entry. Removal returns the ordered whole-entry sequence
   `erase`, Found iff membership and Missing iff absence, preserves finiteness
   and uniqueness, and changes no unrelated entry. Prove corresponding
   insertion and update frame, membership, uniqueness and order laws. Include
   empty, head, tail, missing and duplicate-input precondition cases.
2. **Local ledger.** Initialization establishes the invariant. Every modeled
   registration, close, retirement and acknowledgement branch preserves it.
   Accepted registration installs a fresh child and matching output together;
   missing or closed parents do not change state. Closure preserves all
   unrelated fields and cannot reopen. Retirement removes only a non-root
   closed childless record and queues its correct acknowledgement. Wrong-peer,
   unknown and duplicate acknowledgements preserve the whole state. A matching
   acknowledgement removes exactly the intended child. Nonnegative serials,
   unique allocator labels and checked successor increments establish no
   reuse over finite histories, including retired IDs. Distinct activations remain distinct authority domains,
   even if their copied numeric IDs coincide.
3. **Network coverage.** Define a finite interleaving of workers, pending
   outputs, accepted and delivered transport and active or retained control.
   State the initial root and preservation invariant for rooted coverage and
   uniqueness of logical ownership. Prove by induction through reservation,
   publication, receipt, dispatch, actual completion, retirement, in-flight
   acknowledgement and matching removal. Explicitly assume actual local
   completion and source emission discipline, honest codec, authenticated peer,
   faithful transport and at-most-once dispatch. Prove stable AppQuiet from
   current root Closed/empty plus closed independent admission and absence of
   unaccounted producers. List precisely which premises supply each step; do
   not derive them from ledger functions. AppQuiet is not backing settlement.
4. **Restricted checker.** Define modeled syntax, well-formed linked
   definitions, call-by-value evaluation including nominal constructor match,
   verified equality and checked dependency closure, plan binding, rule judgments,
   reachable branches and actual returns. Prove each rule preserves its semantic
   interpretation. Prove that acceptance of `RemoveById` for the *bound actual
   body*, with finite unique input, implies every normal return satisfies all
   clauses of CP-0028. Use induction on the finite input and show that the
   recursive call has the checked proper tail and instantiated arguments and
   premises. Include checked helper calls and acyclic dependency ordering.
   Model actual Effect Core allocation and canonical integer increment, including
   authenticated default allocation selection, nonreentry and failure; prove
   that successful allocation preserves modeled state and resumes once. Refuse
   unsupported local providers, handlers or unknown selection rather than
   treating an empty row or erased allocation as purity.
   No assumed certificate may state the theorem being proved. Model nonreturn
   separately; normal-return soundness is not termination. Prove the same
   acceptance-to-evaluation theorem for *every* other schema able to publish a
   fact: equality, lookup, insertion, update, initialization, registration,
   closure, retirement and acknowledgement. Each theorem quantifies over the
   actual linked target and instantiation, admitted input and every normal
   return; it establishes every corresponding CP-0028 status, whole-entry,
   invariant, counter, output-envelope and frame clause on the returned value.
   Prove equality and checked helper dependency closure and establish each helper
   precondition at each call, then compose those theorems in acyclic order.
   The transition theorem must derive actual returned fields and envelope
   operands from checked evaluation, not substitute an ideal transition.
5. **State and control hook.** Define the relation between actual owner,
   activation, current input and returned successor at each control point.
   Prove checked transitions move currentness to the actual successor, no-op
   equality permits only its justified reuse, and possible mutation, stale
   captures, reentry and joins invalidate old observations. Show how retained
   exclusive control carries this relation as an explicit premise, and identify
   the N4 checks needed to establish that premise on linked programs. Model
   budget exhaustion as rejection with no published partial claim or permission.
   Prove acceptance-to-control-step simulation for each rule publishing a
   currentness, successor, equality, observation or invalidation fact. It must
   relate actual linked execution and returned successor values to the fact,
   and cover captures, calls, returns, reentry and joins, not merely prove a
   hand-written successor stream preserves an invariant.

A model that assumes its checker correct, restricts away difficult reachable
branches, omits helper purity or concludes completion from a Closed flag does
not satisfy the assignment. A model of an idealized evaluation is useful only
with an explicit, reviewed correspondence to the actual Core fragment.

## Correspondence and implementation evidence

Map each modeled construct, branch and premise to actual linked Core identity,
type, binder, scope, evaluation rule, call target, selected evidence, capture,
return and checker operation. Explain unsupported forms and prove or test that
they reject before any fact is consumed. Map plan decoding and candidate
discovery to untrusted inputs; show that actual bodies, not producer claims,
establish each fact. Document how constructor and equality semantics, finite
representation and actual output values correspond, and identify conditional
codec premises. Map the public sealed operation and the untrusted per-activation driver nominations to actual entry,
call and capture closure, including imported, indirect and reexported paths.
Show that unchecked raw send, receive, Control results and capability escape
reject, while ordinary N2 one-way operation remains admitted. Show how
imports, specialization, inlining and other transforms are rechecked at each
validation boundary, and how budget accounting charges all work and retention
before the operation. The proof does not by itself prove Rust, the evaluator or
native channel code; record the remaining trusted and external assumptions.

Run focused linked-Core tests on a valid ordinary Ash driver and ledger with
renamed binders, and independent imports and supported transformations. Include
mutants for altered retained phase/parent/children/destination, reordered or
dropped entries, wrong result tag, wrong key projection, whole-input recursion,
changed recursive arguments, cyclic or arbitrary list input, unverified or
handled-effect helper, circular dependencies, forged nominal identities and
same-typed changed bodies. Check missing/default arms, branch joins, no-op and
actual successor, rollback, reentry, stale observation, unresolved captures,
wrong or duplicate acknowledgements, mismatched envelope fields and peer,
application/control confusion. Codec-dependent admission remains disabled until
a separately accepted codec contract and its malformed/trailing-byte tests
exist. Check exact,
one-short and already-spent budgets, failed retries and no partial publication.
Tests must exercise the independently linked validator, not only a helper's
unit function. The valid alternative outside the fragment must reject rather
than inherit a prior fact.

Freeze source, proof toolchain, configuration and relevant linked inputs before
verification; record commands, outputs, hashes and review at the same pin.
The proof and connected implementation require independent review and the
N-proof gate. The N3 result is a conditional hook for N4; N4 must separately
verify actual local completion, source emission, raw publication confinement,
codec, transport and recursive application drain. N5 must establish settlement.
