# Initial provider reference cases

> These are experimental scenarios under
> [DN-0036](../DN-0036-foreign-library-and-memory-provider-experiments.md).
> Expected admission and observations are comparison criteria, not test results
> or current Ash semantics. The named steps are scenario notation, not syntax.

Each case has a positive program and a nearby negative or failure variant.
Native error cases are valid checked programs with a failure outcome; prohibited
access cases should reject before entering native code. When a candidate cannot
establish a required fact, record that limitation instead of running unsafe use.

The first source fragment and trace notation are described in
[semantics](semantics.md). Operation requirements come from
[contracts](contracts.md). Stable IDs below refine DN-0036's SQL and MEM cases.

## SQLite baselines

### S-01: connection and statement lifecycle

Acquire a connection, prepare `SELECT ?1`, bind integer `42`, step to a row,
read `42`, step to completion, finalize, and close. Return the copied integer.
Repeat with two live connections and with another activation at the same source
site. Access must select the declared instance, not the most recently acquired
connection.

Positive expectation: the copied result remains valid and each statement
completes before its connection. Negative variant: use a statement after its
scope completes or mix connection/statement instances. Checking rejects and
relates the use to the owner. Covers SQL-01 and SQL-08.

### S-02: establishment and empty input

Fail to open a database in an exclusively owned nonexistent directory; also
prepare malformed SQL. Record native errors separately from injected allocation
or publication failures. Try empty SQL as a distinct case.

Positive expectation: failure reaches the declared outcome with no published
client authority; partial native state is disposed of. Empty preparation uses
its specified no-statement outcome. Negative variant: enter the acquired body
after failed open or treat empty preparation as a usable statement. Reject
unjustified authority. Covers SQL-02 and SQL-05.

### S-03: copied input and output bytes

Bind bytes `[1, 2, 3]` with the copying operation, end the input storage's valid
interval, execute `SELECT ?1`, copy the result, complete the statement and
connection, then read the independent copied bytes. Run empty bytes and SQL null
as distinct inputs.

Positive expectation: the result preserves byte contents and distinguishes
empty bytes from null. Negative variant: use a shallow alias as the escaping
result while calling it an independent copy. Reject the remaining dependency.
Record bytes actually copied. Covers SQL-04, SQL-05, and MEM-04.

### S-04: protocol and completion reports

Run a constraint-violating statement and retain its body error together with
the finalization report. Contrast finalization that consumes a statement with
refused connection close that leaves its owner live. Use a native reference
harness, not an admitted Ash client, to observe the refusal contract with a
deliberately unfinished dependent statement.

Positive expectation: outcome handling preserves those different postconditions.
Negative variants: column access before a row, retry through a consumed
statement, or treating refused close as completed ownership. Reject or require
the stated runtime protocol check; never expose an invalid pointer. Covers
SQL-05 and SQL-07.

### S-05: external persistence and importing helper

An importing client asks a generic helper to insert `42` into a temporary file
database, closes it, reopens it, and reads `42`. Compare client checking with
the provider/helper body present and with only its authenticated public contract.

Positive expectation: persistence is observed and public relationships are
sufficient for client use. Negative variant: omit or forge the provider contract
or erase a stored owner dependency from the summary. Reject at the owning
validation boundary. Covers SQL-08 and SQL-09.

## Arena baselines

### M-01: exact capacity and failed publication

For a recorded object layout, acquire exactly the capacity needed for two
objects plus padding. Allocate and read both, then attempt a third. Repeat with
one byte less, excessive alignment, overflow in layout arithmetic, and the
chosen zero-sized-object policy.

Positive expectation: failure preserves previous objects and the promised
cursor state; no partial reference is published. Negative variant: use access
produced by a failed reservation or an incompatible typed layout. Reject forged
access; native validation guards dynamic layout facts. Covers MEM-01.

The A-0 [allocation suite](../../../tests/provider_arena_allocation.rs) makes
this source milestone concrete: store/load Int 41 to an independent result
after completion; admit Int and Bool in one arena; preserve an earlier object
after byte/slot, alignment and signed-64 conversion refusals; distinguish
zero-extent Unit records from alignment padding. The selected seven-case public
suite now passes, including actual native storage and ordinary source overrides;
[scalar results](arena-results.md#actual-storage-and-control) retain the receipt
boundary. This does not admit the wider stored-payload and graph cases below.

### M-02: immutable sharing and captured values

Allocate an immutable node containing `41`; alias it twice, build a persistent
structure sharing it, and capture an alias in a closure called twice inside the
arena. Record one payload identity and the number of allocations. Keep a cyclic
shared-graph scenario as a later construction case if the first fragment cannot
form it safely.

Positive expectation: aliases observe the same object with no payload copy.
Negative variant: return the capturing closure after arena completion, even if
its exposed type mentions only `Unit -> Int`. Reject its retained dependency.
Covers MEM-02 and MEM-03; cycles are pressure, not a completed initial result.

### M-03: nested arenas and safe projection

In outer arena A allocate node `41`. In inner arena B allocate a tuple containing
an A reference and a B reference. Project the A reference and use it after B
completes, while A remains live.

Positive expectation: the projection depends on A only. Negative variants:
return the whole tuple, project its B reference, or store a B-dependent closure
in surviving A storage. Reject the B dependency. Covers MEM-03.

The later A-0 [source-refusal counterexample](../../../tests/fixtures/provider-experiments/arena-typed/inner-owner-source-refusal.ash)
intercepts the exact A storage instance inside B and retains nothing in A.
Its allocation clause always refuses; its load clause returns the live B Ref.
It must not inherit an unselected native-store obligation. Placement of an
exact generated fallback whose payload mentions B remains unresolved in the
[remaining obligations](arena-results.md#costs-and-assumptions).
The fixture is unexecuted; no useful-case admission is claimed.

### M-04: independent copying

While A is live, copy an admitted shared value into ordinary recipient-owned
storage or an enclosing arena B. Complete A and use the result while its
recipient remains live. Record whether sharing is preserved or duplicated.

Positive expectation: the copied result has no A dependency under the specified
deep-copy contract. Negative variant: copy only the outer aggregate while
retaining an A reference. Reject escape. General cyclic copying remains a
separate contract question. Covers MEM-04.

### M-05: owner restriction and scratch retention

Acquire and complete a scratch arena repeatedly; independently owned scalar
results remain usable. Compare peak payload bytes and separate metadata costs.

Positive expectation: completed storage is reclaimed with the promised order.
Negative variants: return the arena owner, package it with an object, or extend
its source lifetime by counting references. All are excluded and must reject.
Covers MEM-07 and MEM-08.

### M-06: completion using storage

Retain a cleanup action that reads arena-backed data. Arrange nested ownership
so the action completes while the arena is live. Repeat through capture/resume
and checked abandonment of the owned scope.

Positive expectation: cleanup use precedes storage release. Negative variant:
discard a capture that skips required outside completion or reclaim storage
before a pending action. Reject the unsafe completion. Covers MEM-06 and SQL-06.

## Shared foreign-memory cases

### X-01: retained input and the release point

Acquire arena A outside the connection and statement scopes. Allocate bytes
`[1, 2, 3]`, bind them with retained access, and execute. End that retention by
the specified rebind, clear-bindings, or finalization operation; then mutate or
complete the input storage where its access contract permits.

Positive expectation: the foreign address, contents, and owner remain valid
through every retained use. Negative variants: complete A, mutate its borrowed
bytes, or infer retention release from reset alone. Reject conflicting use.
Compare allocation, copying, and retained bytes with S-03. Covers SQL-03.

### X-02: temporary output and a live owner

Step to a row, obtain a scoped byte view, inspect it, finish its admitted access
interval, then continue statement execution. The statement owner remains live.

Positive expectation: access follows the narrower interval. Negative variants:
step, reset, finalize, or perform an invalidating conversion through an alias
while the view remains usable. Reject the conflict even though the statement's
owner is live. Copying the view before continuing is the positive alternative.
Covers SQL-04 and MEM-05.

### X-03: captured conflicting access

Inside a scoped shared or exclusive borrow, perform an outward resource-free
request. A surrounding handler can reach another alias of the borrowed owner.
Compare a handler that resumes without conflicting use with one that mutates
or invalidates through that alias before resumption.

Positive expectation: capture preserves the access obligation until its use
ends. Negative variant rejects conflicting handler access; single-use resume
does not by itself resolve the alias conflict. Covers MEM-05 and MEM-06.

### X-04: combined close order and typed reporting

In the composed retained-input case, abandon a captured body through checked
discard. Record dependent statement completion, connection completion, actions
that need arena data, and arena release in the valid structural order.

Positive expectation: every required action has its interpreter and storage.
Negative variants: close an outside owner, skip a running action, or report a
consumed owner as still callable after an error. Preserve native postconditions
and reject unsafe abandonment. Covers SQL-06, SQL-07, and MEM-06.

## Slice assignments and records

S-01 through S-05 and the storage portion of M-01/M-02 are native baselines.
Their type rejection variants need the source slice. M-03 through M-06 need
source relationships and control. X-01 through X-04 are the first composition
slice; implement them only after their access rules have been reviewed.

For each run retain the fixture, phase, candidate, outcome, diagnostic source,
inferred/explicit contract facts, Core trace, native events, copying and storage
costs, and unresolved assumptions. A case can be unimplemented, admitted,
rejected, or inconclusive for a named candidate. Never count an unimplemented
negative case as a successful rejection.
