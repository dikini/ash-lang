# Current failure paths after decoder-local Row reuse

These are the assigned read-only `55910` and `24841` observations on clean
`b3ba6a4bb4c108b905c078ac5cd90cdc13a2510d`, using the actual tested binary
`1ff2054ee56ff09594b550f972676a0770015dd750f1b5f9b9940bea5967f705`
(607776144 bytes). Both required canonical image tests remain failures. This
record locates executed boundaries; it does not establish a total deficit,
redundant work, or acceptance under a larger allowance.

The unchanged reviewed observer records 16 Row and 13 Access rows. Both naturally
close every measured phase and restore, with debugger exit 0 versus test exit
101. All mandatory breakpoints resolve. Source, script, tool and artifact pins
match before/after; direct children are reaped and owned groups absent. The
180+10-second, 1 MiB, 80-row and 20-frame limits are unchanged. There are no
inferior calls or writes, cap changes, rebuilds, retries or foreign execution.

- Row registry reconstruction consumes 46752; templates consume 158435. Final
  independent validation enters at root work 266236. Its first refused charge
  is on a Validator object's counter: used 61441 / limit 61444, request 5,
  through `effect_signature` and Type/Row substitution at `types.rs:4160`.
  The distinct root meter still reads 266236 at that stop; return debits it to
  327677. Counter identity is not inferred from matching values.
- Access registry reconstruction consumes 60911; templates consume 215043 and
  leave root work 323683. Final node reconstruction later exhausts the actual
  root meter at 327680, refusing request 1 while `Decoder::ty` reconstructs and
  canonicalizes a Row at `image.rs:9277`. No independent-validation entry or
  CoreAdmission conversion is observed for this case.

The second path shows raw Row reconstruction nested in a Type. It does not show
that the specific refused subtree was decoded earlier. Retaining completed nested
Row data would require actual repeat evidence and exact per-subtree depth;
the whole traversal's maximum depth cannot simply be assigned to an arbitrary
subtree. Pending/fact contexts remain cold, and their applicability is not
measured here. No new repair or proof-sharing authority follows from this trace.

[index.json](index.json), SHA-256
`704f6ee2613a681f0d21329acc89b8dbb36d272ee05a57eed5978115ffd9ec10`,
retains 16 original records and two deduplicated maps in 18 compressed blobs.
Use the same lossless JSON-map reconstruction described in the
[preceding checkpoint](../row-representation/README.md). Every original was
reconstructed and compared byte-for-byte; no binary or cache is copied.
The fresh maps contain 5535 full entries and 611 runtime-inventory entries;
only qualified post-test task/plan prose and evidence differ from the tested
map. All Rust, configuration and fixture entries remain exact. The runtime
inventory includes the task-owned plan, so it is not described as wholly equal
to the pre-prose test map.

The next milestone rebase must preserve these as old-context observations.
Required full-Row and Access restoration, image bounds/hostiles after canonical
success, startup refresh, final specification, regressions, Clippy and exact-head
review remain pending. Whole F3 and the connected F-core gate remain open.
