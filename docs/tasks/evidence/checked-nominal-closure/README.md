# Capture-only nominal closure

This test-first checkpoint belongs to [TASK-0051](../../TASK-0051-checked-ffi-contract-carriers.md)
and draft [PR #94](https://github.com/dikini/ash-lang/pull/94). It starts from
retained `036c366834c839e4f0a503cf63e9db46448bb486`. No product repair or acceptance
is supplied by these results.

The initial data-only fixture parses and checks but has no Held type in the real
callable inventory. Its reconstructed source and diagnostic are retained; this
is rejected fixture evidence, not a product defect. Constructor patterns use
`Held(captured)`. Hidden kind metadata grants no constructor access.

The revised fixture passes Held as an ABI-unused native Type actual through the
existing generic closed scalar wrapper. Its public scheme omits Held. Actual
capture types retain Held, and its private hidden kind row is present without a
constructor family or public source name. The exact authored Callee assumption
and native original remain. The unrelated private Spare is absent.

| Command | Result |
| --- | --- |
| Global canonical capture/hidden-kind control | passed |
| Unrelated private Spare control | passed |
| Body-free consumer, linking, Core and identity/fold revalidation | passed |
| Required hidden Held metadata erasure | failed as expected: summary returned Ok |

The red preserves the completed defining global publication, callable capture,
resident sources, native originals, effect identities and outward scheme while
removing the Held hidden lookup/order row. It identifies summary authentication
as an accepting boundary; it does not establish a later consumer or Core bypass.
Independent mutated consumer/Core controls, selected-method parity and a bounded
repair remain pending. Whole F3, F-core and runtime gates remain pending.

`test-first.json` lists exact commands, environment, exits and raw digests.
`vector-source-pins.json` records the frozen Rust/Ash/Cargo/build input bytes for
these four commands. The raw diagnostic predates that revised fixture and is
not transferred as a result on the vector input. Logs retain original bytes,
including any trailing blank lines. No native call executes.
