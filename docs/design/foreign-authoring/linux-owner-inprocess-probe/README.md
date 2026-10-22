# Trusted build-monitor preparation and record-scope clarification

Preparation only. No compiler, generation, linking or owner/native image startup
was assigned or run. The prospective contract clarification is required before
assigning the selected build. No architecture, strict-artifact approval, checked
runtime, deployment/store/context, isolation or whole F2 acceptance follows.
AD-0015 remains owner-free.

The [parent experiment contract](../linux-owner-inprocess-experiment.md) distinguishes adapted Ash/entry/generated text
records from the entire existing repository producer snapshot. All 2784 blobs
of selected 1a8ecef0 are pinned in [the full selected manifest](preparation/selected-archive-manifest.json),
including all eight over 1 MiB. The 177 build.rs runtime-content inputs are a
separate census, not a replacement snapshot or a full runtime fingerprint.
The snapshot itself is unchanged. Full source/archive bytes remain external;
no binary, system header, object, large map or vendor source is copied here.

## Executed safe evidence

[build_monitor.py](build_monitor.py) and [test_monitor.py](test_monitor.py) are
the exact reviewed/executed bytes. The [verification index](verification-repaired.json)
binds the retained command receipts.
The final source-before/after pins agree. The [final raw log](safe-tests-repaired-final.log) records 15 methods:
14 receipt-bearing benign Python command cases, one oversized-config pre-run
CLI refusal, plus pure cumulative-record/read-size assertions. All passed.
observations/ retains the exact 14 configs, receipts, stdout/stderr, retained
outputs/prefixes and fixture-disposal readbacks. Original paths refer to disposed
private /tmp fixtures; copies preserve bytes and are not newly executed records.
No recorded successful child is an Ash/native artifact.

The historical-d247 source and test/index bytes precede the repairs.
red-finalization.log plus test-finalization-red.py and red-observations preserve
actual late-output/map exit-success defects and cumulative-record failure.
The original 304-entry d247 manifest and all earlier safe-test generations remain
external at /tmp/ash-owner-build-monitor; they are not reproduced by this compact
payload. verification.json's historical receipt pins are historical associations,
not claims that every referenced older receipt is included here.

The repaired monitor uses an exact argv (no shell) and exact environment, verifies
streamed tool/input pins, creates an owned private run directory, and uses a
process-local Linux subreaper. WNOWAIT keeps the leader PID pinned until the one
owned-group signal; adopted/direct children are individually reaped. Escaped
owned groups refuse. Pending kernel reaping cannot be called completion. Final
output drain/tree sampling cannot preserve exit success after a late limit
violation; earlier refusals remain primary. Cumulative retained watch paths and
config allocation are bounded. Output retention is bounded; sidefile checks are
sampled observations with possible overshoot, not a quota or cache containment.
Tools/intermediates are not subject to the 128 MiB final-candidate limit; the
589,362,808-byte cached compiler is not approved for reuse.

To reproduce only the safe controls, copy the two Python files to a fresh owned
private /tmp directory and run `/usr/bin/python3 -B test_monitor.py` there.
This creates a new observation generation with new paths/process identities.
It does not reproduce old receipts or authorize the build configs. Inspect the
monitor's Linux/process-local assumptions and source pins before running tests.
Do not execute commands.unexecuted.json or compiler-build.monitor.json from this
preparation record without a separate exact build assignment.

## Unexecuted next gates

preparation/ contains pinned selected-source/native/tool/config correspondence,
the exact adapted owner input and entry, a read-only full snapshot verifier, and
an unexecuted command proposal. The proposed record-scope amendment must first
be accepted/retained and its actual hash entered into the later assigned tuple.
Fresh selected-source offline compiler build is the default. Generated project,
compiler/output, private payload, map and final-image pins are post-build facts
that do not yet exist. Each next command config requires the just-observed exact
tool/artifact pins, operator coordination and review. Shared cache stays singular;
no active Borrow source or cached compiler reuse by intent is permitted.

Readelf/static-format facts do not prove absence of runtime loading. New ownerful
closure, evaluator/native/bridge correspondence, host-loss/group-reservation/
shutdown premises and later exact approval remain explicit gates. This small
preparation item does not complete issue58 or permit ownerful execution.

The unexecuted [command proposal](preparation/commands.unexecuted.json) and
[compiler monitor config](preparation/compiler-build.monitor.json) preserve the
external d448eee1 proposed-contract pin as prepublication history. That original
/tmp proposal remains unchanged; the publication contract adds only the
informative preparation link. These historical proposal pins do not identify an
accepted contract. A fresh association with the exact retained contract and
accepted amendment is mandatory before any command assignment.
