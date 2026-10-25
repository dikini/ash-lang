# Generated Ash scalar diagnostic — prepared, not executed

This disposable experiment asks whether the exact existing-profile generated
Ash scalar evaluator and libc `abs(-7)` bridge run from the approved, sealed
whole-image file descriptor after their candidate pathname is replaced.
It is not a checked runtime, isolation experiment, or accepted architecture.

The image retains libc localization/gconv paths to runtime loading. Those
paths and host authority are explicit trusted diagnostic premises. Structural
ELF checks establish ET_EXEC, x86-64, and absence of PT_INTERP/PT_DYNAMIC; they
do not establish a whole closure that excludes runtime loading. Strict profile
readiness, the proposed architecture decision, and whole F2 acceptance remain
unmet. No approval store is provisioned.

`policy.json` pins the image, producer receipt, source checkpoint, separately
approved inert replacement, fixed argv, empty environment, and bounds. The
producer receipt describes production; it does not authorize execution.
`approval-template.json` is deliberately unauthorized. Root must separately
approve the exact policy, harness, receipt, and image hashes and diagnostic
premises after independent review. This manual trusted approval session is
not a product approval authority or protected store implementation.

The harness opens candidate/control paths nonblocking and rejects nonregular
files before reads. It bounds all fixture/control reads and streaming copies: image at
96 MiB, control documents at 256 KiB, at most 64 ELF program headers, and
combined captured output at 16 KiB. It requires executable memfd flags 19,
mode 0500, and all four immutable seals (mask 15). It hashes and inspects the
same sealed object, attempts write/shrink/grow (requiring EPERM), and rehashes
before child creation. A private mutable copy supplies a digest-mismatch
comparison; the original image is never modified. The approved reporter B
only replaces the candidate pathname and is never executed by this harness.

The child has a single fixed argv[0], no additional arguments, an empty
environment, stdin from /dev/null, and one combined output pipe. Descriptors
other than 0–3 are closed before fd execution; fd 3 is CLOEXEC. The 30-second
child deadline requests termination. All parent post-fork setup and failure
paths enter kill/reap cleanup; the pending lifecycle is recorded before a
blocking reap. Kernel delays may delay reaping, and termination of the launcher
itself cannot guarantee cleanup. Success requires an observed reaped child,
exit zero, no harness failure, and exactly `Returned(7)\n`. This trusted fixture
has no authored descendant creation; process-domain containment is not tested.

Pre-execution comparisons cover missing approval, altered approval pins,
unsupported or changed receipt, changed image, and replacement before pinning.
A missing/unreadable approval also refuses before child creation. A result
record remains on refusal. Temporary executable candidate files are removed
when no child exists or the child is observed reaped; unconfirmed child state
retains its evidence instead of claiming cleanup succeeded.

## Verification so far

`/usr/bin/python3 -m unittest -v test_diagnostic` passes nine focused tests.
All lifecycle tests mock fork, kill, and waitpid: no child or generated image
has run. They exercise pre-fork selector refusal, post-fork setup refusal,
deadline/interrupted reaping, exec-refusal status, combined-output overflow,
pure approval/input validation, FIFO refusal before blocking, and fully mocked child
descriptor mapping/close_range/fd-exec plus setup failure. These tests are harness evidence, not
observed kernel execution or cleanup evidence. `unit-tests.log` records the run.

After independent review and separate exact approval only, the proposed command
is `/usr/bin/python3 diagnostic.py --approval /absolute/path/to/approved.json`
from this directory. Preserve sandbox refusal, errno, and lifecycle evidence.
Any host rerun requires its own normal tool authorization for these exact
artifacts; it does not change policy or create an isolation claim.

Retain source, policy, approvals, observations and their hashes if this provides
useful F2 feasibility evidence. Dispose of private image copies after reaping;
retain the original build/receipt externally without copying binaries into the
repository. No Cargo, relink, repository writes, or image execution is part of
this preparation checkpoint. The earlier 1 MiB reporter probe remains unchanged.
