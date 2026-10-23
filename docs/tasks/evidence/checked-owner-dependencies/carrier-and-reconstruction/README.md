# Checked dependency carrier and reconstruction checkpoint

This is a partial PR110 record on retained `0bbf75cb`, through source checkpoint
`2ea22b64` plus the frozen `origin-access-04` candidate. The required full-Row
private images still fail under the unchanged 327680 allowance. No native
program is executed and no runtime dependency group is admitted.

The indexed original records are reconstructed byte-for-byte from 92 gzip blobs
and eight deduplicated full/runtime input maps. Every reconstructed size and
SHA256 was checked against its original target file. The index records each
original relative path, size, hash, encoding and blob. For `json-map-template`,
recursively replace each sole `$retained_map` object with the JSON from the
matching map blob, then serialize with `json.dumps(indent=2)` and a final newline.
Other blobs decompress directly. Binaries and caches are not copied here.

Actual commands are separate observations:

- `row-direct-construction` (92250): its isolated specializer test passes, then
  the matrix is 6/10. The proposed conditional row override does not apply to
  the actual empty node-row maps. Its product change was removed. Two Core
  hostile tests had an invalid nonempty-map premise; Access failed at kind
  checking; the full-Row image still exhausted work. These are not hostile or
  restoration successes.
- `origin-access-01` (22878): the borrowed-origin donor/depth/work control passes,
  then the matrix is 8/10. The full-Row image fails with `Validation(Resource)`;
  Access fails during source/body-free checking with `Internal(InvalidState)`.
- `origin-access-02` (31090): both new row controls fail at their supposed positive
  unwrap with `Missing`. The constructor correctly adds known member 0 to the
  tail's lacks set, so replacement `[0,2]` is invalid in both old and owned paths.
  No later batch phase ran. The production exclusion check was not relaxed.
- `origin-access-04` (69535): corrected owned-row 2, existing substitution 3,
  copied-template 1 and borrowed-origin 1 all pass. The matrix is 8/10. Genuine
  checked Access now passes source/body-free/link/independent Core and static
  matching, preserves the executable Type-only refusal, and rejects the wrong
  Row request. Its private image then fails with `CoreAdmission(TypeWorkExceeded)`.
  The other full-Row image still fails with `Validation(Resource)`. The base
  private image completes at 264910, and full-Row Core completes at 88641 with
  canonical-first hostile and exact/prefix/short/spent/fresh controls. Bounds and
  hostiles after either failed image are not credited. All three startup commands
  remain unrun because the runner stops on the matrix failure.

The last observation is 17 selected tests: 15 pass and 2 fail. These include the
real Parent/Child runtime guard in the canonical source/Core test: an independent
Parent registers first; dependent Child returns exact `Unsupported` without an
extra owner record, group binding, acquisition, K, pending call, history or
observation. It does not call a native callback. This preserves the separate
runtime dependency-free restriction.

The final tested full 5186/runtime 609 maps are
`71eedd2a889f3516e35fa2ff3fc121748b10fb3f48f23ed2434cd0b0c54e5898`
and `4eec03fa505b918fb778965285a6fc8d7a6fbc5b95df6dfd48ba951a64b11071`.
Its actual lib artifact is 579010784 bytes,
`57dd6b2801f31f078be944a95b4ca223b287e3ebacc98bb10a4f1fb9e5b782bd`.
Every recorded before/after map is equal for its own command. Post-test task and
this evidence prose are additional; no new uniform tested map is implied.

Origin borrowing retains fresh substitution and complete provenance comparison,
including the original depth refusal; direct comparison demonstrates actual
avoided clone work. The consuming row helper preserves full semantics and passes
parity/bounds, but its whole replacement-row clone introduces a second
canonicalization before combining. Current observations establish neither its
required-case net saving nor default-image sufficiency; mixed-input totals must
not be attributed solely to that helper. A paid member-only refinement remains
pending.

The formal-driven checked Access matcher hardening and coherent erased-descriptor
control remain pending. Full Core already rejects that forgery at complete
window admission; the pending helper-contract repair is not evidence of a whole
Core authority bypass. Final delivered-subset specification wording, full-Row
image success, all startup refreshes, affected regressions, Clippy and independent
current-head review remain required before merge. Initialized-byte dependencies,
ordinary State/view helper transport and runtime activation remain excluded.
The next full workspace gate is the connected F-core checkpoint, scheduled by PM
and run by the developer.
