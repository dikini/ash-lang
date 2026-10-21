# Static checked-owner binding prerequisite

This TASK-0051 checkpoint implements no lifecycle or runtime authority.
The passive dependency-free opaque State<H,R> fixture uses exact distinct
host H and owned R, nullable acquisition, void teardown and canonical checked
call results. Its explicit-profile source resolution currently refuses owner
binding with ForeignContract/InvalidLibrary before source checking.

The three preparation/default-resolution/legacy-ABI controls pass. Both commands
have equal before/after 564-file manifests, compact sorted-JSON aggregate
`de7f3bde6c3721df5964e5168187491acfbc724dde3030addfc0671258db7199`.
The raw expected failure and passing controls are in `test-first`; the failure
is not passing delivery verification. No product change is present at this
snapshot. Body-free owner imports, checked_scope and connected lifecycle/Core
remain pending.

## Shared header boundary

The binding candidate passes the passive source controls and five original-owner
identity/work tests. A separate real-source probe first admits the unchanged
ordinary resource Scope header, then resolves its checked-owner counterpart and
calls the same independent header admission API. That checked candidate also
admits: the expected-refusal test fails. Its loop stops at Scope, so the later
AcquiredOnly case has not yet run in this snapshot. No checked lifecycle success
is inferred; this exposes an unintended prerequisite bypass to close before
binding delivery. The header-red commands share a frozen 566-file manifest,
aggregate `da792bd7bbc2515946f64cec87cd9f90f9290173e575728a407d0903bb5b9541`.
The separate earlier helper compilation error is not product evidence.
