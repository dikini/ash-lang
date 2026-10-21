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
