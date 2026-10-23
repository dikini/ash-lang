# Member reconstruction and static Access matching

This is a partial record on published PR110 checkpoint `0027f766`, before the
assigned rebase onto retained F6 checkpoint `8b844436`. It grants no success on
the newer combined tree. Required private-image work failures remain open.

The index retains 60 original files through content-addressed gzip blobs and
four deduplicated full/runtime maps. For JSON-map templates, recursively replace
the sole `$retained_map` marker with its indexed map, then serialize with
`json.dumps(indent=2)` plus a newline. Other blobs decompress directly. All
reconstructed sizes, hashes and bytes were checked against the original files.
No binary, ELF, archive or Cargo cache is copied into this record.

`origin-access-05` (4077) is compile-only: the new test helper supplied a
SourceCopyWindow node where the existing enum requires a Box. E0308 stopped
compilation before any selected test. The exact test-only Box wrapper repair
is frozen separately in the next observation.

`origin-access-06` (67080) compiles and passes owned-row 2, existing substitution 3,
copied-template 1 and borrowed-origin 1. The dependency matrix is 8/10. Its
canonical full-kind Access control reaches and passes the coherent erased
descriptor/ordinary-spine static-helper refusal and the erased-descriptor
independent-Core Registry refusal. The ordinary spine itself is not installed
into Core. The actual Parent/Child runtime non-entry control also passes.

Both image failures remain genuine: the Access full-Row image returns
`CoreAdmission(TypeWorkExceeded)`; the other full-Row image returns
`Validation(Resource)`. These are distinct paths and the earlier Row-image
observer's refused-charge cause is not transferred to this binary. The base
image completes at 264909 and full-Row Core at 87672. Those positives include
canonical-first hostile and exact/prefix/short/spent/fresh controls; controls
after either failed image restoration are uncredited. The runner stops there,
so all three startup refreshes remain unrun. Overall 17 tests are selected:
15 pass and 2 fail, with no default, fixture or tariff waiver.

All five executed test commands have equal before/after maps: full 5280
`1a33701eee92d5e10ed6996d947b1a5ac8425775bed3c612117bc02b9b24907c`
and runtime 609
`717bf7f2a11a545e929f5bd2bacc85067bc2465752ee89dd8ac01e9a7833168c`.
Actual lib artifact: 607102960 bytes,
`8a3cd78471d74ad841637470b6d7d35f3a6f44bbd8dad65a4c308310c7714a94`.
The source-only refinement moves owned row members and clones borrowed members
with the unchanged full-kinded instance rebuild code before one combined
canonicalization. Its isolated parity/budget tests pass; the required images
do not. No sufficient saving or isolated cross-map component attribution is
claimed. The static matcher now selects its row path from prepaid original
formal kinds; the separate executable Type-only matcher is unchanged.

This post-test record and TASK0051 prose are added after the frozen map. Final
specification wording, both default full-Row image restorations and their later
bounds/hostiles, refreshed startups/regressions, Clippy and independent final-head
review remain pending. F-core remains the next full workspace gate, scheduled by
PM and run by the developer. No native program or callback is executed here.
