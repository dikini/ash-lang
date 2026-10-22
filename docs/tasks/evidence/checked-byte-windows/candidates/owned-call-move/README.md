# Owned observed-call State checkpoint

This local candidate is based on `a3c2bac83cd2e8447b002507996390e547a19143`.
It moves the already-owned incoming State into a new observed-call record only
after successful publication. The paid map-key copy, hash, reserve and insertion,
record order, successor work and existing delivered-prefix update remain.
It removes one redundant complete State construction; no tariff, fixture,
default allowance, semantic proof or public execution guard changes.

The fresh baseline build selected the original two-owner startup and failed with
`Validation(Resource)` at the unchanged 327680 limit. Its valid four-region
coarse observation then measured a 75529-unit root interval: 70496 measured union
and 5033 residual. Discover exclusive work was 41062 and value-close work 29366.
These region measurements identify context, not the cost or net saving of the
owned-call change. The test inferior failed with 101 despite debugger exit 0.

The source-reviewed owned-call candidate passed seven distinct tests in eight
occurrences: three new record/order/late-prefix/failure/budget controls, the
existing delivered-prefix/opaque-replay control, and all three unchanged startup
probes. Actual totals were two-owner 327365, nested cleanup 320457 and dependent
cumulative 325006. The dependent test includes exact, one-short, prefixed and two
fresh retries plus independent original-library correspondence. No native foreign
execution or public checked activation occurred.

All six commands retained identical 3641 full and 596 runtime input maps:
`61fa59a0bdb153f5c5569864fa8bff9cf551f8aef36601494c0ee67c67e61734` and
`40569d63bb7d7cbaee55046fc777323ef0cd96291b96060e6913579d53cb3304`.
User-authorized parallel verification used a new isolated `parallel-f3` target,
`CARGO_INCREMENTAL=0`, one job, offline/locked and an empty compiler wrapper.
The freshly compiled artifact was SHA256
`8803937d3582e1e2e27938b0b9d4816201398d077f44adafe93d9832c3b8d253`
(821433880 bytes). This configuration differs from historical shared-target
builds, so no exact cross-configuration saving is claimed. Sampled target disk
peaked at 2656448512 bytes and available memory stayed at least 8669089792 bytes;
no resource stop occurred.

Source and dynamic review were independently CLEAR for this focused scope.
The retained milestone subsequently advanced to the passive PR108 tree; this
standalone evidence does not transfer as a fresh combined-tree test result.
Rebase integration review, affected regressions, two fresh two-owner repeats,
Clippy and immutable final-head review remain pending. Whole F3, connected byte
execution and milestone-wide gates remain open.

`index.json` identifies every original raw/receipt/process/script/pin file.
Content-addressed gzip blobs deduplicate identical files and large input maps.
For `raw-gzip`, decompression reproduces the original bytes. For
`json-map-template-gzip`, decompress the template, recursively replace each sole
`$retained_map` object with the JSON map from its referenced gzip blob, then
serialize with Python `json.dumps(value, indent=2) + '\n'`. The resulting bytes
must match the original SHA256 and size. No binary is copied into evidence.
