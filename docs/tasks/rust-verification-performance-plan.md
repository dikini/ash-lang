# Rust verification performance implementation plan

Owned by [TASK-0042](TASK-0042-rust-verification-performance.md).

## Goal and boundary

Implement AD-0014 in the isolated tooling checkout. Keep all product sources
unchanged, preserve the milestone's current gate and serialize heavy builds.

## Steps

1. Add CLI regressions with a temporary Git fixture and an external Cargo stub.
   Test the actual runner boundary, command coverage, partial evidence, reuse,
   failed runs, moved inputs and invalidation. Observe the expected failures.
2. Replace the duplicate default-feature all-target build with all-target check
   and library/binary/example build. Keep the other required commands.
3. Implement stage selection, explicit reuse and successful-stage receipts.
   Pin Git-visible files, external inputs, tools, effective environment and
   Cargo configuration. Compare before/after pins and authenticate saved logs.
4. Run the focused suite and strict tool checks. Repair concrete failures.
5. Document the real CLI and ownership contract; review dependency roles and
   lockfile changes without selecting new package versions.
6. After PM assigns the build window, archive a frozen milestone commit into a
   comparison checkout. Apply the same tooling overlay before both plans.
   Execute the old reference plan and revised fresh plan with independent,
   comparable caches, then measure explicit reuse. Preserve every log and pin.
7. Obtain independent review, apply required repairs, refresh affected evidence
   and supply PM with exact commits, commands, measurements and limitations.

## Completion evidence

Passing tool regressions, fresh gate and matched reuse receipts; measured old
and revised wall time and unchanged product inputs; documentation/link review;
independent verdict and concrete milestone handoff.
