# Checked byte/window test-first evidence

The genuine checked library prepares an initialized byte-backed `State<H,R>`,
Bytes and Nul access families, preserving native members, complete W/H/R vectors,
view-producing scalar keys and an extent tied to its view/key. This is static
contract evidence; no native memory was allocated or observed.

Both commands use `cargo test --offline --lib checked_byte_window_ -- --nocapture`
with one job and the existing shared target. Each before/after map contains 590
identical inputs for that command. The maps include source, tests, specification,
libraries, path-dependency inputs, the plan and runner; they are scoped input
inventories, not a claim about external tools or the entire filesystem.

- `prerequisites`: exit 101, 2/3 pass; aggregate
  `3d3468b8b77e8664bbe8e8f69c72bdf0f1d88035aaf003cc25645ba7eb535863`.
  Preparation and default-profile refusal pass. Expected-positive resolution
  stops at `UnavailableExport` for `checked_byte_read`, span 5287..5304. This
  inventory finding does not establish checked owner binding or source permission.
- `binding-isolated`: exit 101, 2/4 pass; aggregate
  `2a1eb5aed6582288ce11555679ad70613ecd1125e506619f4c8508036ccb94da`.
  Preparation and default refusal pass again. The separate name-isolated control
  substitutes only existing legacy builtin spellings so resolution can reach the
  unchanged checked library. It then refuses `ForeignContract / InvalidLibrary`
  at library span 35..2618. The checked owner binder requires Opaque and rejects
  this Bytes representation. The root is never source-checked in this control;
  legacy spellings grant no checked State/view permission. The inventory test
  independently retains its earlier missing-export failure.

The committed test source reconstructs `binding-isolated`. Applying
`prerequisites-test.patch` to that source reconstructs the first test bytes exactly
(SHA256 `9b403bf5a8c8a72d462429f5871d22fa18707101080a4b6df5d8e231e468cf3b`);
the fixture, runner and all other first-map inputs are unchanged between runs.
The second test strengthens the View/Extent full-vector assertions and isolates
binding. Raw logs, complete maps and receipt digests are retained beside this file.
No product code changed for either run.

The final test artifact SHA256 is
`ab62ad461690aba74a12783a869bda8e603ad6324f86c9d33961ec02711313c7`.
The existing F2 compiler `target/debug/ash` remains SHA256
`5dca1b624bf206c44c6c4d3037675193800516eb936a0cf6420e67394e998d3e`
before and after these library-only commands. The Cargo slot was released after
both commands completed. Source/summary/consumer/Core/transforms/static-image
positives for the four primitives remain pending, as do hostile and budget gates.
