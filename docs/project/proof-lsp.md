# Lean proof navigation

[AD-0012](../decisions/AD-0012-proof-development-feedback-and-build-reuse.md)
uses language servers for navigation and local diagnostics. The reviewed frozen
integration runner remains the proof acceptance gate, including warning, report,
source, dependency and axiom checks. LSP success does not establish proof
coverage.

The adapter in [tools/lean/lsp.py](../../tools/lean/lsp.py) exposes eight
navigation
and diagnostic tools. It removes builds, scratch compilation, proof mutation,
remote search and local search indexing. It starts `lake -f lakefile.toml serve
-- -j1 -M2048`
with one open-file worker and a 15-second request timeout. Canonical file inputs
must remain inside the prepared workspace; traversal, escaping symlinks and
nested Lake projects are rejected before client startup. Project binding,
inference and the client factory also enforce that exact root. Upstream stdio
project switching is disabled, and the shared-client cap is one. The 2048 MiB
Lean
allocation cap is per Lean process; it is not a total process-tree RSS limit.
Open one file at a time and stop a request that exceeds the available resource
window. The integration runner's host lock does not cover LSP; stop the MCP
before
resource-heavy integration work.

## Installation

Run commands from the repository root. Keep the MCP checkout in `target/`.

```bash
bash tools/lean/lsp-install.sh
```

This checks out
[`lean-lsp-mcp`
0.31.0](https://github.com/oOo0oOo/lean-lsp-mcp/tree/f00f625810d183dbb597a3677d2d5a83b084f761)
at commit `f00f625810d183dbb597a3677d2d5a83b084f761` and installs its frozen
`uv.lock` with `uv sync --frozen --no-dev`. The lock selects `leanclient` 0.13.2
and MCP 2.0.0. Serve checks the clean source commit and package versions before
starting Lean. The adapter uses the pinned client's `server_command` API and
replaces the MCP's internal client factory; review that boundary before
upgrading.
Lean remains `leanprover/lean4:v4.33.1`.

The optional
[`lean4`
skill](https://github.com/cameronfreer/lean4-skills/tree/b6243b85b9b0a0ddff5bb6773889044daf687f8e/plugins/lean4/skills/lean4)
was inspected at commit `b6243b85b9b0a0ddff5bb6773889044daf687f8e`. Install
only `plugins/lean4/skills/lean4` using the Codex skill installer with that ref.
This Tier 1 installation adds instructions and references. It does not install
helper commands, plugin hooks or agents. It becomes available on the next turn.
The full plugin registers session, prompt and tool hooks; its checkpoint
workflow includes project builds and commits. Those workflows are outside this
setup. Ash's frozen acceptance gate and explicit resource limits take precedence
over generic skill advice to bootstrap or checkpoint with `lake build`.

## Frozen workspace

Prepare a separate workspace from an existing validated integration evidence
file. Use a fresh output path; preparation preserves an existing workspace.

```bash
python3 tools/lean/lsp.py prepare \
  --evidence /absolute/path/to/integration-evidence.json \
  --workspace target/lean-lsp-workspace
```

The default selects `OneShot`. Repeat `--module NAME` to select another set.
Preparation checks compiler and library hashes, frozen sources, source import
lists, every selected direct-import hash, artifact hashes and log hashes for the
transitive closure. It copies sources and artifacts into the new workspace and
records the evidence hash. Serve rechecks the frozen pins and copied artifacts.
It rejects changes to the workspace's pinned toolchain or Lake configuration
and rejects an additional `lakefile.lean`, including a dangling symlink. The
client factory rechecks these constraints before every start or restart and
selects `lakefile.toml` explicitly.

The Lake package has no library, executable or default build targets.
`LEAN_PATH`
contains only copied, validated artifacts in the workspace's `imports/`
directory.
The original snapshot, cache and active alignment checkout are not changed.
Local copied-source edits are development feedback; downstream imported
artifacts
remain frozen until another workspace is prepared from new integration evidence.
LSP feedback cannot certify a changed dependency closure.

Register one stdio server after resolving the repository root to an absolute
path. This writes the named MCP entry in the user's Codex configuration.

```bash
codex mcp add lean-proof-navigation -- \
  /absolute/repo/target/lean-lsp-mcp/.venv/bin/python \
  /absolute/repo/tools/lean/lsp.py serve \
  --workspace /absolute/repo/target/lean-lsp-workspace
```

Reload the task's MCP tools or start a new task if the new tools are not
visible.
Keep this workspace and checkout while the entry refers to them; update the
entry before removing the tooling worktree.

## Verification

The pin tests start no compiler:

```bash
python3 -m unittest discover -s tools/lean -p test_lsp.py
target/lean-lsp-mcp/.venv/bin/python -m unittest discover \
  -s tools/lean -p test_lsp_upstream.py
```

The upstream routing tests mock every client startup and stdlib discovery. They
exercise all eight exposed tools with an external workspace file, absolute and
relative paths, symlink escapes, nested projects, direct project inference,
binding and factory calls. They also reject changed configurations before
restart and additional Lean configuration files, including dangling symlinks.
These tests start no Lean or Lake process.

Run the smoke check only in a resource window without another Lean build. It
creates and removes `LspSmoke.lean` in the prepared workspace, imports the
validated `OneShot` artifact and checks a positive proof state and hover plus
an intentional negative diagnostic. Its total deadline is 15 seconds.

```bash
target/lean-lsp-mcp/.venv/bin/python tools/lean/lsp-smoke.py \
  --workspace target/lean-lsp-workspace
```

The verified Lean 4.33.1 handshake with isolated copied artifacts completed in
2.56 seconds after the workspace and configuration guards were added. Its
requests used
1-based positions: `lean_goal` at line 3, column 3 returned `n : Nat` and
`⊢ n = n`; `lean_hover_info` at line 4, column 26 returned
`Ash.OneShot.TypeArgument : Type`; `lean_diagnostic_messages` returned a
complete
report with an unknown-constant error for `False.intro` at line 6, column 9
and no failed imports. The imported type came from the existing frozen artifact,
without a
proof rebuild.
The final 100 ms resource sample peaked at 1,236,099,072 bytes (1.151 GiB)
across the
smoke client, MCP, Lake and Lean process tree. Sampling can miss shorter peaks.
The eight-tool allowlist also matched the MCP tool inventory.

Python 3.10 emitted an upstream subprocess-finalizer warning during shutdown
of both smoke handshakes. A process check found no surviving Lake or Lean
server.
No claim about large-module latency follows from this small smoke check.

The installed Codex entry is `lean-proof-navigation`. On the verified host it
points to `.worktree/proof-tooling/target/lean-lsp-mcp/.venv/bin/python`,
`tools/lean/lsp.py` and `target/lean-lsp-workspace-isolated` within that
worktree.
The final smoke transcript is `target/lean-lsp-final-smoke.jsonl`. The selected
frozen evidence SHA-256 is
`d865019fb806462484467c8722e0ab4c48766086b2911bfdd5166f5190ae73b8`.
The MCP and language server were stopped after verification. The current task
has not reloaded its tool inventory.
