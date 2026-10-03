#!/usr/bin/env python3
"""Prepare a frozen Lean workspace or serve its bounded navigation MCP."""
import argparse
import asyncio
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys
import subprocess

MCP_COMMIT = "f00f625810d183dbb597a3677d2d5a83b084f761"
LAKEFILE = 'name = "ash_proof_navigation"\nversion = "0.1.0"\n'
TOOLCHAIN = "leanprover/lean4:v4.33.1\n"
TOOLS = frozenset({"lean_goal", "lean_term_goal", "lean_hover_info", "lean_diagnostic_messages",
                   "lean_file_outline", "lean_completions", "lean_declaration_file", "lean_references"})


def digest(path):
    hasher = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def check(path, expected):
    if digest(path) != expected:
        raise ValueError(f"Pin mismatch: {path}")


def validate(evidence, modules):
    """Validate the selected transitive imports before copying any source."""
    data = json.loads(Path(evidence).read_text())
    if not data["version"].startswith("Lean (version 4.33.1,"):
        raise ValueError("Expected pinned Lean 4.33.1")
    for path, pin in data["compiler_library_hashes"].items():
        check(path, pin)
    selected = set()
    def visit(module):
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", module):
            raise ValueError(f"Invalid module: {module}")
        if module in selected:
            return
        selected.add(module)
        source = Path(data["cwd"]) / f"{module}.lean"
        record = data["records"][module]
        check(source, data["manifest"][source.name])
        if record["source_sha256"] != data["manifest"][source.name]:
            raise ValueError(f"Source record mismatch: {module}")
        imports = re.findall(r"^import\s+([^\n]+)", source.read_text(), re.M)
        actual = [name for line in imports for name in line.split() if name not in {"Std", "Init", "Lean"}]
        if actual != data["imports"][module]:
            raise ValueError(f"Import mismatch: {module}")
        artifact = data["selected_external_artifacts"][module]
        check(artifact["selected_path"], artifact["olean_sha256"])
        if artifact["olean_sha256"] != record["artifact_sha256"]:
            raise ValueError(f"Artifact record mismatch: {module}")
        check(record["log"], record["log_sha256"])
        if set(record["direct_import_artifacts"]) != set(actual):
            raise ValueError(f"Direct import record mismatch: {module}")
        for name in actual:
            if record["direct_import_artifacts"][name] != data["selected_external_artifacts"][name]["olean_sha256"]:
                raise ValueError(f"Direct import artifact mismatch: {module} -> {name}")
            visit(name)
    for module in modules:
        visit(module)
    return data, sorted(selected)


def prepare(evidence, workspace, modules):
    data, selected = validate(evidence, modules)
    workspace = Path(workspace).resolve()
    if workspace.exists():
        raise ValueError(f"Workspace already exists; choose a fresh path: {workspace}")
    workspace.mkdir(parents=True)
    (workspace / "imports").mkdir()
    for module in selected:
        shutil.copyfile(data["selected_external_artifacts"][module]["selected_path"],
                        workspace / "imports" / f"{module}.olean")
        shutil.copyfile(Path(data["cwd"]) / f"{module}.lean", workspace / f"{module}.lean")
    (workspace / "lean-toolchain").write_text(TOOLCHAIN)
    (workspace / "lakefile.toml").write_text(LAKEFILE)
    receipt = {"evidence": str(Path(evidence).resolve()), "evidence_sha256": digest(evidence),
               "modules": selected, "lean_path": data["lean_path"], "mcp_commit": MCP_COMMIT}
    (workspace / "lsp-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


def check_workspace_configuration(workspace):
    workspace = Path(workspace)
    alternative = workspace / "lakefile.lean"
    if alternative.exists() or alternative.is_symlink():
        raise ValueError("Workspace must not contain lakefile.lean")
    if (workspace / "lean-toolchain").read_text() != TOOLCHAIN or (workspace / "lakefile.toml").read_text() != LAKEFILE:
        raise ValueError("Workspace toolchain or Lake targets changed")


class FixedWorkspace:
    """Resolve tool inputs only inside the one prepared Lake project."""

    def __init__(self, workspace):
        self.workspace = Path(workspace).resolve(strict=True)

    def project(self, project_path):
        if Path(project_path).resolve() != self.workspace:
            raise ValueError("Only the prepared Lean workspace is allowed")
        return self.workspace

    def file(self, file_path, *, require_exists=True):
        candidate = Path(file_path).expanduser()
        if not candidate.is_absolute():
            candidate = self.workspace / candidate
        candidate = candidate.resolve(strict=require_exists)
        if not candidate.is_relative_to(self.workspace):
            raise ValueError("File is outside the prepared Lean workspace")
        current = candidate if candidate.is_dir() else candidate.parent
        while current != self.workspace:
            if (current / "lean-toolchain").exists() and any(
                (current / name).exists() for name in ("lakefile.toml", "lakefile.lean")
            ):
                raise ValueError("Nested Lean projects are outside the prepared workspace")
            current = current.parent
        return candidate


def install_workspace_guard(workspace, client_utils, server):
    """Guard the pinned upstream paths before any project inference or start."""
    guard = FixedWorkspace(workspace)
    original_bind = client_utils.bind_lean_project_path

    def bind(ctx, project_path):
        guard.project(project_path)
        current = ctx.request_context.lifespan_context.lean_project_path
        if current is not None:
            guard.project(current)
        ctx.request_context.lifespan_context.project_switching_allowed = False
        return original_bind(ctx, guard.workspace)

    def resolve(ctx, file_path, *, require_exists=True):
        bind(ctx, guard.workspace)
        return guard.file(file_path, require_exists=require_exists)

    def infer(file_path, ctx=None):
        guard.file(file_path, require_exists=False)
        if ctx is not None:
            bind(ctx, guard.workspace)
        return guard.workspace

    async def start(project_path):
        return await bounded_client(guard.project(project_path), guard.workspace)

    client_utils.bind_lean_project_path = bind
    client_utils.resolve_file_path = resolve
    client_utils.infer_project_path = infer
    client_utils._project_switching_allowed = lambda ctx=None: False
    client_utils._MAX_SHARED_CLIENTS = 1
    client_utils._start_client = start
    # server imports the switching function by value for its lifespan setup.
    server._project_switching_allowed = lambda ctx=None: False
    return guard


async def bounded_client(project_path, workspace):
    FixedWorkspace(workspace).project(project_path)
    check_workspace_configuration(workspace)
    from leanclient.aio import AsyncLeanLSPClient
    client = AsyncLeanLSPClient(str(project_path), max_workers=1, request_timeout=15,
        server_command=["lake", "-f", "lakefile.toml", "serve", "--", "-j1", "-M2048", "-Dserver.reportDelayMs=0"])
    await client.start()
    return client


def serve(workspace):
    workspace = Path(workspace).resolve()
    receipt = json.loads((workspace / "lsp-receipt.json").read_text())
    check_workspace_configuration(workspace)
    check(receipt["evidence"], receipt["evidence_sha256"])
    data, _ = validate(receipt["evidence"], receipt["modules"])
    if receipt["lean_path"] != data["lean_path"] or receipt["mcp_commit"] != MCP_COMMIT:
        raise ValueError("Workspace receipt mismatch")
    for module in receipt["modules"]:
        check(workspace / "imports" / f"{module}.olean",
              data["selected_external_artifacts"][module]["olean_sha256"])
    install = Path(sys.prefix).parent
    revision = subprocess.check_output(["git", "-C", str(install), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", str(install), "status", "--porcelain", "--untracked-files=no"], text=True).strip()
    if revision != MCP_COMMIT or dirty:
        raise ValueError("MCP checkout does not match the clean pinned source")
    from importlib.metadata import version
    if version("lean-lsp-mcp") != "0.31.0" or version("leanclient") != "0.13.2":
        raise ValueError("Install the pinned MCP lockfile first")
    os.environ.update(LEAN_PROJECT_PATH=str(workspace), LEAN_PATH=str(workspace / "imports"),
                      LEAN_LSP_MAX_OPEN_FILES="1", LEAN_MCP_PREWARM_FILES="", LEAN_REPL="",
                      LEAN_LOOGLE_LOCAL="false", LEAN_LOG_LEVEL="ERROR",
                      LEAN_MCP_INSTRUCTIONS="Navigation and local diagnostics only. Frozen integration remains the proof acceptance gate. Open one file at a time; no automatic builds.")
    from lean_lsp_mcp import client_utils, server, main
    install_workspace_guard(workspace, client_utils, server)
    for tool in asyncio.run(server.mcp.list_tools()):
        if tool.name not in TOOLS:
            server.mcp.remove_tool(tool.name)
    sys.argv = [sys.argv[0]]
    return main()


def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare")
    prep.add_argument("--evidence", required=True)
    prep.add_argument("--workspace", required=True)
    prep.add_argument("--module", action="append", default=[])
    run = sub.add_parser("serve")
    run.add_argument("--workspace", required=True)
    args = parser.parse_args()
    if args.command == "prepare":
        prepare(args.evidence, args.workspace, args.module or ["OneShot"])
    else:
        return serve(args.workspace)


if __name__ == "__main__":
    sys.exit(cli())
