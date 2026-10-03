#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
install_dir="$repo_root/target/lean-lsp-mcp"
revision=f00f625810d183dbb597a3677d2d5a83b084f761
if [[ ! -d "$install_dir/.git" ]]; then
  git clone https://github.com/oOo0oOo/lean-lsp-mcp "$install_dir"
fi
if [[ -n "$(git -C "$install_dir" status --porcelain)" ]]; then
  echo "MCP checkout has local changes: $install_dir" >&2
  exit 1
fi
git -C "$install_dir" checkout --detach "$revision"
uv sync --project "$install_dir" --frozen --no-dev
"$install_dir/.venv/bin/lean-lsp-mcp" --version
