#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
proof_build_dir=$(mktemp -d)
trap 'rm -rf -- "$proof_build_dir"' EXIT
export LEAN_PATH="$proof_build_dir"
# Empty registration baseline. No region proof has been integrated yet.
