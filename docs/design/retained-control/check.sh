#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
proof_build_dir=$(mktemp -d)
trap 'rm -rf -- "$proof_build_dir"' EXIT
export LEAN_PATH="$proof_build_dir"
# Reviewed proof registrations follow.
lean -DwarningAsError=true -o "$proof_build_dir/Ownership.olean" Ownership.lean
lean -DwarningAsError=true -o "$proof_build_dir/OwnershipExamples.olean" OwnershipExamples.lean
lean -DwarningAsError=true -o "$proof_build_dir/DrainSafety.olean" DrainSafety.lean
