#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
proof_build_dir=$(mktemp -d)
trap 'rm -rf -- "$proof_build_dir"' EXIT
export LEAN_PATH="$proof_build_dir"
# Region proof registrations follow.
lean -DwarningAsError=true -o "$proof_build_dir/RegionModel.olean" RegionModel.lean
lean -DwarningAsError=true -o "$proof_build_dir/RegionControl.olean" RegionControl.lean
lean -DwarningAsError=true -o "$proof_build_dir/RegionFrames.olean" RegionFrames.lean
lean -DwarningAsError=true -o "$proof_build_dir/RegionTransitions.olean" RegionTransitions.lean
lean -DwarningAsError=true -o "$proof_build_dir/RegionProperties.olean" RegionProperties.lean
lean -DwarningAsError=true -o "$proof_build_dir/RegionCoherence.olean" RegionCoherence.lean
lean -DwarningAsError=true -o "$proof_build_dir/RegionExamples.olean" RegionExamples.lean
lean -DwarningAsError=true -o "$proof_build_dir/RegionMachineExamples.olean" RegionMachineExamples.lean
