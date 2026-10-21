"""Capture one explicitly supplied verification command and its source input maps."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[5]
OUT = Path(os.environ.get("ASH_RECEIPT_DIR", "/tmp/ash-pr97"))


def pins():
    paths = set(json.loads((ROOT / "docs/tasks/evidence/checked-nominal-closure/final/closure.inputs.json").read_text()))
    for directory in ["src", "tests", "spec"]:
        paths.update(str(path.relative_to(ROOT)) for path in (ROOT / directory).rglob("*") if path.is_file())
    for directory in ["libraries", "foreign-adapter"]:
        paths.update(str(path.relative_to(ROOT)) for path in (ROOT / directory).rglob("*")
                     if path.is_file() and path.suffix in {".ash", ".rs", ".toml", ".c", ".h", ".json"})
    paths.update({"docs/tasks/plans/checked-ffi-contract-carriers.md",
                  str(Path(__file__).resolve().relative_to(ROOT))})
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in sorted(paths) if (ROOT / name).is_file()}


def main():
    name, *command = sys.argv[1:]
    OUT.mkdir(parents=True, exist_ok=True)
    before = pins()
    environment = os.environ.copy()
    environment.update(RUSTC_WRAPPER="", CARGO_BUILD_JOBS="1",
                       CARGO_TARGET_DIR="/home/dikini/Projects/ash-lang/.worktree/generic-cells/target")
    started = time.monotonic()
    with (OUT / (name + ".log")).open("wb") as log:
        result = subprocess.run(command, cwd=ROOT, env=environment, stdout=log, stderr=subprocess.STDOUT)
    after = pins()
    (OUT / (name + ".inputs.json")).write_text(json.dumps({"before": before, "after": after}, indent=2) + "\n")
    receipt = {
        "command": command, "cwd": str(ROOT), "exit_code": result.returncode,
        "seconds": round(time.monotonic() - started, 3), "inputs_equal": before == after,
        "count": len(before), "aggregate_algorithm": "SHA256 of sorted-key compact JSON UTF-8 no newline",
        "aggregate_sha256": hashlib.sha256(json.dumps(before, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
        "log_sha256": hashlib.sha256((OUT / (name + ".log")).read_bytes()).hexdigest(),
        "environment": {key: environment.get(key) for key in
                        ["RUSTC_WRAPPER", "CARGO_BUILD_JOBS", "CARGO_TARGET_DIR", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"]},
    }
    (OUT / (name + ".receipt.json")).write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt))
    return result.returncode


if __name__ == "__main__":
    sys.exit(main())
