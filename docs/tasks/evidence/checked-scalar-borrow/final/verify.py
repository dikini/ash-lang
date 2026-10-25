"""Read-only source/input/raw-result verification; executes no Ash artifacts."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import sys

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[5]
EVIDENCE = ROOT / "docs/tasks/evidence/checked-scalar-borrow"
FINAL = Path(os.environ.get("ASH_RECEIPT_DIR", str(EVIDENCE / "final")))
SPEC = importlib.util.spec_from_file_location("borrow_receipts", EVIDENCE / "test-first/run.py")
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def aggregate(mapping):
    return digest(json.dumps(mapping, sort_keys=True, separators=(",", ":")).encode())


def verify():
    current = RUNNER.pins()
    histories = 0
    for receipt_path in EVIDENCE.rglob("*.receipt.json"):
        if receipt_path.parent == EVIDENCE / "final":
            continue
        stem = receipt_path.name.removesuffix(".receipt.json")
        receipt = json.loads(receipt_path.read_text())
        maps = json.loads((receipt_path.parent / (stem + ".inputs.json")).read_text())
        assert maps["before"] == maps["after"], receipt_path
        assert len(maps["before"]) == receipt["count"], receipt_path
        assert aggregate(maps["before"]) == receipt["aggregate_sha256"], receipt_path
        assert digest((receipt_path.parent / (stem + ".log")).read_bytes()) == receipt["log_sha256"], receipt_path
        histories += 1
    names = ["private", "integration", "provider", "resource", "capture", "foreign", "images", "clippy"]
    passed = set()
    lines = 0
    results = []
    for name in names:
        stem = "final-" + name
        receipt = json.loads((FINAL / (stem + ".receipt.json")).read_text())
        maps = json.loads((FINAL / (stem + ".inputs.json")).read_text())
        raw = (FINAL / (stem + ".log")).read_bytes()
        assert receipt["exit_code"] == 0, name
        assert receipt["inputs_equal"] and maps["before"] == maps["after"] == current, name
        assert len(current) == receipt["count"] and aggregate(current) == receipt["aggregate_sha256"], name
        assert digest(raw) == receipt["log_sha256"], name
        tests = re.findall(r"^test (\S+) \.\.\. ok$", raw.decode(), re.M)
        assert tests or name == "clippy", name
        passed.update(tests)
        lines += len(tests)
        results.append({"name": name, "passed_lines": len(tests), "log_sha256": digest(raw)})
    images = (FINAL / "final-images.log").read_text()
    buffer = int(re.search(r"startup after reconstruction: (\d+)", images)[1])
    dependent = int(re.search(r"cumulative checked-library work=(\d+)", images)[1])
    assert 0 < buffer < 327680 and 0 < dependent < 327680
    assert len(re.findall(r"^test \S+ \.\.\. ok$", images, re.M)) == 16
    return {"inputs": len(current), "aggregate_sha256": aggregate(current),
            "aggregate_algorithm": "SHA256 of sorted-key compact JSON UTF-8 no newline",
            "distinct_passes": len(passed), "passing_lines": lines,
            "buffer_startup": buffer, "dependent_startup": dependent,
            "startup_limit": 327680, "historical_receipts": histories,
            "commands": results, "scope": "Focused static delivery; no F-core or checked runtime/native execution"}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
