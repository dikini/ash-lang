"""Verify final command receipts against their raw logs and current frozen inputs."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("lifecycle_receipt_runner", HERE / "run.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

BASE = ["cargo", "test", "-p", "ash", "--locked", "--lib"]
COMMANDS = {
    "checked": BASE + ["checked_", "--", "--nocapture"],
    "foreign": BASE + ["foreign::", "--", "--nocapture"],
    "imports": BASE + ["imported_", "--", "--nocapture"],
    "resource": BASE + ["core::source_resource::tests", "--", "--nocapture"],
    "capture": BASE + ["core::capture::tests", "--", "--nocapture"],
    "images": BASE + ["source_resource_image", "--", "--nocapture"],
    "owners": BASE + ["source_owner_post_record", "--", "--nocapture"],
    "deep": BASE + ["freeze_rejects_", "--", "--nocapture"],
    "integrations": ["cargo", "test", "-p", "ash", "--locked",
                     "--test", "checked_foreign_owners", "--test", "checked_foreign_host",
                     "--test", "checked_foreign_lifecycle", "--test", "foreign_source_owner_contracts",
                     "--test", "foreign_source_owner_admission", "--", "--nocapture"],
    "clippy": ["cargo", "clippy", "-p", "ash", "--locked", "--lib", "--tests", "--", "-D", "warnings"],
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(directory):
    current = runner.pins()
    aggregate = digest(json.dumps(current, sort_keys=True, separators=(",", ":")).encode())
    names = set()
    qualified = set()
    lines = 0
    records = {}
    for name, command in COMMANDS.items():
        receipt = json.loads((directory / (name + ".receipt.json")).read_text())
        maps = json.loads((directory / (name + ".inputs.json")).read_text())
        raw = (directory / (name + ".log")).read_bytes()
        assert receipt["command"] == command, (name, "command")
        assert receipt["exit_code"] == 0, (name, "exit", receipt["exit_code"])
        assert receipt["inputs_equal"] and maps["before"] == maps["after"] == current, (name, "inputs")
        assert receipt["count"] == len(current) and receipt["aggregate_sha256"] == aggregate, (name, "aggregate")
        assert receipt["log_sha256"] == digest(raw), (name, "raw digest")
        target = "lib"
        passed = []
        for line in raw.decode().splitlines():
            match = re.search(r"Running tests/([^ ]+)\.rs", line)
            if match:
                target = match.group(1)
            for test in re.findall(r"\btest ([A-Za-z_][A-Za-z0-9_:]*) \.\.\. ok\b", line):
                names.add(test)
                qualified.add(target + "::" + test)
                passed.append(test)
                lines += 1
        records[name] = {"exit_code": 0, "passing_lines": len(passed), "log_sha256": digest(raw)}
    image_log = (directory / "images.log").read_text()
    assert "16 passed; 0 failed" in image_log
    assert "30 passed; 0 failed" in (directory / "resource.log").read_text()
    buffer = int(re.search(r"buffer startup after reconstruction: (\d+)", image_log).group(1))
    dependent = int(re.search(r"dependent discard image:.*?cumulative checked-library work=(\d+)", image_log).group(1))
    assert buffer <= 327680 and dependent <= 327680
    result = {
        "all_commands_pass": True, "current_complete_input_maps_equal": True,
        "input_count": len(current), "aggregate_algorithm": "SHA256 of sorted-key compact JSON UTF-8 no newline",
        "aggregate_sha256": aggregate, "distinct_test_names": len(names),
        "distinct_target_qualified_tests": len(qualified), "passing_lines": lines,
        "test_ids": sorted(qualified), "commands": records,
        "images": "16/16", "source_resource": "30/30", "clippy_exit_code": 0,
        "startup": {"buffer": buffer, "dependent_discard": dependent, "unchanged_default": 327680},
        "scope": "Static checks only; no checked evaluator/native/image execution or whole F3/F-core acceptance.",
    }
    return current, result


if __name__ == "__main__":
    directory = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    current, result = verify(directory)
    (directory / "source.inputs.json").write_text(json.dumps(current, indent=2) + "\n")
    (directory / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key not in {"test_ids", "commands"}}))
