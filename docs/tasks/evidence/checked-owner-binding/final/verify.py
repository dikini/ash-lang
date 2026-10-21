"""Verify exact final inputs and raw command results without building or executing Ash."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
NAMES = ["binding", "foreign", "resource", "owners", "images", "imports", "capture", "integrations", "clippy"]
common = None
unique = set()
commands = []
for name in NAMES:
    stem = "final-" + name
    receipt = json.loads((HERE / (stem + ".receipt.json")).read_text())
    inputs = json.loads((HERE / (stem + ".inputs.json")).read_text())
    raw = (HERE / (stem + ".log")).read_bytes()
    assert receipt["exit_code"] == 0 and receipt["inputs_equal"]
    assert inputs["before"] == inputs["after"]
    pins = inputs["before"]
    aggregate = hashlib.sha256(json.dumps(pins, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    assert aggregate == receipt["aggregate_sha256"]
    assert len(pins) == receipt["count"]
    assert hashlib.sha256(raw).hexdigest() == receipt["log_sha256"]
    assert all(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == wanted for path, wanted in pins.items())
    if common is None:
        common = pins
    assert common == pins
    text = raw.decode()
    passes = re.findall(r"^test (\S+) \.\.\. ok$", text, re.M)
    assert not re.search(r"test result: FAILED", text)
    unique.update(passes)
    commands.append({"name": name, "command": receipt["command"], "pass_lines": len(passes), "seconds": receipt["seconds"]})
report = {"commands": commands, "input_count": len(common), "input_aggregate_sha256": aggregate, "all_before_after_and_current_pins_equal": True, "distinct_passing_test_names": len(unique), "clippy_exit_code": 0}
print(json.dumps(report, indent=2))
