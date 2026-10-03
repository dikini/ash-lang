"""Benchmark the affected closure of pinned, already verified evidence.

This is a timing replay, not a substitute for the reviewed integration gate.
No tracked source or original evidence/cache is written.
"""
import argparse
import json
from pathlib import Path
import shutil
import time

from module_build import build, sha, validate_log


def replay(evidence_path, evidence_sha256, output, jobs=1, module_cache=None):
    if sha(evidence_path) != evidence_sha256:
        raise ValueError("evidence pin mismatch")
    evidence = json.loads(Path(evidence_path).read_text())
    output = Path(output).resolve()
    output.mkdir(parents=True)  # New output only: retain failed runs for diagnosis.
    snapshot, cache = output / "source", output / "artifacts"
    snapshot.mkdir()
    cache.mkdir()
    started = time.monotonic()
    order = evidence["registered_order"]
    affected = evidence["reverse_dependency_closure"]
    if len(order) != len(set(order)) or not set(affected) <= set(order):
        raise ValueError("invalid registered closure")
    for name, digest in evidence["manifest"].items():
        source = Path(evidence["cwd"]) / name
        if sha(source) != digest:
            raise ValueError("frozen source pin mismatch: " + name)
        shutil.copyfile(source, snapshot / name)
    for name in order:
        record = evidence["records"][name]
        artifact = Path(evidence["cache"]) / (name + ".olean")
        if sha(artifact) != record["artifact_sha256"] or sha(record["log"]) != record["log_sha256"]:
            raise ValueError("frozen artifact/log pin mismatch: " + name)
        validate_log(record["log"], record["reports"])
        if record["source_sha256"] != evidence["manifest"][name + ".lean"]:
            raise ValueError("source record mismatch: " + name)
        if set(record["direct_import_artifacts"]) != set(evidence["imports"][name]):
            raise ValueError("dependency record mismatch: " + name)
        for dependency, digest in record["direct_import_artifacts"].items():
            if digest != evidence["records"][dependency]["artifact_sha256"]:
                raise ValueError("incoherent frozen import: " + name)
        if name not in affected:
            # Copies ensure a later retry cannot mutate parent hardlinks.
            shutil.copyfile(artifact, cache / artifact.name)
    preparation_seconds = time.monotonic() - started
    compiler = evidence["records"][order[0]]["command"][0]
    result = build(snapshot=snapshot, cache=cache,
                   store=module_cache or output / "receipts", modules=affected,
                   imports=evidence["imports"],
                   reports={n: evidence["records"][n]["reports"] for n in affected},
                   source_hashes={n: evidence["manifest"][n + ".lean"] for n in affected},
                   compiler=compiler, libraries=evidence["compiler_library_hashes"], jobs=jobs)
    if sha(evidence_path) != evidence_sha256:
        raise ValueError("evidence changed during replay")
    result.update(evidence=str(Path(evidence_path).resolve()), evidence_sha256=evidence_sha256,
                  preparation_seconds=preparation_seconds,
                  total_seconds=time.monotonic() - started,
                  scope="Timing replay of a previously verified closure; not new integration evidence")
    (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("records", "failures")}))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=1)
    parser.add_argument("--module-cache", type=Path)
    args = parser.parse_args()
    result = replay(args.evidence, args.sha256, args.output, args.jobs, args.module_cache)
    raise SystemExit(0 if result["status"] == "complete" else 1)
