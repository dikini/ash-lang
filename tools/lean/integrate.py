"""Compile a reviewed source delta and its reverse consumers once.

No tracked writes: assemble in a new snapshot/cache. Root copies the exact
reviewed sources and registrations only after the coherent gate passes.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

from module_build import build

if not __debug__:
    raise RuntimeError("Proof gates require Python assertion checks; do not use -O")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_pinned(path, digest):
    contents = Path(path).read_bytes()
    assert hashlib.sha256(contents).hexdigest() == digest, (path, "stale pin")
    return json.loads(contents)


def registration_plan(parent_order, new, patches, insertions, original_script):
    """Insert declared new modules before existing anchors; append the rest."""
    assert len(parent_order) == len(set(parent_order)), "Duplicate parent registration"
    assert len(new) == len(set(new)) and set(new) == set(patches) - set(parent_order)
    assert isinstance(insertions, list), "insert_before must be a list"
    anchors = {}
    for insertion in insertions:
        assert isinstance(insertion, dict) and set(insertion) == {"module", "before"}
        name, anchor = insertion["module"], insertion["before"]
        assert name in new and name not in anchors, (name, "duplicate or non-new insertion")
        assert anchor in parent_order, (anchor, "missing parent anchor")
        anchors[name] = anchor
    registered = [line.split()[-1].removesuffix(".lean")
                  for line in original_script.splitlines() if line.startswith("lean ")]
    assert registered == parent_order, "Parent registration script mismatch"
    before = {anchor: [name for name in new if anchors.get(name) == anchor]
              for anchor in parent_order}
    appended = [name for name in new if name not in anchors]
    modules = [name for anchor in parent_order for name in before[anchor] + [anchor]] + appended
    command = lambda name: f'lean -DwarningAsError=true -o "$proof_build_dir/{name}.olean" {name}.lean'
    lines = []
    for line in original_script.rstrip().splitlines():
        if line.startswith("lean "):
            anchor = line.split()[-1].removesuffix(".lean")
            lines.extend(command(name) for name in before[anchor])
        lines.append(line)
    script = "\n".join(lines) + "\n"
    if appended:
        script += "\n".join(command(name) for name in appended) + "\n"
    assert [line.split()[-1].removesuffix(".lean") for line in script.splitlines()
            if line.startswith("lean ")] == modules
    return modules, script


configuration_path = Path(sys.argv[1]).resolve()
configuration_contents = configuration_path.read_bytes()
configuration_sha256 = hashlib.sha256(configuration_contents).hexdigest()
configuration = json.loads(configuration_contents)
parent_path = Path(configuration["parent_evidence"])
parent = read_pinned(parent_path, configuration["parent_evidence_sha256"])
work = Path(configuration["worktree"])
live = work / "docs/design/direct-effects/one-shot"
head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=work, text=True).strip()
assert head == configuration["parent_head"]
prefix = Path(configuration["output_prefix"])
snapshot = Path(str(prefix) + "-source-snapshot")
cache = Path(str(prefix) + "-review-cache")
assert not snapshot.exists() and not cache.exists(), "Use a new frozen output prefix"
assert sha(live / "check.sh") == parent["manifest"]["check.sh"]
compiler = Path(configuration["compiler"]) if "compiler" in configuration else Path(
    subprocess.check_output(["elan", "which", "lean"], cwd=live, text=True).strip())
assert subprocess.check_output([str(compiler), "--version"], text=True).strip() == parent["version"]

patches = {}
components = []
for component in configuration["components"]:
    assert component["root_verified_review_pass"] is True
    checkpoint_path = Path(component["checkpoint"])
    review_path = Path(component["review"])
    read_pinned(checkpoint_path, component["checkpoint_sha256"])
    read_pinned(review_path, component["review_sha256"])
    for record in component["sources"]:
        name = record["module"]
        assert re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name)
        assert name not in patches, (name, "conflicting component ownership")
        path = Path(record["source"])
        assert sha(path) == record["source_sha256"]
        patches[name] = {**record, "component": component["name"]}
    components.append({"name": component["name"], "checkpoint": str(checkpoint_path),
                       "checkpoint_sha256": sha(checkpoint_path), "review": str(review_path),
                       "review_sha256": sha(review_path)})
assert patches
new = configuration["new_registered_order"]
modules, script_text = registration_plan(parent["registered_order"], new, patches,
                                         configuration.get("insert_before", []),
                                         (live / "check.sh").read_text())
started = time.monotonic()
snapshot.mkdir(parents=True)
cache.mkdir()
manifest = {}
imports = {}
changed = set()
seen = set()
for name in modules:
    original = live / (name + ".lean")
    if name in parent["records"]:
        assert sha(original) == parent["records"][name]["source_sha256"], (name, "live source drift")
    else:
        assert not original.exists(), (name, "new source already tracked/present")
    source = Path(patches[name]["source"]) if name in patches else original
    destination = snapshot / source.with_name(name + ".lean").name
    shutil.copyfile(source, destination)
    digest = sha(destination)
    manifest[name + ".lean"] = digest
    if name not in parent["records"] or digest != parent["records"][name]["source_sha256"]:
        changed.add(name)
    dependencies = [dependency for line in destination.read_text().splitlines()
                    if line.startswith("import ") for dependency in line.split()[1:]
                    if dependency in modules]
    assert all(dependency in seen for dependency in dependencies), (name, "productive import order")
    imports[name] = dependencies
    seen.add(name)
assert changed, "No source delta"

# Include both old and new edges: a removed dependency still gets rechecked.
affected = set(changed)
while True:
    successors = {name for name in modules if
                  (set(imports[name]) | set(parent["imports"].get(name, []))) & affected}
    enlarged = affected | successors
    if enlarged == affected:
        break
    affected = enlarged
fresh_order = [name for name in modules if name in affected]
(snapshot / "check.sh").write_text(script_text)
assert [line.split()[-1].removesuffix(".lean") for line in script_text.splitlines()
        if line.startswith("lean ")] == modules
shutil.copyfile(live / "lean-toolchain", snapshot / "lean-toolchain")
for name in ["check.sh", "lean-toolchain"]:
    manifest[name] = sha(snapshot / name)
libraries = parent["compiler_library_hashes"]
for path, digest in libraries.items():
    assert sha(path) == digest
records = {}
for name in parent["registered_order"]:
    old = parent["records"][name]
    artifact = Path(parent["cache"]) / (name + ".olean")
    log = Path(old["log"])
    assert sha(artifact) == old["artifact_sha256"] and sha(log) == old["log_sha256"]
    if name in affected:
        continue
    assert imports[name] == parent["imports"][name]
    os.link(artifact, cache / artifact.name)
    os.link(log, cache / (name + ".log"))
    records[name] = {**old, "log": str(cache / (name + ".log")),
                     "copied_artifact": str(cache / artifact.name),
                     "fresh_for_this_integration": False,
                     "reuse_evidence": str(parent_path),
                     "reuse_evidence_sha256": sha(parent_path)}
preparation_seconds = time.monotonic() - started

registrations = {line.split()[-1].removesuffix(".lean"): line
                 for line in script_text.splitlines() if line.startswith("lean ")}
replay = Path(str(prefix) + "-productive-replay.sh")
replay.write_text("#!/usr/bin/env bash\nset -euo pipefail\nproof_build_dir=" + str(cache) + "\n" +
                  "\n".join(registrations[name] + f' > "$proof_build_dir/{name}.log" 2>&1'
                            for name in fresh_order) + "\n")
expected_reports = {name: patches[name]["reports"] if name in patches
                    else parent["records"][name]["reports"] for name in fresh_order}
module_result = build(
    snapshot=snapshot, cache=cache,
    store=Path(configuration.get("module_cache", str(work / "target/lean-module-cache"))),
    modules=fresh_order, imports=imports, reports=expected_reports,
    source_hashes={name: manifest[name + ".lean"] for name in fresh_order},
    compiler=compiler, libraries=libraries,
    jobs=configuration.get("jobs", 1), memory_mb=configuration.get("memory_mb", 4096),
    headroom_mb=configuration.get("headroom_mb", 4096))
progress_path = Path(str(prefix) + "-module-progress.json")
progress_path.write_text(json.dumps(module_result, indent=2) + "\n")
if module_result["status"] != "complete":
    print(json.dumps({"status": module_result["status"], "progress": str(progress_path),
                      "successes": len(module_result["records"]),
                      "failed": list(module_result["failures"]),
                      "blocked": module_result["blocked"], "pending": module_result["pending"]}))
    raise SystemExit(1)
compile_seconds = module_result["wall_seconds"]
environment = dict(os.environ, LEAN_PATH=str(cache),
                   PATH=str(compiler.parent) + ":" + os.environ["PATH"])
for name in fresh_order:
    log = cache / (name + ".log")
    output = log.read_text()
    reports = re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", output)
    assert not re.search(r"\b(?:error:|warning:|sorryAx)", output), name
    axioms = {atom.strip() for block in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
              for atom in block.split(",")}
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, name
    if name in parent["records"] and name not in changed:
        assert reports == parent["records"][name]["reports"], (name, "unchanged-source report names")
    if name in patches:
        assert reports == patches[name]["reports"], (name, "reviewed report names")
    deps_output = subprocess.check_output([str(compiler), "--deps", name + ".lean"],
                                         cwd=snapshot, env=environment, text=True)
    for dependency in imports[name]:
        assert str(cache / (dependency + ".olean")) in deps_output, (name, dependency)
    record = {"source_sha256": manifest[name + ".lean"],
              "artifact_sha256": sha(cache / (name + ".olean")), "log": str(log),
              "log_sha256": sha(log), "reports": reports, "exit_code": 0,
              "command": module_result["records"][name]["command"],
              "origin_cwd": module_result["records"][name]["origin_cwd"],
              "origin_lean_path": module_result["records"][name]["origin_lean_path"],
              "fresh_for_this_integration": not module_result["records"][name]["cache_hit"],
              "module_build": module_result["records"][name],
              "direct_import_artifacts": {d: sha(cache / (d + ".olean")) for d in imports[name]}}
    if name in patches:
        record["reviewed_component"] = patches[name]["component"]
        record["reviewed_source"] = str(patches[name]["source"])
    if name in parent["records"]:
        record["previous_artifact_sha256"] = parent["records"][name]["artifact_sha256"]
        record["previous_direct_import_artifacts"] = parent["records"][name]["direct_import_artifacts"]
    records[name] = record

for name in modules:
    record = records[name]
    assert sha(snapshot / (name + ".lean")) == record["source_sha256"]
    assert sha(cache / (name + ".olean")) == record["artifact_sha256"]
    assert sha(record["log"]) == record["log_sha256"]
    assert set(record["direct_import_artifacts"]) == set(imports[name])
    for dependency, digest in record["direct_import_artifacts"].items():
        assert sha(cache / (dependency + ".olean")) == digest, (name, "coherent selected import")
for path, digest in libraries.items():
    assert sha(path) == digest
for name in parent["registered_order"]:
    assert sha(live / (name + ".lean")) == parent["records"][name]["source_sha256"]
assert sha(live / "check.sh") == parent["manifest"]["check.sh"]
for name, patch in patches.items():
    assert sha(patch["source"]) == patch["source_sha256"]
assert sha(configuration_path) == configuration_sha256, "Configuration changed during build"
assert sha(parent_path) == configuration["parent_evidence_sha256"], "Parent evidence changed during build"
for component in components:
    assert sha(component["checkpoint"]) == component["checkpoint_sha256"]
    assert sha(component["review"]) == component["review_sha256"]
assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=work, text=True).strip() == head
report_pattern = r"^'[^']+' (?:depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)\n?"
aggregate = "".join("".join(re.findall(report_pattern, Path(records[name]["log"]).read_text(), re.M))
                    for name in modules)
Path(str(prefix) + "-proof.log").write_text(aggregate)
Path(str(prefix) + "-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
evidence = {"cwd": str(snapshot), "cache": str(cache), "lean_path": str(cache),
            "version": parent["version"], "compiler_library_hashes": libraries,
            "manifest": manifest, "registered_order": modules, "imports": imports,
            "records": records, "reports": sum(len(r["reports"]) for r in records.values()),
            "changed_source_modules": [name for name in modules if name in changed],
            "reverse_dependency_closure": fresh_order,
            "all_modules_fresh": all(r["fresh_for_this_integration"] for r in records.values()),
            "old_external_artifact_count": 0,
            "selected_external_artifacts": {name: {"selected_path": str(cache / (name + ".olean")),
                                            "olean_sha256": records[name]["artifact_sha256"]} for name in modules},
            "parent_head": head, "parent_evidence": str(parent_path),
            "parent_evidence_sha256": sha(parent_path), "reviewed_components": components,
            "configuration": str(configuration_path), "configuration_sha256": configuration_sha256,
            "build_script": str(Path(__file__).resolve()), "build_script_sha256": sha(__file__),
            "productive_registration_replay": {"script": str(replay), "script_sha256": sha(replay),
                                                "execution": "reference only; dependency scheduler executed the modules",
                                                "modules": fresh_order},
            "module_scheduler": {"progress": str(progress_path), "progress_sha256": sha(progress_path),
                                 "script": str(Path(__file__).with_name("module_build.py")),
                                 "script_sha256": sha(Path(__file__).with_name("module_build.py")),
                                 "jobs": module_result["jobs"], "max_running": module_result["max_running"],
                                 "cache_hits": sum(r["cache_hit"] for r in module_result["records"].values()),
                                 "compiled_modules": [n for n in fresh_order
                                                      if not module_result["records"][n]["cache_hit"]],
                                 "memory_mb": module_result["memory_mb"],
                                 "headroom_mb": module_result["headroom_mb"]},
            "timing": {"preparation_and_hash_checks_seconds": preparation_seconds,
                       "batched_affected_compile_seconds": compile_seconds},
            "scope": "Changed sources and the union of old/new reverse consumers checked by a bounded dependency scheduler. Matching independently validated successful module receipts may be reused. Unaffected frozen artifacts and logs reused through immutable hardlinks. Every selected direct-import hash rechecked. Independently reviewed source deltas are checked against coalesced dependencies through compilation or exact validated receipt reuse; no claim that changed-dependency artifacts equal isolated worker artifacts. No tracked writes."}
evidence_path = Path(str(prefix) + "-evidence.json")
evidence_path.write_text(json.dumps(evidence, indent=2) + "\n")
print(json.dumps({"modules": len(modules), "reports": evidence["reports"],
                  "changed_sources": len(changed), "affected_consumers": len(fresh_order),
                  "fresh_consumers": len(evidence["module_scheduler"]["compiled_modules"]),
                  "receipt_cache_hits": evidence["module_scheduler"]["cache_hits"],
                  "reused": len(modules) - len(evidence["module_scheduler"]["compiled_modules"]),
                  "timing": evidence["timing"],
                  "evidence": str(evidence_path), "evidence_sha256": sha(evidence_path)}))
