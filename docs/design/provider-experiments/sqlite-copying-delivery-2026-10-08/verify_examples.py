from pathlib import Path
import json, re, shutil, subprocess, tempfile, time

repo = Path("/home/dikini/Projects/ash-lang/.worktree/sqlite-provider")
evidence = Path(__file__).parent / "host-run"
evidence.mkdir(exist_ok=True)
owned = Path(tempfile.mkdtemp(prefix="ash-sqlite-calibrated-examples-"))
for source in (repo / "docs/design/provider-experiments/examples/sqlite-copying").glob("*.ash"):
    shutil.copyfile(source, owned / source.name)
unit = "Completed(Ok(()), Closed)"
rows = 'Cons(Stored(1, TextValue("héllo 世界"), BlobBytes([0, 255])), Cons(Stored(2, TextValue("héllo 世界"), BlobBytes([0, 255])), Cons(Stored(3, TextValue("third"), BlobBytes([])), Nil)))'
query = f"Completed(Ok({rows}), Closed)"
expected = {
    "text-entry.ash": ('Completed(Completed(Ok(TextValue("héllo 世界")), Closed), Closed)', [13], [13], 1, 1),
    "copying-entry.ash": ('CopySession(Completed(Completed(Ok(Copied(42, TextValue("héllo 世界"), BlobBytes([0, 255]), TextValue(""), BlobBytes([]), NullText, NullBytes, TextValue("世界\\0tail"))), Closed), Closed))', [13, 2, 0, 0], [13, 2, 0, 0, 11], 1, 1),
    "session-entry.ash": (f"SessionReports(Completed(({unit}, {unit}, {unit}, {unit}, {query}), Closed), Completed({query}, Closed))", [13, 2, 5, 0], [13, 2, 13, 2, 5, 0, 13, 2, 13, 2, 5, 0], 2, 6),
    "control-resume.ash": ('Completed(Completed(Ok(CopiedRow(TextValue("héllo 世界"), BlobBytes([0, 255]))), Closed), Closed)', [], [13, 2], 1, 1),
    "control-discard.ash": ("42", [], [], 1, 1),
}
results = []
for entry, (value, inputs, outputs, connections, statements) in expected.items():
    started = time.monotonic()
    run = subprocess.run([str(repo / "target/debug/examples/sqlite_session"), str(owned / entry)], cwd=owned, text=True, capture_output=True)
    (evidence / (entry + ".stdout")).write_text(run.stdout)
    (evidence / (entry + ".stderr")).write_text(run.stderr)
    issues = []
    if run.returncode != 0: issues.append(f"exit {run.returncode}")
    if f"value: {value}\n" not in run.stdout: issues.append("source result mismatch")
    if "retained owners: 0\n" not in run.stdout: issues.append("retained owners")
    for label, sizes in [("InputCopied", inputs), ("OutputCopied", outputs)]:
        actual = [int(n) for n in re.findall(label + r"\((\d+)\)", run.stdout)]
        if actual != sizes: issues.append(f"{label} mismatch: {actual}")
    events = [line for line in run.stdout.splitlines() if line.startswith("observation: ")]
    for operation, count in [("open", connections), ("prepare", statements), ("finalize", statements), ("close", connections)]:
        calls = [i for i, e in enumerate(events) if f'Call {{ operation: "{operation}",' in e]
        if len(calls) != count: issues.append(f"{operation} count")
        if operation in ["finalize", "close"]:
            dispatches = [i for i, e in enumerate(events) if f'FinishDispatched {{ operation: "{operation}" }}' in e]
            if len(dispatches) != count or any(a >= b for a, b in zip(dispatches, calls)): issues.append(f"{operation} dispatch order")
            if any('code: 0 }' not in events[i] for i in calls): issues.append(f"{operation} native status")
    if any("FaultInjected" in e or 'operation: "close_v2"' in e for e in events): issues.append("fault or close_v2")
    phases = [line for line in run.stdout.splitlines() if line.startswith("compiler work: ")]
    if len(phases) != 3 or any("unobserved" in line or "completed=true" not in line for line in phases): issues.append("phase completion report")
    results.append({"entry": entry, "exit_code": run.returncode, "elapsed_seconds": time.monotonic() - started, "issues": issues, "phase_reports": phases})
    (evidence / "results.json").write_text(json.dumps({"owned_directory": str(owned), "results": results}, indent=2) + "\n")
    print(entry, "PASS" if not issues else issues, flush=True)
assert not any(r["issues"] for r in results), results
assert (owned / "session.sqlite3").is_file()
print("All five full source results, copies, phase reports and native completion observations checked.")
