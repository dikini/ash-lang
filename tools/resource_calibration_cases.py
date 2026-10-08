#!/usr/bin/env python3
"""Generate bounded Ash calibration inputs and exact-process run manifests.

The generated parameters describe the experiment. They are not work-budget
features: the measurement runner must derive those independently from inputs.
This tool never builds or executes Ash, and never changes compiler policies.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
from typing import Any


SOURCE_ROOT = Path(__file__).resolve().parents[1]
PHASES = [
    "loading",
    "resolution",
    "source-checking",
    "module-linking",
    "linked-interface",
    "final-elaboration",
    "independent-effect-core",
    "evaluation",
    "pipeline",
]
OPTION = "type Option<A> =\nNone\n| Some(A)\n\n"
NATIVE_CASES = [
    (
        "copying",
        "copying",
        "copied_unicode_blobs_nulls_and_empty_values_survive_both_scopes",
        "copying-entry.ash",
    ),
    (
        "persistence",
        "sessions",
        "statement_reuse_transactions_generic_rows_and_reopen_preserve_every_report",
        "session-entry.ash",
    ),
    (
        "resume",
        "control",
        "captured_statement_and_connection_resume_actual_copied_query_without_reacquisition",
        "control-resume.ash",
    ),
    (
        "bound_nul",
        "copying",
        "bound_text_nul_is_an_ordinary_failure_with_both_completion_reports",
        "copying-entry.ash",
    ),
    (
        "forwarding",
        "copying",
        "qualified_forwarding_chain_preserves_integer_and_source_completion",
        "forwarding-chain.ash",
    ),
]


def write_source(path: Path, source: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8", newline="\n")


def flat_program(width: int) -> str:
    definitions = "".join(
        f"identity{index} : Int -> Int\nidentity{index} value = value\n\n"
        for index in range(width)
    )
    calls = "".join(
        f"let ignored{index} = identity{index} 42\n" for index in range(width)
    )
    return definitions + "main : Unit -> Int\nmain () = {\n" + calls + "42\n}\n"


def nested_type(depth: int) -> str:
    return "Option<" * depth + "Int" + ">" * depth


def nested_value(depth: int) -> str:
    return "Some(" * depth + "42" + ")" * depth


def nested_program(depth: int) -> str:
    ty = nested_type(depth)
    return (
        OPTION
        + "identity<A> : A -> A\nidentity value = value\n\n"
        + f"probe : {ty} -> {ty}\nprobe value = identity value\n\n"
        + "main : Unit -> Int\nmain () = {\n"
        + f"let value : {ty} = {nested_value(depth)}\n"
        + f"let kept : {ty} = probe value\n42\n}}\n"
    )


def prerequisite_program(depth: int) -> str:
    ty = nested_type(depth)
    return (
        OPTION
        + "interface Keep<A> {\nkeep : A -> A\n}\n\n"
        + "impl Keep<Int> {\nkeep value = value\n}\n\n"
        + "impl Keep<Option<A>> where Keep<A> {\n"
        + "keep None = None\nkeep (Some(value)) = Some(keep value)\n}\n\n"
        + "main : Unit -> Int\nmain () = {\n"
        + f"let value : {ty} = {nested_value(depth)}\n"
        + f"let kept : {ty} = keep value\n42\n}}\n"
    )


def route_base(width: int) -> str:
    return "".join(
        f"pub interface Marker{index}<A> {{\nmark{index} : A -> A\n}}\n\n"
        f"pub impl Marker{index}<Int> {{\nmark{index} value = value\n}}\n\n"
        for index in range(width)
    )


def reexports(module: str, width: int) -> str:
    selected = [
        item
        for index in range(width)
        for item in (f"Marker{index}", f"mark{index}", f"impl Marker{index}")
    ]
    repeated = [f"impl Marker{index}" for index in range(width)]
    return (
        f"pub import {module} ({', '.join(selected)})\n"
        f"pub import {module} ({', '.join(repeated)})\n"
    )


def route_programs(width: int, depth: int) -> dict[str, str]:
    sources = {"base.ash": route_base(width)}
    dependency = "base"
    for layer in range(depth):
        module = f"layer{layer}"
        sources[f"{module}.ash"] = reexports(dependency, width)
        dependency = module
    sources["entry.ash"] = (
        reexports(dependency, width) + "main : Unit -> Int\nmain () = mark0(42)\n"
    )
    return sources


def string_program(payload_bytes: int) -> str:
    # ASCII makes decoded UTF-8 length equal the explicit payload parameter.
    # The single literal varies bytes while keeping the source AST shape fixed.
    return (
        "main : Unit -> Int\nmain () = {\nlet payload = \""
        + "x" * payload_bytes
        + "\"\n42\n}\n"
    )


def local_module_inputs(entry: Path, support_root: Path | None = None) -> list[Path]:
    """Find relative filesystem imports in these known generated/test fixtures.

    Builtin and foreign interfaces are synthetic compiler inputs, not invented
    source files here. The measured driver remains authoritative for its graph.
    """
    pending = [entry]
    found: set[Path] = set()
    while pending:
        path = pending.pop().resolve()
        if path in found:
            continue
        source = path.read_text(encoding="utf-8")
        found.add(path)
        for name in re.findall(r"^(?:pub\s+)?import\s+([a-z][a-zA-Z0-9_]*)\b", source, re.M):
            dependency = path.parent / f"{name}.ash"
            if not dependency.exists() and support_root is not None:
                dependency = support_root / f"{name}.ash"
            pending.append(dependency)
    return sorted(found)


def input_hashes(paths: list[Path]) -> dict[str, str]:
    return {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def generated_case(
    output: Path,
    cli: Path,
    family: str,
    parameters: dict[str, int],
    held_out: bool,
    sources: dict[str, str],
) -> dict[str, Any]:
    suffix = "-".join(f"{key}{value}" for key, value in parameters.items())
    case_id = f"{family}-{suffix}"
    directory = output / "inputs" / case_id
    for name, source in sources.items():
        write_source(directory / name, source)
    entry = directory / "entry.ash"
    paths = local_module_inputs(entry)
    return {
        "id": case_id,
        "family": family,
        "parameters": parameters,
        "argv": [str(cli), str(entry)],
        "cwd": str(SOURCE_ROOT),
        "expected_exit": 0,
        "expected_stdout": "42 : Int\n",
        "held_out": held_out,
        "entry_path": str(entry),
        "input_paths": [str(path) for path in paths],
        "input_sha256": input_hashes(paths),
        "required_phases": PHASES,
    }


def native_cases(output: Path, binaries: dict[str, Path]) -> list[dict[str, Any]]:
    fixture_root = SOURCE_ROOT / "tests/fixtures/provider-experiments/sqlite-copying"
    cases = []
    for name, binary_kind, test_name, entry_name in NATIVE_CASES:
        entry = fixture_root / entry_name
        paths = local_module_inputs(entry)
        contract: dict[str, Any] = {"kind": "unchanged_exact_native_test"}
        if name == "bound_nul":
            before = 'Sqlite.TextValue "héllo 世界"'
            after = 'Sqlite.TextValue "nul\\0text"'
            original = entry.read_text(encoding="utf-8")
            if original.count(before) != 1:
                raise ValueError("bound-NUL fixture no longer has exactly one replacement site")
            snapshot = output / "native-inputs/bound_nul/copying-entry.ash"
            write_source(snapshot, original.replace(before, after))
            paths = sorted(snapshot if path == entry else path for path in paths)
            contract["replacement"] = {"before": before, "after": after}
            contract["snapshot_path"] = str(snapshot)
        elif name == "persistence":
            contract["runtime_path_substitution"] = {
                "placeholder": "__SQLITE_FILE__",
                "replacement": "isolated temporary database path generated by unchanged test",
            }
        harness = SOURCE_ROOT / f"tests/provider_sqlite_{binary_kind}.rs"
        if f"fn {test_name}()" not in harness.read_text(encoding="utf-8"):
            raise ValueError(f"exact native test is absent from {harness}: {test_name}")
        test_paths = [harness, SOURCE_ROOT / "tests/support/sqlite_copying.rs"]
        cases.append(
            {
                "id": f"sqlite-{name}",
                "family": "sqlite",
                "parameters": {"program": name},
                "argv": [str(binaries[binary_kind]), test_name, "--exact", "--test-threads=1", "--nocapture"],
                "cwd": str(SOURCE_ROOT),
                "expected_exit": 0,
                "expected_test_count": 1,
                "held_out": True,
                "entry_path": str(entry),
                "input_paths": [str(path) for path in paths],
                "input_sha256": input_hashes(paths),
                "test_source_paths": [str(path) for path in test_paths],
                "test_source_sha256": input_hashes(test_paths),
                "input_contract": contract,
                "required_phases": PHASES,
            }
        )
    return cases


def resource_program(width: int) -> str:
    definitions = "".join(
        f"session{index} : Unit -> Provider.Scope<Sqlite.OpenError, Sqlite.CloseError, Int>\n"
        f"session{index} () = resource Sqlite.Connection<C{index}> db{index} = Sqlite.InMemory {{\n42\n}}\n\n"
        for index in range(width)
    )
    calls = "".join(f"let report{index} = session{index} ()\n" for index in range(width))
    return (
        "import provider as Provider\nimport sqlite as Sqlite\n\n"
        + definitions
        + "main : Unit -> Int\nmain () = {\n"
        + calls
        + "42\n}\n"
    )


def resource_cases(output: Path, binary: Path) -> list[dict[str, Any]]:
    fixture_root = SOURCE_ROOT / "tests/fixtures/provider-experiments/sqlite-copying"
    harness = SOURCE_ROOT / "tests/resource_calibration_native.rs"
    test_name = "generated_resource_sessions_close_every_connection"
    if f"fn {test_name}()" not in harness.read_text(encoding="utf-8"):
        raise ValueError(f"exact resource test is absent from {harness}: {test_name}")
    test_paths = [harness, SOURCE_ROOT / "tests/support/sqlite_copying.rs"]
    cases = []
    for index, width in enumerate((1, 2, 4, 8)):
        case_id = f"resource_width-width{width}"
        entry = output / "inputs" / case_id / "entry.ash"
        write_source(entry, resource_program(width))
        paths = local_module_inputs(entry, fixture_root)
        cases.append(
            {
                "id": case_id,
                "family": "resource_width",
                "parameters": {"width": width},
                "argv": [str(binary), test_name, "--exact", "--test-threads=1", "--nocapture"],
                "env": {
                    "ASH_CALIBRATION_ENTRY": str(entry),
                    "ASH_CALIBRATION_SESSIONS": str(width),
                },
                "cwd": str(SOURCE_ROOT),
                "expected_exit": 0,
                "expected_test_count": 1,
                "held_out": index % 2 == 1,
                "entry_path": str(entry),
                "input_paths": [str(path) for path in paths],
                "input_sha256": input_hashes(paths),
                "test_source_paths": [str(path) for path in test_paths],
                "test_source_sha256": input_hashes(test_paths),
                "input_contract": {
                    "kind": "generated_entry_with_unchanged_fixture_support",
                    "runtime_entry_name": "calibration-entry.ash",
                    "support_root": str(fixture_root),
                },
                "required_phases": PHASES,
            }
        )
    return cases


def generate(args: argparse.Namespace) -> dict[str, Any]:
    output = args.output.resolve()
    cli = args.cli.resolve()
    cases = []
    for index, width in enumerate((1, 2, 4, 8, 16, 32, 64, 128)):
        cases.append(generated_case(output, cli, "flat", {"width": width}, index % 2 == 1, {"entry.ash": flat_program(width)}))
    for family, builder in (("nested_type", nested_program), ("prerequisite", prerequisite_program)):
        for index, depth in enumerate((1, 2, 4, 8, 12, 16)):
            cases.append(generated_case(output, cli, family, {"depth": depth}, index % 2 == 1, {"entry.ash": builder(depth)}))
    for index, width in enumerate((1, 2, 4, 8, 16, 32)):
        cases.append(generated_case(output, cli, "reexport_width", {"width": width, "depth": 2}, index % 2 == 1, route_programs(width, 2)))
    for index, depth in enumerate((1, 2, 4, 8, 12, 16)):
        cases.append(generated_case(output, cli, "reexport_depth", {"width": 1, "depth": depth}, index % 2 == 1, route_programs(1, depth)))
    for index, length in enumerate((16, 1024, 65536)):
        cases.append(generated_case(output, cli, "string_payload", {"payload_bytes": length}, index == 2, {"entry.ash": string_program(length)}))
    cases.extend(native_cases(output, {"copying": args.copying_test.resolve(), "sessions": args.sessions_test.resolve(), "control": args.control_test.resolve()}))
    if args.resource_test is not None:
        cases.extend(resource_cases(output, args.resource_test.resolve()))
    manifest = {
        "schema_version": 1,
        "source_root": str(SOURCE_ROOT),
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "purpose": "Calibration evidence; generated parameters are not budget features or acceptance policy.",
        "cases": cases,
    }
    output.mkdir(parents=True, exist_ok=True)
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    selected = []
    seen = set()
    for case in cases:
        if case["family"] == "sqlite" or case["family"] not in seen:
            selected.append(case)
            seen.add(case["family"])
    smoke = {**manifest, "purpose": "Smallest generated case per family and all five unchanged native anchors.", "cases": selected}
    (output / "smoke-manifest.json").write_text(json.dumps(smoke, indent=2) + "\n", encoding="utf-8")
    return {"manifest": str(output / "manifest.json"), "smoke_manifest": str(output / "smoke-manifest.json"), "cases": len(cases), "smoke_cases": len(selected)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    generate_parser = commands.add_parser("generate", help="write inputs and manifests; never execute them")
    generate_parser.add_argument("--output", type=Path, required=True)
    generate_parser.add_argument("--cli", type=Path, required=True)
    generate_parser.add_argument("--copying-test", type=Path, required=True)
    generate_parser.add_argument("--sessions-test", type=Path, required=True)
    generate_parser.add_argument("--control-test", type=Path, required=True)
    generate_parser.add_argument("--resource-test", type=Path, help="optional exact native resource-width test binary")
    args = parser.parse_args()
    print(json.dumps(generate(args), indent=2))


if __name__ == "__main__":
    main()
