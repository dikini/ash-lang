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

from ash_indent import indent_source


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


def write_source(path: Path, source: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(indent_source(source), encoding="utf-8", newline="\n")


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
        if case["family"] not in seen:
            selected.append(case)
            seen.add(case["family"])
    smoke = {**manifest, "purpose": "Smallest generated case per family.", "cases": selected}
    (output / "smoke-manifest.json").write_text(json.dumps(smoke, indent=2) + "\n", encoding="utf-8")
    return {"manifest": str(output / "manifest.json"), "smoke_manifest": str(output / "smoke-manifest.json"), "cases": len(cases), "smoke_cases": len(selected)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    generate_parser = commands.add_parser("generate", help="write inputs and manifests; never execute them")
    generate_parser.add_argument("--output", type=Path, required=True)
    generate_parser.add_argument("--cli", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(generate(args), indent=2))


if __name__ == "__main__":
    main()
