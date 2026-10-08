#!/usr/bin/env python3
"""Generate a small Ash/Rust frontend reference corpus without running engines.

The pairs match declared language structures, not compiler passes or machine
work. Rust metadata compilation includes analyses and metadata serialization;
Ash CLI execution additionally includes effect Core verification and evaluation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import resource_calibration_cases as ash_cases


SOURCE_ROOT = Path(__file__).resolve().parents[1]
FLAT_WIDTHS = (0, 16, 64, 128)
TYPE_DEPTHS = (1, 4, 16, 24, 32)
RUST_OPTION = "enum Option<T> { None, Some(T) }\nuse self::Option::{None, Some};\n\n"
RUST_FLAGS = (
    "--edition=2024",
    "--crate-type=lib",
    "--crate-name=ash_reference",
    "--emit=metadata",
    "-Copt-level=0",
    "-Cdebuginfo=0",
    "-Adead_code",
    "-Aunused_imports",
)
DIFFERENCES = [
    "Ash Int and Rust i64 differ; all inputs are 42, so integer range is not exercised.",
    "Ash performs effect Core verification and evaluates main; Rust emits library metadata without executing run.",
    "Rust performs ownership/borrow analyses and metadata encoding; these do not correspond one-for-one to Ash phases.",
    "Rust loads its implicit standard-library interface; Ash loads its own builtin interfaces. Neither lane rebuilds dependencies.",
    "Source bytes and language-specific AST node counts are recorded separately, not treated as equal units across languages.",
]


def rust_nested_type(depth: int) -> str:
    return "Option<" * depth + "i64" + ">" * depth


def rust_nested_value(depth: int) -> str:
    return "Some(" * depth + "42i64" + ")" * depth


def rust_flat_program(width: int) -> str:
    definitions = "".join(
        f"fn identity{index}(value: i64) -> i64 {{ value }}\n"
        for index in range(width)
    )
    calls = "".join(
        f"    let _ignored{index} = identity{index}(42);\n"
        for index in range(width)
    )
    return definitions + "\npub fn run() -> i64 {\n" + calls + "    42\n}\n"


def rust_nested_program(depth: int) -> str:
    ty = rust_nested_type(depth)
    return (
        RUST_OPTION
        + "fn identity<T>(value: T) -> T { value }\n\n"
        + f"fn probe(value: {ty}) -> {ty} {{ identity(value) }}\n\n"
        + "pub fn run() -> i64 {\n"
        + f"    let value: {ty} = {rust_nested_value(depth)};\n"
        + f"    let _kept: {ty} = probe(value);\n    42\n}}\n"
    )


def rust_prerequisite_program(depth: int) -> str:
    ty = rust_nested_type(depth)
    return (
        RUST_OPTION
        + "trait Keep: Sized {\n    fn keep(value: Self) -> Self;\n}\n\n"
        + "impl Keep for i64 {\n    fn keep(value: Self) -> Self { value }\n}\n\n"
        + "impl<T: Keep> Keep for Option<T> {\n"
        + "    fn keep(value: Self) -> Self {\n"
        + "        match value {\n"
        + "            None => None,\n"
        + "            Some(inner) => Some(T::keep(inner)),\n"
        + "        }\n    }\n}\n\n"
        + "pub fn run() -> i64 {\n"
        + f"    let value: {ty} = {rust_nested_value(depth)};\n"
        + f"    let _kept: {ty} = Keep::keep(value);\n    42\n}}\n"
    )


def pair(
    output: Path,
    cli: Path,
    rustc: Path,
    family: str,
    parameters: dict[str, int],
    ash_source: str,
    rust_source: str,
    shared_structure: dict[str, Any],
) -> dict[str, Any]:
    ash = ash_cases.generated_case(
        output, cli, family, parameters, False, {"entry.ash": ash_source}
    )
    held_out = parameters.get("depth", 0) >= 24
    ash["held_out"] = held_out
    entry = Path(ash["entry_path"]).with_suffix(".rs")
    ash_cases.write_source(entry, rust_source)
    metadata = output / "metadata" / f"{ash['id']}.rmeta"
    metadata.parent.mkdir(parents=True, exist_ok=True)
    differences = list(DIFFERENCES)
    if family == "prerequisite":
        differences.append(
            "Ash Keep<A> uses an explicit interface parameter; Rust Keep represents that parameter as Self with a Sized bound."
        )
    return {
        "id": ash["id"],
        "family": family,
        "parameters": parameters,
        "held_out": held_out,
        "startup_control": family == "flat" and parameters["width"] == 0,
        "shared_structure": shared_structure,
        "differences": differences,
        "ash": ash,
        "rust": {
            "id": f"rust-{ash['id']}",
            "family": family,
            "parameters": parameters,
            "held_out": held_out,
            "argv": [str(rustc), *RUST_FLAGS, str(entry), "-o", str(metadata)],
            "cwd": str(SOURCE_ROOT),
            "expected_exit": 0,
            "expected_stdout": "",
            "entry_path": str(entry),
            "input_paths": [str(entry)],
            "input_sha256": ash_cases.input_hashes([entry]),
            "metadata_output": str(metadata),
            "required_phases": [],
            "measurement_boundary": "fresh rustc process through library metadata emission; no native code generation or run() evaluation",
        },
    }


def generate(output: Path, cli: Path, rustc: Path) -> Path:
    output.mkdir(parents=True, exist_ok=True)
    pairs = []
    for width in FLAT_WIDTHS:
        pairs.append(
            pair(
                output, cli, rustc, "flat", {"width": width},
                ash_cases.flat_program(width), rust_flat_program(width),
                {
                    "monomorphic_identity_functions": width,
                    "identity_calls": width,
                    "entry_result": 42,
                    "generic_type_nesting_depth": 0,
                },
            )
        )
    for family, ash_template, rust_template in (
        ("nested_type", ash_cases.nested_program, rust_nested_program),
        ("prerequisite", ash_cases.prerequisite_program, rust_prerequisite_program),
    ):
        for depth in TYPE_DEPTHS:
            structure: dict[str, Any] = {
                "generic_sum_type_declarations": 1,
                "generic_type_nesting_depth": depth,
                "nested_constructor_count": depth,
                "entry_result": 42,
            }
            if family == "nested_type":
                structure.update(generic_identity_functions=1, typed_probe_functions=1)
            else:
                structure.update(
                    interface_or_trait_declarations=1,
                    base_instances=1,
                    recursive_generic_instances=1,
                    prerequisite_resolution_depth=depth,
                )
            pairs.append(
                pair(
                    output, cli, rustc, family, {"depth": depth},
                    ash_template(depth), rust_template(depth), structure,
                )
            )

    harness = output / "validation.rs"
    modules = []
    assertions = []
    for index, case in enumerate(pairs):
        path_literal = json.dumps(case["rust"]["entry_path"], ensure_ascii=False)
        modules.append(f"#[path = {path_literal}]\nmod case{index};\n")
        label = json.dumps(case["id"])
        assertions.append(f"    assert_eq!(case{index}::run(), 42, {label});\n")
    ash_cases.write_source(
        harness,
        "#![allow(dead_code, unused_imports)]\n\n"
        + "\n".join(modules)
        + "\nfn main() {\n" + "".join(assertions) + "}\n",
    )
    executable = output / "validation"
    harness_inputs = [harness, *(Path(case["rust"]["entry_path"]) for case in pairs)]
    manifest = {
        "schema_version": 1,
        "source_root": str(SOURCE_ROOT),
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "ash_generator_sha256": hashlib.sha256(Path(ash_cases.__file__).read_bytes()).hexdigest(),
        "purpose": "bounded structural Rust frontend reference for the Ash calibration corpus; not a claim of equivalent compiler work",
        "protocol": {
            "execution": "serial fresh processes; no Cargo or incremental compilation",
            "pair_count": len(pairs),
            "warmups_per_language": 1,
            "measured_runs_per_language": 3,
            "ash_observer_runs_per_pair": 1,
            "per_process_timeout_seconds": 10,
            "total_window_seconds": 180,
            "timed_processes_including_warmups": len(pairs) * 2 * 4,
            "ash_observer_processes": len(pairs),
            "rust_native_harness_builds": 1,
            "rust_native_harness_executions": 1,
            "metrics": ["wall_seconds", "user_cpu_seconds", "system_cpu_seconds", "peak_rss_kib"],
            "interpretation": "report absolute results and growth over the startup control; do not subtract RSS peaks or equate language-specific work ledgers",
        },
        "pairs": pairs,
        "harness": {
            "compile_argv": [
                str(rustc), "--edition=2024", "--crate-type=bin",
                "--crate-name=ash_reference_validation", "-Copt-level=0",
                "-Cdebuginfo=0", str(harness), "-o", str(executable),
            ],
            "run_argv": [str(executable)],
            "executable_output": str(executable),
            "cwd": str(SOURCE_ROOT),
            "expected_exit": 0,
            "expected_stdout": "",
            "entry_path": str(harness),
            "input_paths": [str(path) for path in harness_inputs],
            "input_sha256": ash_cases.input_hashes(harness_inputs),
            "asserted_case_ids": [case["id"] for case in pairs],
            "measurement_boundary": "one untimed native build and run validates every generated Rust run() result before interpreting timings",
        },
    }
    manifest_path = output / "reference-manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return manifest_path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    command = subparsers.add_parser("generate")
    command.add_argument("--output", required=True, type=Path)
    command.add_argument("--cli", required=True, type=Path)
    command.add_argument("--rustc", required=True, type=Path)
    args = parser.parse_args()
    manifest = generate(args.output.resolve(), args.cli.resolve(), args.rustc.resolve())
    print(manifest)


if __name__ == "__main__":
    main()
