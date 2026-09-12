#!/usr/bin/env python3
"""Generate bytecode fixtures using an independently installed pinned Vyper."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from importlib.metadata import version
from pathlib import Path

import vyper
from vyper.compiler.settings import OptimizationLevel, Settings
from vyper.venom import OPTIMIZATION_PASSES


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--expected-python", required=True)
    parser.add_argument("--generator-uv", required=True)
    parser.add_argument("--expected-install-root", type=Path, required=True)
    parser.add_argument("--sources", type=Path, required=True)
    parser.add_argument("--hol-programs", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def canonical_hex(value: str, field: str, source: Path) -> str:
    value = value.removeprefix("0x").lower()
    if len(value) % 2 or any(c not in "0123456789abcdef" for c in value):
        raise ValueError(f"invalid {field} output for {source}")
    return value


def main() -> None:
    args = parse_args()
    if platform.python_version() != args.expected_python:
        raise RuntimeError(
            f"running Python {platform.python_version()}, expected {args.expected_python}"
        )

    actual_commit = vyper.__commit__.strip()
    if len(actual_commit) < 8 or not args.expected_commit.startswith(actual_commit):
        raise RuntimeError(
            f"imported Vyper commit {actual_commit!r}, expected {args.expected_commit!r}"
        )
    install_root = args.expected_install_root.resolve()
    imported_from = Path(vyper.__file__).resolve()
    if install_root not in imported_from.parents:
        raise RuntimeError(
            f"imported Vyper from {imported_from}, outside isolated environment {install_root}"
        )

    expected_stems = {
        "add_arg", "deploy_storage", "empty", "event_log", "for_accum",
        "for_break", "for_continue", "for_pass", "hashmap_read",
        "hashmap_write", "if_bool", "if_join", "indexed_event_log",
        "internal_call", "internal_call_arg", "local_uint", "mixed_event_log",
        "noop", "return_arg", "return_uint", "storage_read", "storage_write",
        "two_external",
    }
    sources = sorted(args.sources.glob("*.vy"))
    actual_stems = {source.stem for source in sources}
    if actual_stems != expected_stems:
        missing = sorted(expected_stems - actual_stems)
        unexpected = sorted(actual_stems - expected_stems)
        raise RuntimeError(
            f"wrong Vyper source set; missing={missing}, unexpected={unexpected}"
        )

    if (
        OPTIMIZATION_PASSES[OptimizationLevel.NONE]
        != OPTIMIZATION_PASSES[OptimizationLevel.O1]
    ):
        raise RuntimeError("pinned Vyper NONE and O1 Venom pipelines differ")

    args.output.mkdir(parents=True, exist_ok=True)
    settings = Settings(
        # At the pinned revision NONE and O1 run the same PASSES_O1 Venom
        # pipeline; NONE alone disables the final assembly optimizer. This
        # matches HOL's o1_policy combined with identity finalizer K SOME.
        optimize=OptimizationLevel.NONE,
        evm_version="prague",
        experimental_codegen=True,
    )
    fixtures = {}
    for source in sources:
        source_bytes = source.read_bytes()
        result = vyper.compile_code(
            source.read_text(),
            contract_path=source,
            output_formats=("bytecode", "bytecode_runtime"),
            settings=settings,
            no_bytecode_metadata=True,
        )
        deploy = canonical_hex(result["bytecode"], "deploy", source)
        runtime = canonical_hex(result["bytecode_runtime"], "runtime", source)
        (args.output / f"{source.stem}.hex").write_text(
            f"deploy={deploy}\nruntime={runtime}\n"
        )
        fixtures[source.stem] = {
            "source": f"python-o1-no-asm-opt-sources/{source.name}",
            "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
            "deploy_sha256": hashlib.sha256(bytes.fromhex(deploy)).hexdigest(),
            "runtime_sha256": hashlib.sha256(bytes.fromhex(runtime)).hexdigest(),
        }

    dependencies = {
        package: version(package)
        for package in (
            "cbor2", "immutables", "lark", "packaging", "pycryptodome", "wheel"
        )
    }
    provenance = {
        "schema_version": 1,
        "producer": "pinned Python Vyper",
        "vyper_commit": args.expected_commit,
        "vyper_version": vyper.__version__,
        "python_version": platform.python_version(),
        "uv_version": args.generator_uv,
        "dependencies": dependencies,
        "hol_source_correspondence": {
            "file": "lowering/defs/evalCompilerScript.sml",
            "sha256": hashlib.sha256(args.hol_programs.read_bytes()).hexdigest(),
            "note": "Audit anchor only; HOL is not an input to Python compilation.",
        },
        "settings": {
            "experimental_codegen": True,
            "optimization_level": "NONE",
            "venom_ir_pipeline": "O1",
            "final_assembly_optimization": False,
            "evm_version": "prague",
            "bytecode_metadata": False,
            "outputs": ["bytecode", "bytecode_runtime"],
        },
        "fixtures": fixtures,
    }
    (args.output / "provenance.json").write_text(
        json.dumps(provenance, indent=2, sort_keys=True) + "\n"
    )


if __name__ == "__main__":
    main()
