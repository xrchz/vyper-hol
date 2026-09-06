#!/usr/bin/env python3
"""Write or verify deterministic provenance for functional Vyper exports."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
EXPORT_ROOT = HERE / "vyper-test-exports"
PROVENANCE = HERE / "vyper-test-export-provenance.json"


def aggregate_exports() -> tuple[int, str]:
    if not EXPORT_ROOT.is_dir():
        raise RuntimeError(f"export directory not found: {EXPORT_ROOT}")
    paths = sorted(
        (path.relative_to(EXPORT_ROOT) for path in EXPORT_ROOT.rglob("*.json")),
        key=lambda path: path.as_posix().encode("utf-8"),
    )
    digest = hashlib.sha256()
    for relative in paths:
        path_bytes = relative.as_posix().encode("utf-8")
        contents = (EXPORT_ROOT / relative).read_bytes()
        digest.update(len(path_bytes).to_bytes(8, "big"))
        digest.update(path_bytes)
        digest.update(len(contents).to_bytes(8, "big"))
        digest.update(contents)
    return len(paths), digest.hexdigest()


def expected_provenance(selected_count: int) -> dict[str, object]:
    json_count, aggregate_hash = aggregate_exports()
    if selected_count < 0 or selected_count > json_count:
        raise RuntimeError(
            f"invalid selected JSON count {selected_count} for {json_count} exports"
        )
    return {
        "schema_version": 1,
        "pin_file": "../VYPER_PIN",
        "settings_file": "vyper-test-export-settings.json",
        "aggregate": {
            "algorithm": "sha256",
            "framing": "sorted UTF-8 POSIX relative path; each path and file is prefixed by its unsigned 8-byte big-endian length",
            "json_count": json_count,
            "sha256": aggregate_hash,
        },
        "inventory": {
            "selected_json_count": selected_count,
            "excluded_json_count": json_count - selected_count,
            "definition_wrapper_count": selected_count,
            "test_wrapper_count": selected_count,
        },
        "explicit_exclusions": [
            {
                "path": "functional/codegen/features/test_custom_errors.json",
                "status": "excluded",
                "reason": "top-level ErrorDef is unsupported by frontend/jsonASTLib.sml",
            }
        ],
    }


def serialized(value: dict[str, object]) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("selected_count", type=int)
    args = parser.parse_args()

    expected = serialized(expected_provenance(args.selected_count))
    if re.search(r'\b[0-9a-fA-F]{40}\b', expected):
        raise RuntimeError("provenance must not duplicate the VYPER_PIN revision")

    if args.check:
        try:
            actual = PROVENANCE.read_text(encoding="utf-8")
        except FileNotFoundError:
            print(f"missing provenance: {PROVENANCE}", file=sys.stderr)
            return 1
        if actual != expected:
            print(
                "vyper-test-export-provenance.json is stale; run "
                "sh tests/vyper-test-wrappers",
                file=sys.stderr,
            )
            return 1
    else:
        temporary = PROVENANCE.with_suffix(PROVENANCE.suffix + ".tmp")
        temporary.write_text(expected, encoding="utf-8")
        temporary.replace(PROVENANCE)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"vyper-test-provenance: {error}", file=sys.stderr)
        raise SystemExit(1)
