#!/usr/bin/env python3
"""Merge and sanitize Vyper compiler JSON for contract-checker fixtures."""

import argparse
import json
from pathlib import Path
from typing import Any

DEFAULT_FORBIDDEN = ("/home/", "/tmp/")


def parse_replacement(value: str) -> tuple[str, str]:
    if "=" not in value:
        raise argparse.ArgumentTypeError("replacement must have the form OLD=NEW")
    old, new = value.split("=", 1)
    if not old:
        raise argparse.ArgumentTypeError("replacement OLD value must not be empty")
    return old, new


def rewrite(value: Any, replacements: list[tuple[str, str]]) -> Any:
    if isinstance(value, dict):
        return {key: rewrite(item, replacements) for key, item in value.items()}
    if isinstance(value, list):
        return [rewrite(item, replacements) for item in value]
    if isinstance(value, str):
        for old, new in replacements:
            value = value.replace(old, new)
    return value


def string_values(value: Any):
    if isinstance(value, dict):
        for item in value.values():
            yield from string_values(item)
    elif isinstance(value, list):
        for item in value:
            yield from string_values(item)
    elif isinstance(value, str):
        yield value


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON or two-object JSONL input")
    parser.add_argument("output", type=Path, help="canonical merged JSON output")
    parser.add_argument(
        "--replace", action="append", default=[], type=parse_replacement,
        metavar="OLD=NEW", help="recursive string replacement (repeatable)")
    parser.add_argument(
        "--forbid", action="append", default=[], metavar="TEXT",
        help="additional text forbidden in every output string")
    args = parser.parse_args()

    objects = [json.loads(line) for line in args.input.read_text().splitlines()
               if line.strip()]
    if not 1 <= len(objects) <= 2 or not all(isinstance(obj, dict) for obj in objects):
        parser.error("input must contain one or two JSON objects")

    merged: dict[str, Any] = {}
    for obj in objects:
        duplicate = merged.keys() & obj.keys()
        if duplicate:
            parser.error("duplicate top-level keys: " + ", ".join(sorted(duplicate)))
        merged.update(obj)

    sanitized = rewrite(merged, args.replace)
    forbidden = DEFAULT_FORBIDDEN + tuple(args.forbid)
    leaks = sorted({text for text in string_values(sanitized)
                    for marker in forbidden if marker in text})
    if leaks:
        parser.error("forbidden text remains in output: " + repr(leaks[:5]))

    args.output.write_text(
        json.dumps(sanitized, separators=(",", ":"), sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
