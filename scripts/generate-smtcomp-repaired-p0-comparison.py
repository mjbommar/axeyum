#!/usr/bin/env python3
"""Generate or check the frozen repaired-P0 combined comparison."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts" / "smtcomp_repro"))

from p0_compare import (  # noqa: E402
    comparison_json_bytes,
    derive_live_comparison,
    render_markdown,
    sha256_bytes,
    validate_comparison,
)


DEFAULT_JSON = ROOT / "docs" / "plan" / "generated" / "smtcomp-repaired-p0-comparison.json"
DEFAULT_MARKDOWN = ROOT / "docs" / "plan" / "generated" / "smtcomp-repaired-p0-comparison.md"


def _load_committed(path: Path) -> dict:
    try:
        result = json.loads(path.read_bytes())
    except (OSError, json.JSONDecodeError) as exc:
        raise SystemExit(f"unable to load generated comparison: {path}: {exc}") from exc
    validate_comparison(result)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--preparation-root", type=Path)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--markdown-output", type=Path, default=DEFAULT_MARKDOWN)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    if args.preparation_root is None:
        if not args.check:
            parser.error("--preparation-root is required when generating")
        result = _load_committed(args.json_output)
    else:
        result = derive_live_comparison(args.preparation_root.resolve(strict=True))

    json_bytes = comparison_json_bytes(result)
    markdown_bytes = render_markdown(result, sha256_bytes(json_bytes))
    if args.check:
        if args.json_output.read_bytes() != json_bytes:
            raise SystemExit("generated repaired-P0 comparison JSON is stale")
        if args.markdown_output.read_bytes() != markdown_bytes:
            raise SystemExit("generated repaired-P0 comparison Markdown is stale")
        return 0

    for path in (args.json_output, args.markdown_output):
        try:
            path.resolve().relative_to(args.preparation_root.resolve())
        except ValueError:
            pass
        else:
            raise SystemExit("refusing to write comparison output under preparation root")
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.markdown_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_bytes(json_bytes)
    args.markdown_output.write_bytes(markdown_bytes)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
