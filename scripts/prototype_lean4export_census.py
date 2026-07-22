#!/usr/bin/env python3
"""Hash and inventory one official lean4export stream without granting checking credit."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict
from pathlib import Path

from prototype_lean4export_reader import ProbeError, probe_lines


def census_bytes(data: bytes, *, label: str) -> dict[str, object]:
    """Return a deterministic syntax/blocker census for exact NDJSON bytes."""
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ProbeError(f"input is not UTF-8: {error}") from error
    result = probe_lines(text.splitlines(keepends=True))
    return {
        "label": label,
        "sha256": hashlib.sha256(data).hexdigest(),
        "bytes": len(data),
        "records": len(text.splitlines()),
        **asdict(result),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", nargs="?", default="-", help="NDJSON path or - for stdin")
    parser.add_argument("--label", required=True)
    args = parser.parse_args()
    try:
        if args.path == "-":
            data = sys.stdin.buffer.read()
        else:
            data = Path(args.path).read_bytes()
        result = census_bytes(data, label=args.label)
    except (OSError, ProbeError) as error:
        parser.exit(2, f"LEAN4EXPORT_CENSUS_ERROR|{error}\n")
    print("LEAN4EXPORT_CENSUS|" + json.dumps(result, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
