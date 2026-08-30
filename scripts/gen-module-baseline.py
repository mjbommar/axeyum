#!/usr/bin/env python3
"""Generate the Mathlib module-import baseline receipt (L1 phase G0).

Vendors nothing: reads whatever Mathlib checkout `--mathlib-dir` points at
(default: the pinned toolchain checkout from
`scripts/provision-lean-import-toolchain.sh`) and writes a compact JSON
receipt -- source identity, parser identity, module/edge totals, top-degree
rows, sink count -- to `artifacts/module-baseline/receipt.json` by default.

    python3 scripts/gen-module-baseline.py
    python3 scripts/gen-module-baseline.py --mathlib-dir /path/to/mathlib4 --out /tmp/receipt.json

Exits nonzero (naming the reason) if the source directory does not exist, is
not a mathlib4 checkout, or parses to zero modules -- a run that finds nothing
must never emit a receipt that looks like a clean baseline.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import module_baseline as mb  # noqa: E402

DEFAULT_MATHLIB_DIR = "/data0/axeyum/lean-import-toolchain/mathlib4"
DEFAULT_OUT = "artifacts/module-baseline/receipt.json"


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mathlib-dir",
        default=DEFAULT_MATHLIB_DIR,
        help=f"mathlib4 checkout root (default: {DEFAULT_MATHLIB_DIR})",
    )
    parser.add_argument(
        "--out",
        default=DEFAULT_OUT,
        help=f"output receipt path (default: {DEFAULT_OUT})",
    )
    parser.add_argument(
        "--commit",
        default=None,
        help="override the recorded source commit (for non-git fixtures; "
        "real runs should omit this and let git identify the checkout)",
    )
    parser.add_argument(
        "--print-only",
        action="store_true",
        help="print the receipt to stdout instead of writing --out",
    )
    args = parser.parse_args(argv)

    mathlib_dir = Path(args.mathlib_dir)
    try:
        receipt = mb.build_receipt(mathlib_dir, commit_override=args.commit)
    except mb.SourceUnreachable as e:
        print(f"MODULE_BASELINE|verdict=FAIL|reason=SOURCE_UNREACHABLE|detail={e}", file=sys.stderr)
        return 1
    except mb.EmptySource as e:
        print(f"MODULE_BASELINE|verdict=FAIL|reason=EMPTY_SOURCE|detail={e}", file=sys.stderr)
        return 1

    text = mb.receipt_to_json(receipt)

    if args.print_only:
        sys.stdout.write(text)
        return 0

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text, encoding="utf-8")
    print(
        f"MODULE_BASELINE|verdict=PASS|modules={receipt['totals']['modules']}"
        f"|internal_edges={receipt['totals']['internal_edges']}"
        f"|sinks={receipt['totals']['no_importer_sink_count']}"
        f"|out={out_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
