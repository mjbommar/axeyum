#!/usr/bin/env python3
"""Gate: the committed Mathlib module-baseline receipt is reproducible and
undrifted (L1 phase G0, docs/plan/graph-directed-library-roadmap-2026-08-30.md).

What this checks, in order, each with its own named failure reason:

1.  SOURCE_UNREACHABLE / EMPTY_SOURCE -- the source directory must exist, be a
    mathlib4 checkout, and parse to at least one module. A run that finds
    nothing must fail loudly, never report a clean baseline.
2.  RECEIPT_MISSING -- the committed receipt must exist on disk.
3.  NONDETERMINISM -- two independent fresh parses of the SAME source must
    produce byte-identical receipt JSON. This is "two runs reproduce the
    receipt" re-checked on every gate invocation, not just asserted once by a
    human.
4.  SOURCE_DRIFT -- the committed receipt's source identity (commit and/or
    content tree hash) must match a fresh parse. Reported independently of
    parser drift, naming the specific commit/hash values that disagree.
5.  PARSER_DRIFT -- the committed receipt's parser identity (sha256 of
    scripts/lib/module_baseline.py) must match the parser actually installed.
    Reported independently of source drift.
6.  CONTENT_MISMATCH -- if source and parser identities both match but the
    receipt bodies differ anyway, that is a determinism bug this checker
    cannot otherwise name; reported explicitly rather than passing silently.

Usage:
    python3 scripts/check-module-baseline.py
    python3 scripts/check-module-baseline.py --mathlib-dir DIR --receipt PATH
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import module_baseline as mb  # noqa: E402

DEFAULT_MATHLIB_DIR = "/data0/axeyum/lean-import-toolchain/mathlib4"
DEFAULT_RECEIPT = "artifacts/module-baseline/receipt.json"


def fail(reason: str, detail: str) -> int:
    print(f"MODULE_BASELINE_CHECK|verdict=FAIL|reason={reason}|detail={detail}", file=sys.stderr)
    return 1


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-dir", default=DEFAULT_MATHLIB_DIR)
    parser.add_argument("--receipt", default=DEFAULT_RECEIPT)
    parser.add_argument(
        "--commit",
        default=None,
        help="override the recorded source commit (test fixtures only)",
    )
    args = parser.parse_args(argv)

    mathlib_dir = Path(args.mathlib_dir)
    receipt_path = Path(args.receipt)

    # --- absence / unreachable-source checks, before anything else ---------
    try:
        fresh_1 = mb.build_receipt(mathlib_dir, commit_override=args.commit)
    except mb.SourceUnreachable as e:
        return fail("SOURCE_UNREACHABLE", str(e))
    except mb.EmptySource as e:
        return fail("EMPTY_SOURCE", str(e))

    if not receipt_path.is_file():
        return fail("RECEIPT_MISSING", f"no receipt at {receipt_path}")

    committed_text = receipt_path.read_text(encoding="utf-8")
    try:
        committed = mb.json.loads(committed_text)
    except mb.json.JSONDecodeError as e:
        return fail("RECEIPT_UNPARSEABLE", str(e))

    # --- reproducibility: a SECOND independent fresh parse ------------------
    fresh_2 = mb.build_receipt(mathlib_dir, commit_override=args.commit)
    text_1 = mb.receipt_to_json(fresh_1)
    text_2 = mb.receipt_to_json(fresh_2)
    if text_1 != text_2:
        return fail(
            "NONDETERMINISM",
            "two fresh parses of the same source produced different receipts "
            "-- look for unsorted iteration in scripts/lib/module_baseline.py",
        )

    # --- drift diagnosis, source and parser reported independently ---------
    reasons = []

    committed_source = committed.get("source", {})
    fresh_source = fresh_1["source"]
    source_mismatch = (
        committed_source.get("commit") != fresh_source.get("commit")
        or committed_source.get("tree_hash_sha256") != fresh_source.get("tree_hash_sha256")
    )
    if source_mismatch:
        reasons.append(
            "SOURCE_DRIFT: committed commit={c1} tree_hash={h1} vs fresh "
            "commit={c2} tree_hash={h2}".format(
                c1=committed_source.get("commit"),
                h1=committed_source.get("tree_hash_sha256"),
                c2=fresh_source.get("commit"),
                h2=fresh_source.get("tree_hash_sha256"),
            )
        )

    committed_parser = committed.get("parser", {})
    fresh_parser = fresh_1["parser"]
    parser_mismatch = committed_parser.get("sha256") != fresh_parser.get("sha256")
    if parser_mismatch:
        reasons.append(
            "PARSER_DRIFT: committed sha256={p1} vs fresh sha256={p2}".format(
                p1=committed_parser.get("sha256"), p2=fresh_parser.get("sha256")
            )
        )

    if reasons:
        for r in reasons:
            print(f"MODULE_BASELINE_CHECK|verdict=FAIL|{r}", file=sys.stderr)
        return 1

    # --- identities agree; the whole body must agree too --------------------
    if committed_text.strip() != text_1.strip():
        return fail(
            "CONTENT_MISMATCH",
            "source and parser identities match but receipt bodies differ "
            "-- determinism bug not explained by source or parser drift",
        )

    print(
        "MODULE_BASELINE_CHECK|verdict=PASS"
        f"|modules={fresh_1['totals']['modules']}"
        f"|internal_edges={fresh_1['totals']['internal_edges']}"
        f"|sinks={fresh_1['totals']['no_importer_sink_count']}"
        f"|commit={fresh_source.get('commit')}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
