#!/usr/bin/env python3
"""The D3 screen a target actually runs through BEFORE a producer is
dispatched at it (roadmap phase D3, ADR-0890).

`scripts/check-falsification-screen.py` is the GATE: it re-executes the whole
pack and refuses a stale or vacuous state. This script is the SCREEN itself --
what a lane runs, once, for one proposed target, before writing a single line
of proof-producer code against it. It writes a RECEIPT
(`artifacts/falsification/receipts/<target-id>.json`) recording the verdict
and the git commit the screen ran at, and `--dispatch-demo` appends a record
to `artifacts/falsification/dispatch-log.jsonl` that the checker's ordering
guards verify happened AFTER a clear receipt -- checkable with
`git merge-base --is-ancestor <receipt-commit> <dispatch-commit>`, not merely
asserted in prose.

A target is one of:

- a `FALSE_STATEMENTS` id -- the screen's job is to REJECT it (find a
  counterexample). Verdict is `reject-before-dispatch` on success (a
  counterexample was found -- correctly refusing to let this proposal reach a
  producer) or `reject-before-dispatch` is what SHOULD happen; if the control
  finds nothing, the receipt records `NOT-REFUTED` as an explicit failure
  state rather than silently passing.
- a `DEFINITIONS` id -- verdict is `clear-for-dispatch` when the candidate
  matches its independent reference on the whole bounded domain and every
  attached mutation moves an observation; `reject-before-dispatch` otherwise.
- a `REVIEW_OBLIGATIONS` id -- verdict is always `review-required`; dispatch
  against it is refused by the checker's ordering guard regardless of any
  receipt, because a review-required verdict is never `clear-for-dispatch`.

Usage:

    python3 scripts/gen-falsification-screen.py --target Nat.lor
    python3 scripts/gen-falsification-screen.py --all
    python3 scripts/gen-falsification-screen.py --dispatch-demo Nat.lor --note "..."
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import subprocess
import sys
from datetime import datetime, timezone

ROOT = pathlib.Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"
FALS_DIR = ROOT / "artifacts" / "falsification"
RECEIPTS_DIR = FALS_DIR / "receipts"
DISPATCH_LOG = FALS_DIR / "dispatch-log.jsonl"

_spec = importlib.util.spec_from_file_location(
    "check_falsification_screen", SCRIPTS / "check-falsification-screen.py"
)
checker = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(checker)

sys.path.insert(0, str(SCRIPTS))
from falsification_screen_fixtures import DEFINITIONS, FALSE_STATEMENTS, REVIEW_OBLIGATIONS  # noqa: E402


def head_commit() -> str:
    out = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, check=True
    )
    return out.stdout.strip()


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def screen_target(target_id: str) -> dict:
    for fx in FALSE_STATEMENTS:
        if fx.id == target_id:
            r = checker.run_false_statement(fx)
            verdict = "reject-before-dispatch" if r["counterexamples"] > 0 else "NOT-REFUTED"
            return {
                "target_id": target_id,
                "kind": "false_statement",
                "verdict": verdict,
                "detail": r,
                "git_commit": head_commit(),
                "screened_at": now_iso(),
            }
    for d in DEFINITIONS:
        if d.id == target_id:
            r = checker.run_definition(d)
            clear = r["mismatches"] == 0 and r["mutations_vacuous"] == 0 and bool(r["mutations"])
            verdict = "clear-for-dispatch" if clear else "reject-before-dispatch"
            return {
                "target_id": target_id,
                "kind": "definition",
                "verdict": verdict,
                "detail": r,
                "git_commit": head_commit(),
                "screened_at": now_iso(),
            }
    for r in REVIEW_OBLIGATIONS:
        if r.id == target_id:
            rr = checker.run_review_obligation(r)
            return {
                "target_id": target_id,
                "kind": "review_obligation",
                "verdict": "review-required",
                "detail": rr,
                "git_commit": head_commit(),
                "screened_at": now_iso(),
            }
    raise SystemExit(f"unknown target {target_id!r}: not in FALSE_STATEMENTS, DEFINITIONS or REVIEW_OBLIGATIONS")


def write_receipt(receipt: dict) -> pathlib.Path:
    RECEIPTS_DIR.mkdir(parents=True, exist_ok=True)
    path = RECEIPTS_DIR / f"{receipt['target_id']}.json"
    path.write_text(json.dumps(receipt, indent=2) + "\n")
    return path


def all_target_ids() -> list[str]:
    return [fx.id for fx in FALSE_STATEMENTS] + [d.id for d in DEFINITIONS] + [r.id for r in REVIEW_OBLIGATIONS]


def dispatch_demo(target_id: str, note: str) -> int:
    """Append a demo dispatch-log entry for `target_id`. REFUSES unless a
    receipt already on disk for this target has verdict clear-for-dispatch --
    dispatch cannot happen without a prior clear screen, enforced here AND
    re-checked (against real git ancestry) by the gate."""
    receipt_path = RECEIPTS_DIR / f"{target_id}.json"
    if not receipt_path.exists():
        print(f"REFUSED: no screen receipt for {target_id!r} -- run --target {target_id} first")
        return 1
    receipt = json.loads(receipt_path.read_text())
    if receipt.get("verdict") != "clear-for-dispatch":
        print(
            f"REFUSED: receipt for {target_id!r} has verdict {receipt.get('verdict')!r}, "
            "not clear-for-dispatch -- cannot dispatch a producer against it"
        )
        return 1
    entry = {
        "target_id": target_id,
        "commit": head_commit(),
        "timestamp": now_iso(),
        "note": note,
        "receipt_commit_at_dispatch_time": receipt["git_commit"],
    }
    FALS_DIR.mkdir(parents=True, exist_ok=True)
    with DISPATCH_LOG.open("a") as f:
        f.write(json.dumps(entry) + "\n")
    print(f"dispatch recorded for {target_id!r} at commit {entry['commit'][:12]}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--target", help="screen exactly one target id")
    g.add_argument("--all", action="store_true", help="screen every registered target")
    g.add_argument("--dispatch-demo", metavar="TARGET_ID", help="append a demo dispatch-log entry")
    ap.add_argument("--note", default="", help="note recorded with --dispatch-demo")
    args = ap.parse_args()

    if args.dispatch_demo:
        return dispatch_demo(args.dispatch_demo, args.note)

    targets = all_target_ids() if args.all else [args.target]
    exit_code = 0
    for t in targets:
        receipt = screen_target(t)
        path = write_receipt(receipt)
        print(f"{receipt['verdict']:24s} {t:32s} -> {path.relative_to(ROOT)}")
        if receipt["verdict"] == "NOT-REFUTED":
            exit_code = 1
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
