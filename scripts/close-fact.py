#!/usr/bin/env python3
"""Close an open fact — by RUNNING its evidence, not by being told about it.

The last manual link in the loop. `fact-frontier.py` selects a target and the
solver produces a verdict, but writing the evidence rows and flipping
`epistemic_status` has been hand-work — which is exactly where a status gets
asserted without the evidence that backs it. That has already happened in this
ledger: three seed facts were written `proved`, citing
`cargo test -p axeyum-lean-kernel --lib nat_prelude` as their checker, against
statements naming `rado.add_comm` — a shell declared in an integration test that
the `--lib` filter never compiles. The status was right and the evidence row
pointed at a gate structurally incapable of checking it.

So the rule here is that this tool does not accept a claim, it re-derives one:

  **Every evidence row carrying a `checker_command` has that command EXECUTED.
  A non-zero exit refuses the flip.**

That is the whole point. A closer that trusts its caller is a rename utility
with extra steps, and the failure it would permit is the only failure that
matters — a `proved` fact whose evidence does not hold.

Usage:
    python3 scripts/close-fact.py --fact F:rado-r4-a5-b3 \
        --status computed --route search-certificate \
        --footprint '["encoder-faithfulness", "drat-checker"]' \
        --evidence-json path/to/rows.json [--dry-run]

`--evidence-json` is a list of evidence rows in the schema's shape. Rows with a
`checker_command` are run; rows without one (a `bound-citation`, say) are
accepted as-is and REPORTED as unverified rather than silently counted.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FACTS = ROOT / "artifacts" / "facts"

SETTLED = {"proved", "computed", "refuted", "axiom"}
# Only this route can deliver axiom-freedom; mirrors validate-facts.py.
AXIOM_FREE_CAPABLE = {"kernel-lean"}


def path_for(fact_id: str) -> Path:
    return FACTS / (fact_id.replace("F:", "F-") + ".json")


def run_checker(cmd: str, timeout: int) -> tuple[bool, str]:
    """Execute a checker command. Its exit status is the verdict."""
    try:
        p = subprocess.run(cmd, shell=True, cwd=ROOT, capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return False, f"TIMED OUT after {timeout}s"
    tail = (p.stdout or p.stderr or "").strip().splitlines()
    return p.returncode == 0, (tail[-1] if tail else f"exit {p.returncode}, no output")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--fact", required=True)
    ap.add_argument("--status", required=True, choices=sorted(SETTLED))
    ap.add_argument("--route", required=True)
    ap.add_argument("--footprint", help="JSON list; required when --status is proved")
    ap.add_argument("--evidence-json", required=True)
    ap.add_argument("--external-status")
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--force", action="store_true",
                    help="allow re-closing an already-settled fact")
    args = ap.parse_args()

    path = path_for(args.fact)
    if not path.is_file():
        print(f"close-fact: no such fact: {path}", file=sys.stderr)
        return 2
    original = path.read_text()
    fact = json.loads(original)

    if fact["epistemic_status"] in SETTLED and not args.force:
        print(f"close-fact: {args.fact} is already {fact['epistemic_status']!r}. "
              f"Re-closing a settled fact silently rewrites established evidence; "
              f"pass --force if that is genuinely intended.", file=sys.stderr)
        return 2

    rows = json.loads(Path(args.evidence_json).read_text())
    if not isinstance(rows, list) or not rows:
        print("close-fact: --evidence-json must be a non-empty list", file=sys.stderr)
        return 2

    # Refuse an axiom-freedom claim the route cannot support, before running
    # anything. Mirrors validate-facts.py so a flip cannot be attempted on
    # something the ledger would then reject.
    if args.footprint and json.loads(args.footprint) == [] \
            and args.route not in AXIOM_FREE_CAPABLE:
        print(f"close-fact: axiom_footprint [] on route {args.route!r} asserts "
              f"axiom-freedom that route cannot deliver.", file=sys.stderr)
        return 2

    # --- the part that makes this a closer and not a renamer ---
    ran = failed = unverified = 0
    for row in rows:
        cmd = row.get("checker_command")
        if not cmd:
            unverified += 1
            print(f"  UNVERIFIED  {row.get('id')}: no checker_command "
                  f"(kind={row.get('kind')!r}) — accepted as-is, not counted as checked")
            continue
        ok, tail = run_checker(cmd, args.timeout)
        ran += 1
        print(f"  {'OK  ' if ok else 'FAIL'}        {row.get('id')}: {tail[:120]}")
        if not ok:
            failed += 1

    if failed:
        print(f"\nclose-fact: REFUSED. {failed} of {ran} checker command(s) did not "
              f"succeed, so the evidence for {args.fact} does not hold as written. "
              f"A status is only worth what its checker returns.", file=sys.stderr)
        return 1
    if ran == 0:
        print(f"\nclose-fact: REFUSED. No evidence row carried a checker_command, so "
              f"nothing was re-derived. Closing on that would record a claim, not "
              f"evidence.", file=sys.stderr)
        return 1

    fact["epistemic_status"] = args.status
    fact["proof_route"] = args.route
    if args.footprint is not None:
        fact["axiom_footprint"] = json.loads(args.footprint)
    if args.external_status:
        fact["external_status"] = args.external_status
    fact["evidence"] = rows

    new = json.dumps(fact, indent=2) + "\n"
    if args.dry_run:
        print(f"\nclose-fact: DRY RUN — {ran} checker(s) passed, {unverified} unverified. "
              f"Would set {args.fact} to {args.status!r} on route {args.route!r}.")
        return 0

    path.write_text(new)
    v = subprocess.run([sys.executable, "scripts/validate-facts.py"], cwd=ROOT,
                       capture_output=True, text=True)
    if v.returncode != 0:
        path.write_text(original)  # restore; never leave the ledger invalid
        print(f"\nclose-fact: REVERTED — the written fact fails validation:\n"
              f"{v.stdout}{v.stderr}", file=sys.stderr)
        return 1
    print(f"\nclose-fact: {args.fact} -> {args.status} on {args.route} "
          f"({ran} checker(s) re-derived, {unverified} unverified)")
    print(v.stdout.strip())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
