#!/usr/bin/env python3
"""Re-bucket ADR-2121's 24 in-bounds QF_NRA files under ADR-2126's split causes.

Why this exists. ADR-2121 reported `projection` at 2 of 24 and said in its own
text that the number was an UPPER BOUND, because the bucket held four failures
with four different fixes: the Sylvester dimension cap (which a fraction-free
determinant would remove), an identically-zero resultant, a derivative overflow
and a coefficient overflow. A bundle whose members have different fixes is an
upper bound on each of them and a measurement of none. This reads the same 24
files back under the split taxonomy so the per-lever ceiling can be quoted.

Two controls, both of which exit non-zero rather than printing a caveat:

* the row count must be exactly 24 and the file set must equal the file set
  ADR-2121 measured -- otherwise the ceiling is about a different population and
  is not comparable to the number it is meant to correct;
* every row must carry a cause this script recognises. An unparsed row silently
  dropped into an "other" bucket is how a taxonomy measures the subset it
  happens to understand instead of the set.
"""

from __future__ import annotations

import argparse
import collections
import re
import sys
from pathlib import Path

DECLINE_RE = re.compile(r"declined:\s*([a-z0-9-]+)\s*\(cad-arm=")

# What each cause says about what would fix it. The point of the split.
FIX = {
    "non-conjunctive": "the clause loop (CDCAC over a Boolean combination)",
    "algebraic-witness": "an algebraic sample (`Value::RealAlgebraic`)",
    "projection-sylvester-dim": "a fraction-free (Bareiss) multivariate determinant",
    "projection-resultant-zero": "a squarefree / primitive-part split",
    "projection-derivative": "wider coefficient arithmetic",
    "projection-arithmetic": "wider coefficient arithmetic",
    "projection": "(enumerative decider's projection -- not this route)",
    "root-ordering": "exact ordering of two critical values",
    "certificate-rejected": "the checker accepting what the producer built",
    "coefficient-range": "coefficients past `1 << 40` (ADR-2110 claim 2)",
    "slice-bounds": "a wider declared slice",
    "nullified-residual": "Lazard evaluation, or z3's derivative walk",
    "algebraic-coarsening": "a bracket that could not be narrowed",
    "indeterminate-sign": "an exact sign at a complete sample",
    "cell-budget": "a larger cell cap",
    "deadline": "more time",
    "root-isolation": "exact root isolation that completes",
    "critical-count-cap": "a larger critical-value cap",
    "unsat-withheld-by-arm": "nothing -- the ARM withheld it",
    "DECIDED": "nothing -- the route already decides this file",
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--tsv", required=True, help="the cause-scan output")
    ap.add_argument(
        "--expect-files",
        required=True,
        help="the file list the scan consumed; the row set must equal it",
    )
    ap.add_argument("--expect-rows", type=int, default=24)
    args = ap.parse_args()

    rows = [
        line.rstrip("\n").split("\t")
        for line in Path(args.tsv).read_text().splitlines()[1:]
        if line.strip()
    ]
    expected = {
        line.strip()
        for line in Path(args.expect_files).read_text().splitlines()
        if line.strip()
    }

    rc = 0
    if len(rows) != args.expect_rows:
        print(f"CONTROL FAILED: {len(rows)} rows, expected {args.expect_rows}")
        rc = 1
    seen = {r[0] for r in rows}
    if seen != expected:
        print(f"CONTROL FAILED: row set != list ({len(seen ^ expected)} differ)")
        rc = 1

    causes: collections.Counter[str] = collections.Counter()
    unparsed: list[str] = []
    for path, verdict, detail in ((r[0], r[1], r[2]) for r in rows):
        m = DECLINE_RE.search(detail)
        if m:
            causes[m.group(1)] += 1
        elif verdict in ("sat", "unsat"):
            causes["DECIDED"] += 1
        else:
            unparsed.append(f"{path}\t{verdict}\t{detail}")

    if unparsed:
        print(f"CONTROL FAILED: {len(unparsed)} rows carry no recognised cause")
        for u in unparsed:
            print(f"  {u}")
        rc = 1

    unknown = sorted(c for c in causes if c not in FIX)
    if unknown:
        print(f"CONTROL FAILED: cause(s) with no recorded fix: {unknown}")
        rc = 1

    total = sum(causes.values())
    print(f"\n== {args.tsv}: {total} files, {len(causes)} distinct causes ==\n")
    print(f"{'files':>5}  {'cause':<28}  what would fix it")
    print(f"{'-' * 5}  {'-' * 28}  {'-' * 50}")
    for cause, n in sorted(causes.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"{n:>5}  {cause:<28}  {FIX.get(cause, '?')}")
    print(f"{'-' * 5}")
    print(f"{total:>5}  TOTAL")

    if total != args.expect_rows:
        print(f"\nCONTROL FAILED: buckets sum to {total}, not {args.expect_rows}")
        rc = 1
    print("\nCONTROLS PASSED" if rc == 0 else "\nCONTROLS FAILED")
    return rc


if __name__ == "__main__":
    sys.exit(main())
