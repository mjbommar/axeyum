#!/usr/bin/env python3
"""Read an interleaved A/B (ADR-2110, lane NRA-TRACE) and report it honestly.

Six numbers, and each is separately checkable:

  rows / A / B / net    -- how many files, and how many each arm DECIDED.
  gains / losses        -- files one arm decides and the other does not, BY NAME.
  flips                 -- `sat` on one side and `unsat` on the other. A flip is
                           a soundness event and is printed before anything else.
  exit-status diffs     -- an arm that ABORTED where the other returned.
  disagreements         -- verdict against the file's own declared `:status`,
                           with the COMPARABLE DENOMINATOR printed beside it.

The denominator matters: a corpus file may declare `:status unknown`, and those
files cannot contribute to a soundness comparison. Reporting "0 disagreements"
without saying over how many is the shape that makes an unfalsifiable claim.
"""

from __future__ import annotations

import argparse
import collections
from pathlib import Path

DECIDED = ("sat", "unsat")


def read_ab(paths: list[str]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in paths:
        lines = Path(path).read_text(encoding="utf-8").splitlines()
        header = lines[0].split("\t")
        for line in lines[1:]:
            if line:
                rows.append(dict(zip(header, line.split("\t"), strict=False)))
    return rows


def read_status(path: str | None) -> dict[str, str]:
    if not path:
        return {}
    lines = Path(path).read_text(encoding="utf-8").splitlines()
    header = lines[0].split("\t")
    out: dict[str, str] = {}
    for line in lines[1:]:
        if not line:
            continue
        row = dict(zip(header, line.split("\t"), strict=False))
        out[row["file"]] = row["status"]
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ab", action="append", required=True)
    ap.add_argument("--shapes", help="a shape TSV carrying declared :status")
    ap.add_argument("--label", default="A/B")
    args = ap.parse_args()

    rows = read_ab(args.ab)
    status = read_status(args.shapes)

    a_dec = [r for r in rows if r["A"] in DECIDED]
    b_dec = [r for r in rows if r["B"] in DECIDED]
    gains = [r for r in rows if r["B"] in DECIDED and r["A"] not in DECIDED]
    losses = [r for r in rows if r["A"] in DECIDED and r["B"] not in DECIDED]
    flips = [
        r for r in rows
        if r["A"] in DECIDED and r["B"] in DECIDED and r["A"] != r["B"]
    ]
    aborts = [r for r in rows if "none" in (r["A"], r["B"])]

    print(f"== {args.label} ==")
    print(f"  rows            {len(rows)}")
    print(f"  A (default)     {len(a_dec)}")
    print(f"  B (wide)        {len(b_dec)}")
    print(f"  net             {len(b_dec) - len(a_dec):+d}")
    print(f"  gains           {len(gains)}")
    print(f"  losses          {len(losses)}")
    print(f"  sat<->unsat     {len(flips)}")
    print(f"  no-verdict rows {len(aborts)}")

    # The soundness event goes first, always.
    if flips:
        print("\n  *** SAT<->UNSAT FLIPS ***")
        for r in flips:
            print(f"    {r['file']}  A={r['A']} B={r['B']}")

    for name, group in (("GAINS", gains), ("LOSSES", losses)):
        if group:
            print(f"\n  {name}:")
            for r in group:
                print(f"    {r['file']}  A={r['A']} B={r['B']} "
                      f"A_ms={r['A_ms']} B_ms={r['B_ms']} first={r['first']}")

    if aborts:
        print("\n  rows where an arm produced NO verdict token:")
        for r in aborts[:10]:
            print(f"    {r['file']}  A={r['A']} B={r['B']}")

    # Soundness against the file's own declared status, with the denominator.
    if status:
        comparable = 0
        bad: list[str] = []
        for r in rows:
            declared = status.get(r["file"])
            if declared not in DECIDED:
                continue
            for arm in ("A", "B"):
                if r[arm] in DECIDED:
                    comparable += 1
                    if r[arm] != declared:
                        bad.append(f"{r['file']} arm {arm}: {r[arm]} vs :status {declared}")
        print(f"\n  vs declared :status -- {len(bad)} disagreement(s) over "
              f"{comparable} comparable verdicts")
        for line in bad:
            print(f"    {line}")
        if bad:
            return 1

    # A per-arm wall-clock total is reported but is NOT a claim: both arms ran
    # on the same core back to back, so the DIFFERENCE is what survives load.
    a_ms = sum(int(r["A_ms"]) for r in rows)
    b_ms = sum(int(r["B_ms"]) for r in rows)
    print(f"\n  wall clock      A {a_ms / 1000:.0f}s  B {b_ms / 1000:.0f}s  "
          f"({(b_ms - a_ms) / 1000:+.0f}s)")
    print("  order balance   " + ", ".join(
        f"{k}={v}" for k, v in sorted(
            collections.Counter(r["first"] for r in rows).items()
        )
    ))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
