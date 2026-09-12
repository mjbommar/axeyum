#!/usr/bin/env python3
"""Classify a census TSV by the solver's own `give-up detail`.

The 2026-09-12 `dispatch_reduced` fix (ADR-1925) makes the top class of the
previous census a *carrier*: the row now reads

    preprocessed dispatch timeout after reduced solve; the reduced solve's own
    reason was [Kind] <inner detail>

so the honest cause is the INNER detail, not the prefix.  This script reports
both: the raw prefix count (comparable to the old census) and the decomposed
count (what the class actually is).
"""
import argparse
import collections
import csv
import re

CARRIER = "preprocessed dispatch timeout after reduced solve"
INNER_RE = re.compile(r"the reduced solve's own reason was \[(\w+)\]\s*(.*)$", re.S)


def normalise(detail):
    """Collapse a detail to a comparable class label."""
    d = detail.strip()
    d = re.sub(r"#\d+", "#N", d)
    d = re.sub(r"\b\d+\b", "N", d)
    return d[:150]


def decompose(row):
    """Return (outer_class, honest_class, honest_kind)."""
    detail = row["detail"]
    outer = normalise(detail.split(";")[0]) if detail != "none" else "NO REASON"
    if detail.startswith(CARRIER):
        m = INNER_RE.search(detail)
        if m:
            return CARRIER, normalise(m.group(2)), m.group(1)
        return CARRIER, "CARRIER WITH NO INNER REASON", row["kind"]
    if detail == "none":
        return "NO REASON", "NO REASON", row["kind"]
    return normalise(detail), normalise(detail), row["kind"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("census")
    ap.add_argument("--md", help="write a markdown table here")
    args = ap.parse_args()
    rows = list(csv.DictReader(open(args.census), delimiter="\t"))
    print(f"{len(rows)} rows")
    verd = collections.Counter(r["verdict"] for r in rows)
    print("verdicts:", dict(verd))
    print("non-zero rc:", sum(1 for r in rows if r["rc"] != "0"))
    print("no stated reason:", sum(1 for r in rows if r["detail"] == "none"))

    att = collections.Counter(r["attempts"] for r in rows)
    print("attempts distribution:", dict(sorted(att.items(), key=lambda kv: int(kv[0]))))

    outer = collections.Counter()
    honest = collections.Counter()
    honest_kind = collections.Counter()
    for r in rows:
        o, h, k = decompose(r)
        outer[o] += 1
        honest[h] += 1
        honest_kind[k] += 1

    n = len(rows)
    print("\n--- OUTER (the old census's classes) ---")
    for k, v in outer.most_common():
        print(f"{v:4d} {100*v/n:5.1f}%  {k}")
    print("\n--- HONEST (carrier decomposed) ---")
    for k, v in honest.most_common():
        print(f"{v:4d} {100*v/n:5.1f}%  {k}")
    print("\n--- honest kind ---")
    for k, v in honest_kind.most_common():
        print(f"{v:4d}  {k}")
    print("\n--- bound_by ---")
    for k, v in collections.Counter(r["bound_by"] for r in rows).most_common():
        print(f"{v:4d}  {k}")
    print("\n--- last ---")
    for k, v in collections.Counter(r["last"] for r in rows).most_common():
        print(f"{v:4d}  {k}")

    if args.md:
        with open(args.md, "w") as fh:
            fh.write("| honest cause (carrier decomposed) | files | share |\n|---|---:|---:|\n")
            for k, v in honest.most_common():
                fh.write(f"| `{k}` | {v} | {100*v/n:.0f}% |\n")
        print("wrote", args.md)


if __name__ == "__main__":
    main()
