#!/usr/bin/env python3
"""Summarise the ADR-2143 A/B shard TSVs (`ab-run.sh` output).

Per division: files, decided per arm (sat+unsat), sat/unsat per arm, movers
(A and B verdicts differ), `:status` disagreements per arm (a DECIDED verdict
against a DECIDED `:status` that differs -- `unknown` on either side is not a
disagreement), non-zero exit statuses per arm, and total wall per arm.
Prints a Markdown table and the mover rows. Exit status is 1 if any arm
disagrees with a `:status` or any mover is present, so a pipeline cannot read
a red run as green.
"""
import glob
import sys
from collections import defaultdict


def decided(v):
    return v in ("sat", "unsat")


def main(paths):
    rows = []
    for p in paths:
        with open(p, encoding="utf-8") as fh:
            header = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                parts = line.rstrip("\n").split("\t")
                if len(parts) != len(header):
                    continue
                rows.append(dict(zip(header, parts)))
    per = defaultdict(lambda: defaultdict(int))
    movers = []
    dis = []
    for r in rows:
        div = r["file"].split("/", 1)[0]
        d = per[div]
        d["files"] += 1
        for arm in "AB":
            v = r[arm]
            if decided(v):
                d[f"{arm}_decided"] += 1
                d[f"{arm}_{v}"] += 1
            if r[f"{arm}_rc"] != "0":
                d[f"{arm}_rc_nonzero"] += 1
            d[f"{arm}_ms"] += int(r[f"{arm}_ms"])
            st = r["status"]
            if decided(v) and decided(st) and v != st:
                d[f"{arm}_status_disagree"] += 1
                dis.append((arm, r["file"], v, st))
        if r["A"] != r["B"]:
            d["movers"] += 1
            movers.append(r)
    cols = ["files", "A_decided", "B_decided", "A_sat", "A_unsat", "B_sat", "B_unsat",
            "movers", "A_status_disagree", "B_status_disagree", "A_rc_nonzero",
            "B_rc_nonzero", "A_ms", "B_ms"]
    print("| division | " + " | ".join(cols) + " |")
    print("| --- | " + " | ".join("---:" for _ in cols) + " |")
    tot = defaultdict(int)
    for div in sorted(per):
        d = per[div]
        print(f"| {div} | " + " | ".join(str(d[c]) for c in cols) + " |")
        for c in cols:
            tot[c] += d[c]
    print("| **all** | " + " | ".join(str(tot[c]) for c in cols) + " |")
    print()
    print(f"MOVERS={len(movers)}")
    for r in movers:
        print("\t".join([r["file"], r["A"], r["A_ms"], r["A_rc"], r["B"], r["B_ms"], r["B_rc"], r["status"]]))
    print(f"STATUS_DISAGREEMENTS={len(dis)}")
    for arm, f, v, st in dis:
        print(f"{arm}\t{f}\t{v}\t:status {st}")
    return 1 if (movers or dis) else 0


if __name__ == "__main__":
    files = sys.argv[1:] or sorted(glob.glob("*.shard*.tsv"))
    raise SystemExit(main(files))
