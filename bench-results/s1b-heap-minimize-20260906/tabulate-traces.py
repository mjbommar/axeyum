#!/usr/bin/env python3
import re
import sys

rows = []
cur = None
for line in open(sys.argv[1]):
    line = line.rstrip("\n")
    m = re.match(r"### (\S+) \[(\w+) (\w+) rep=(\d+)\] wall_ms=(\d+)", line)
    if m:
        cur = {
            "file": m.group(1),
            "mut": m.group(2),
            "arm": m.group(3),
            "rep": m.group(4),
            "wall": int(m.group(5)),
        }
        rows.append(cur)
        continue
    if line.startswith("; theory-layer") and cur is not None:
        for kv in line[len("; theory-layer ") :].split():
            k, _, v = kv.partition("=")
            cur[k] = v
    elif line in ("sat", "unsat", "unknown") and cur is not None:
        cur["verdict"] = line

print("file\tmut\tarm\trep\tverdict\twall_ms\tdecisions\tdec_per_s\tlearned\tmean_len\tmean_premin")
for r in rows:
    d = int(r.get("decisions", 0) or 0)
    w = r["wall"]
    lc = int(r.get("learned_clauses", 0) or 0)
    ll = int(r.get("learned_literals", 0) or 0)
    lp = int(r.get("learned_literals_premin", 0) or 0)
    ml = f"{ll / lc:.3f}" if lc else "-"
    mp = f"{lp / lc:.3f}" if lc else "-"
    dps = int(d * 1000 / w) if w else 0
    name = r["file"].replace(".smt2", "")[:34]
    print(
        f"{name}\t{r['mut']}\t{r['arm']}\t{r['rep']}\t{r.get('verdict', '-')}\t"
        f"{w}\t{d}\t{dps}\t{lc}\t{ml}\t{mp}"
    )
