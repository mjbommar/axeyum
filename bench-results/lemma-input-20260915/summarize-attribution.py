#!/usr/bin/env python3
"""LEMMA-INPUT -- size the `refresh_initial_lemmas` population by PROFILE and
publish the distribution of the pass's INPUT, from the attribution run.

D4: a row is in the population when the pass holds >= 50 % of the row's wall
budget.  NOREAD rows (the instrument reports once a second, and a row that
finishes sooner never prints) are counted as their own bucket, never as zero.

The exit status depends on the finding: a population of zero, or a run whose
rows all came back NOREAD, exits non-zero -- a summary that cannot fail is not
evidence.
"""

import collections
import math
import pathlib
import sys

SRC = pathlib.Path(sys.argv[1])
BUDGET_MS = int(sys.argv[2]) if len(sys.argv) > 2 else 24_000
INHERITED = pathlib.Path(sys.argv[3]) if len(sys.argv) > 3 else None

inherited = set()
if INHERITED and INHERITED.is_file():
    inherited = {ln.strip() for ln in INHERITED.read_text().splitlines() if ln.strip()}


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = p + z * z / (2 * n)
    r = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return ((c - r) / d, (c + r) / d)


rows = []
for line in SRC.read_text().splitlines():
    if not line.strip():
        continue
    parts = line.split("\t")
    if len(parts) < 5:
        print(f"MALFORMED: {line!r}")
        sys.exit(4)
    name, verdict, status, rss, stats = parts[0], parts[1], parts[2], parts[3], parts[4]
    fields = {}
    if stats.strip() != "NOREAD":
        for tok in stats.split():
            if "=" in tok:
                k, v = tok.split("=", 1)
                try:
                    fields[k] = int(v)
                except ValueError:
                    pass
    rows.append((name, verdict, int(status), rss, fields))

n = len(rows)
read = [r for r in rows if r[4]]
noread = [r for r in rows if not r[4]]
print(f"rows measured: {n}   with an li-stats reading: {len(read)}   NOREAD: {len(noread)}")
if not read:
    print("ABORT: no row produced a reading -- this is a fact about the instrument")
    sys.exit(3)

# --- D4 population ---------------------------------------------------------
pop = []
for name, verdict, status, rss, f in read:
    total = f.get("mutex_ms", 0) + f.get("impl_ms", 0)
    share = total / BUDGET_MS
    if share >= 0.50:
        pop.append((name, verdict, status, share, f))
pop.sort(key=lambda r: -r[3])

print()
print(f"D4 population (>= 50 % of a {BUDGET_MS} ms budget in the pass): "
      f"{len(pop)} of {len(read)} rows with a reading")
lo, hi = wilson(len(pop), len(read))
print(f"  Wilson 95 % on {len(pop)}/{len(read)}: [{lo:.1%}, {hi:.1%}]")
print()
hdr = ("row", "verdict", "exit", "pass%", "calls", "mutex_ms", "extract_ms",
       "impl_ms", "pair_iters", "max_atoms", "max_bounds", "cap_hits")
print("\t".join(hdr))
for name, verdict, status, share, f in pop:
    print("\t".join(str(x) for x in (
        name, verdict, status, f"{share:.1%}", f.get("calls"), f.get("mutex_ms"),
        f.get("extract_ms"), f.get("impl_ms"), f.get("pair_iters"),
        f.get("max_atoms"), f.get("max_bounds"), f.get("cap_hits"))))

if inherited:
    inpop = {r[0] for r in pop} & inherited
    print()
    print(f"of ADR-2075's {len(inherited)}-row bucket, in the D4 population: {len(inpop)}")
    for r in sorted(inpop):
        print(f"  {r}")
    outside = {r[0] for r in pop} - inherited
    print(f"outside that bucket: {len(outside)}")
    for r in sorted(outside):
        print(f"  {r}")

# --- the INPUT distribution (R17 / the brief's item 2) ----------------------
print()
print("INPUT distribution over every row with a reading -- this is what a cap")
print("on the pass's input would be read against:")


def quantiles(vals, label):
    if not vals:
        print(f"  {label}: NO DATA")
        return
    vals = sorted(vals)
    def q(p):
        return vals[min(len(vals) - 1, int(p * len(vals)))]
    print(f"  {label}: n={len(vals)} min={vals[0]} p50={q(0.5)} p90={q(0.9)} "
          f"p99={q(0.99)} max={vals[-1]}")


quantiles([f.get("max_atoms", 0) for *_, f in read], "max_atoms  (ctx.atoms.len())")
quantiles([f.get("max_bounds", 0) for *_, f in read], "max_bounds (simple int bounds)")
quantiles([f.get("calls", 0) for *_, f in read], "calls      (refresh entries)")

over512 = [name for name, _v, _s, _r, f in read if f.get("max_atoms", 0) > 512]
print()
print(f"rows whose atom count crosses the SIBLING's 512-atom input cap: "
      f"{len(over512)} of {len(read)}")
capped_pop = [r for r in pop if r[4].get("max_atoms", 0) > 512]
print(f"  of the D4 population: {len(capped_pop)} of {len(pop)}")

capfires = [name for name, _v, _s, _r, f in read if f.get("cap_hits", 0) > 0]
print(f"rows where MAX_INITIAL_BOUND_MUTEX_LEMMAS (the OUTPUT cap) truncated: "
      f"{len(capfires)} of {len(read)}")

# --- exit status as its own channel (R5) -----------------------------------
print()
print("exit status (its own channel):")
for status, count in sorted(collections.Counter(r[2] for r in rows).items()):
    print(f"  exit {status}: {count}")
print("verdicts:")
for verdict, count in sorted(collections.Counter(r[1] for r in rows).items()):
    print(f"  {verdict}: {count}")
peak = max((int(r[3]) for r in rows if r[3].isdigit()), default=0)
print(f"peak RSS across the run: {peak} KB")

if not pop:
    print()
    print("FINDING: the D4 population is EMPTY -- the pass dominates no measured row.")
    sys.exit(1)
