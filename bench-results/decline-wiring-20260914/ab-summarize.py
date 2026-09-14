"""ADR-2030 -- summarize an interleaved A/B, with Wilson intervals.

Reads the shards of one arm-pair and reports GAIN / LOSS / FLIP / unchanged,
plus wall clock. A "decided" verdict is `sat` or `unsat`; `unknown` and `NONE`
(the harness timeout / no parseable line) are both undecided.

FLIP is reported separately from GAIN and LOSS and is the only one of the three
that is a SOUNDNESS finding: `sat` on one arm and `unsat` on the other means one
of them is wrong.

Usage: ab-summarize.py <label> <tsv>...
"""
import csv, sys, math

DECIDED = {"sat", "unsat"}


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = p + z * z / (2 * n)
    s = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    # Clamp. At k = 0 the algebra gives exactly 0, but in floating point c and s
    # are equal-but-not-identical and the lower bound prints as `-0.0%`. A
    # negative probability in a published table is a defect, not a rounding
    # nicety, so it is fixed here rather than in the prose that quotes it.
    lo = max(0.0, (c - s) / d * 100)
    hi = min(100.0, (c + s) / d * 100)
    return (lo, hi)


label = sys.argv[1]
rows = []
for path in sys.argv[2:]:
    rows += list(csv.DictReader(open(path), delimiter="\t"))

gain, loss, flip, same = [], [], [], 0
off_dec = on_dec = 0
off_ms = on_ms = 0
for r in rows:
    o, n = r["off_verdict"], r["on_verdict"]
    off_ms += int(r["off_ms"])
    on_ms += int(r["on_ms"])
    off_dec += o in DECIDED
    on_dec += n in DECIDED
    if o in DECIDED and n in DECIDED and o != n:
        flip.append(r)
    elif o not in DECIDED and n in DECIDED:
        gain.append(r)
    elif o in DECIDED and n not in DECIDED:
        loss.append(r)
    else:
        same += 1

n = len(rows)
print(f"=== {label} ===")
print(f"rows                 {n}")
print(f"OFF decided          {off_dec}")
print(f"ON  decided          {on_dec}")
print(f"GAIN (off undec -> on dec)  {len(gain)}   Wilson 95% "
      f"[{wilson(len(gain), n)[0]:.1f}%, {wilson(len(gain), n)[1]:.1f}%]")
print(f"LOSS (off dec -> on undec)  {len(loss)}   Wilson 95% "
      f"[{wilson(len(loss), n)[0]:.1f}%, {wilson(len(loss), n)[1]:.1f}%]")
print(f"FLIP (sat<->unsat)          {len(flip)}   <- SOUNDNESS if nonzero")
print(f"unchanged                   {same}")
print(f"wall OFF {off_ms/1000:.0f}s   ON {on_ms/1000:.0f}s   "
      f"ratio {on_ms/off_ms if off_ms else float('nan'):.3f}x")
for name, bucket in (("GAIN", gain), ("LOSS", loss), ("FLIP", flip)):
    for r in bucket:
        print(f"  {name}\t{r['off_verdict']}({r['off_ms']}ms) -> "
              f"{r['on_verdict']}({r['on_ms']}ms)\torder={r['order']}\t{r['file']}")
