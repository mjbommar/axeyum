"""ADR-2020 -- summarise the interleaved per-file A/B of the pre-SAT envelope.

Reports movement in BOTH directions, and prints every class even at zero: an
omitted row and a zero row read the same in a table and only one of them is a
measurement.
"""
import csv, glob, sys, collections, math


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (100 * max(0.0, c - h), 100 * min(1.0, c + h))


def load(pattern):
    rows = []
    for f in sorted(glob.glob(pattern)):
        rows += list(csv.DictReader(open(f), delimiter='\t'))
    return rows


def summarise(label, rows):
    print(f"\n=== {label}: {len(rows)} rows ===")
    if not rows:
        print("  (no rows)")
        return
    DECIDED = ('sat', 'unsat')
    off_dec = sum(1 for r in rows if r['off_verdict'] in DECIDED)
    on_dec = sum(1 for r in rows if r['on_verdict'] in DECIDED)
    print(f"  DIVISION TOTAL decided:  OFF(shipped) {off_dec}   ON(lever) {on_dec}"
          f"   net {on_dec - off_dec:+d}")

    moves = collections.Counter()
    gained, lost, flipped = [], [], []
    for r in rows:
        o, n = r['off_verdict'], r['on_verdict']
        if o == n:
            moves['identical'] += 1
        elif o not in DECIDED and n in DECIDED:
            moves['GAIN unknown->decided'] += 1
            gained.append(r)
        elif o in DECIDED and n not in DECIDED:
            moves['LOSS decided->unknown'] += 1
            lost.append(r)
        elif o in DECIDED and n in DECIDED:
            moves['FLIP sat<->unsat (SOUNDNESS)'] += 1
            flipped.append(r)
        else:
            moves['other (NONE/unknown churn)'] += 1
    for k in ('identical', 'GAIN unknown->decided', 'LOSS decided->unknown',
              'FLIP sat<->unsat (SOUNDNESS)', 'other (NONE/unknown churn)'):
        print(f"  {moves[k]:4d}  {k}")
    lo, hi = wilson(moves['GAIN unknown->decided'], len(rows))
    print(f"  gain rate: {moves['GAIN unknown->decided']}/{len(rows)} "
          f"Wilson95 [{lo:.1f}%, {hi:.1f}%]")
    for tag, lst in (('GAINED', gained), ('LOST', lost), ('FLIPPED', flipped)):
        for r in lst:
            print(f"    {tag}: {r['file']}  off={r['off_verdict']}({r['off_ms']}ms) "
                  f"on={r['on_verdict']}({r['on_ms']}ms) order={r['order']}")
    # wall-clock cost of the lever, which is the thing a refusal was buying
    import statistics
    do = [int(r['off_ms']) for r in rows]
    dn = [int(r['on_ms']) for r in rows]
    print(f"  wall ms: OFF median {statistics.median(do):.0f} total {sum(do)/1000:.0f}s "
          f"| ON median {statistics.median(dn):.0f} total {sum(dn)/1000:.0f}s "
          f"({sum(dn)/max(sum(do),1):.2f}x)")


if __name__ == '__main__':
    summarise(sys.argv[1], load(sys.argv[2]))
