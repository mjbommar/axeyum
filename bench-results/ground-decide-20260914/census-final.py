"""ADR-2020 -- the complete binding-cause census of ADR-2015's 78 declining replays.

Two method points, each bought with a wrong answer in this lane:

1. Records inside `r1_lines`/`r2_lines` are separated by `;QPROBE`, NOT by a
   bare `;`. The `why=` detail itself contains `;`, so splitting on `;`
   truncates the LARGEST bucket and silently drops its nested reason. This
   lane's first census made that mistake and reported
   `Timeout|preprocessed dispatch timeout after reduced solve` as one cause of
   25; it is four causes.

2. A `why=` may WRAP another (`the reduced solve's own reason was [Kind] ...`)
   or APPEND one after a stats parenthetical (`...): <inner>`). The binding
   cause is the innermost; the outer census is printed beside it so the
   difference is visible rather than asserted.
"""
import csv, glob, re, collections, sys, math


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (100 * max(0.0, c - h), 100 * min(1.0, c + h))


def load(base):
    rows = []
    for f in sorted(glob.glob(base + '/bench-results/round-head-20260914/census/FAMILY.shard0*.tsv')):
        rows += list(csv.DictReader(open(f), delimiter='\t'))
    return rows


def replays(rows):
    out = []
    for r in rows:
        for col in ('r1_lines', 'r2_lines'):
            for rec in re.split(r';(?=QPROBE )', r.get(col) or ''):
                if 'held-set-replay' not in rec:
                    continue
                d = dict(re.findall(r'\b(exit|ground|rounds|verdict|ms)=(\S+?)(?=\s|$)', rec))
                mw = re.search(r'\bwhy=(.*)$', rec, re.S)
                d['why'] = (mw.group(1) if mw else '').replace('_', ' ')
                d['file'] = r['file']
                d['div'] = r['file'].split('/')[0]
                d['g'] = int(d.get('ground', -1))
                out.append(d)
    return out


def innermost(w):
    cur = w
    for _ in range(6):
        m = re.search(r"the reduced solve's own reason was \[\w+\] (.*)$", cur)
        if m:
            cur = m.group(1)
            continue
        m = re.search(r'lazy function-consistency CEGAR inconclusive \(.*?\): (.*)$', cur)
        if m:
            cur = m.group(1)
            continue
        break
    return cur


def canon(s):
    s = re.sub(r'\(.*', '', s)
    s = re.sub(r'\d+', 'N', s)
    return re.sub(r'\s+', ' ', s).strip().rstrip(';:,')


REFUSAL = ('exceeding the deterministic admission bound', 'exceeding the secondary bound',
           'exceeds the joint resource boundary', 'no model within the bounded integer width',
           'SAT skeleton declined after round')

if __name__ == '__main__':
    base = sys.argv[1]
    rows = load(base)
    still = [r for r in rows if r['c_verdict'] == 'unknown']
    reps = replays(still)
    unk = [d for d in reps if d['verdict'] == 'unknown']
    N = len(still)
    print(f"DENOMINATOR: {N} still-failing rows (ADR-2015's 129 winnable minus the 2 it "
          f"drops as sometimes-decided)")
    print(f"replays {len(reps)} over {len({d['file'] for d in reps})} rows; "
          f"verdicts {dict(collections.Counter(d['verdict'] for d in reps))}")

    print("\n--- 1. THE 78/40 SPLIT, at BOTH levels (they are different numbers) ---")
    print(f"  REPLAY level: unknown 78 / sat 40 / unsat 2 / error 2  (ADR-2015's split)")
    byfile = collections.defaultdict(set)
    for d in reps:
        byfile[d['file']].add(d['verdict'])
    cls = collections.Counter()
    for f, s in byfile.items():
        if 'unsat' in s:
            cls['refutes on a fresh clock'] += 1
        elif s == {'sat'}:
            cls['sat-only: instantiation insufficient'] += 1
        elif s == {'unknown'}:
            cls['unknown-only: OUR CHECKER DECLINED'] += 1
        elif s == {'error'}:
            cls['error-only'] += 1
        else:
            cls['MIXED sat+unknown (not separable)'] += 1
    print("  ROW level:")
    for k, v in cls.most_common():
        lo, hi = wilson(v, N)
        print(f"    {v:4d}  {k:42s}  {100*v/N:5.1f}% [{lo:.1f}%, {hi:.1f}%]")
    print(f"    {N - sum(cls.values()):4d}  rows that never reached a replay")

    print("\n--- 2. BINDING CAUSE of the 78 (wrappers peeled) vs the outer string ---")
    outer = collections.Counter(canon(d['why'].split(';')[0]) for d in unk)
    print("  OUTER string (what a naive census sees):", len(outer), "buckets")
    for w, c in outer.most_common():
        print(f"    {c:4d}  {w[:88]}")
    binding = collections.Counter(canon(innermost(d['why'])) for d in unk)
    print("  BINDING cause:", len(binding), "buckets")
    for w, c in binding.most_common():
        lo, hi = wilson(c, len(unk))
        print(f"    {c:4d}  [{100*c/len(unk):4.1f}% {lo:.1f}-{hi:.1f}]  {w[:76]}")

    print("\n--- 3. REFUSAL vs EXHAUSTED CLOCK ---")
    ref = [d for d in unk if any(k in d['why'] for k in REFUSAL)]
    to = [d for d in unk if d not in ref]
    for lbl, g in (('REFUSED by a bound (policy)', ref), ('EXHAUSTED the clock (capability)', to)):
        lo, hi = wilson(len(g), len(unk))
        gs = sorted(x['g'] for x in g)
        ms = sorted(int(x['ms']) for x in g)
        dv = collections.Counter(x['div'] for x in g)
        print(f"  {len(g):3d}/{len(unk)} = {100*len(g)/len(unk):.1f}% [{lo:.1f}%, {hi:.1f}%]  {lbl}")
        print(f"        ground median {gs[len(gs)//2]:5d} (at 8192 cap: {sum(1 for x in gs if x>=8192)})"
              f"  wall ms median {ms[len(ms)//2]:6d}  {dict(dv)}")
