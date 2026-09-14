import csv, glob, re, collections, sys, math

base = sys.argv[1]
rows = []
for f in sorted(glob.glob(base + '/bench-results/round-head-20260914/census/FAMILY.shard0*.tsv')):
    rows += list(csv.DictReader(open(f), delimiter='\t'))
still = [r for r in rows if r['c_verdict'] == 'unknown']
reps = []
for r in still:
    for col in ('r1_lines', 'r2_lines'):
        for rec in re.split(r';(?=QPROBE )', r.get(col) or ''):
            if 'held-set-replay' not in rec:
                continue
            d = dict(re.findall(r'\b(exit|ground|rounds|verdict|ms|budget_ms)=(\S+?)(?=\s|$)', rec))
            mw = re.search(r'\bwhy=(.*)$', rec, re.S)
            d['why'] = mw.group(1).strip() if mw else ''
            d['file'] = r['file']
            d['g'] = int(d.get('ground', -1))
            reps.append(d)


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (100 * max(0, c - h), 100 * min(1, c + h))


def pw(lbl, k, n):
    lo, hi = wilson(k, n)
    print(f"  {lbl}: {k}/{n} = {100*k/n:.1f}% Wilson95 [{lo:.1f}%, {hi:.1f}%]")


byfile = collections.defaultdict(list)
for d in reps:
    byfile[d['file']].append(d)

print("=== ROW-LEVEL classification (denominator: 127 still-failing rows) ===")
cls = collections.Counter()
mixed = []
for f, ds in byfile.items():
    s = {d['verdict'] for d in ds}
    if 'unsat' in s:
        k = 'refutes-on-fresh-clock'
    elif s == {'sat'}:
        k = 'sat-only (instantiation insufficient)'
    elif s == {'unknown'}:
        k = 'unknown-only (checker declined)'
    elif s == {'error'}:
        k = 'error-only'
    elif s <= {'sat', 'unknown'}:
        k = 'MIXED sat+unknown'
        mixed.append((f, ds))
    else:
        k = 'other ' + ','.join(sorted(s))
    cls[k] += 1
for k, v in cls.most_common():
    print(f"  {v:4d}  {k}")
print(f"  {sum(cls.values()):4d}  rows with >=1 replay (of 127; {127-sum(cls.values())} rows never replayed)")
print()
pw("rows whose checker declined at least once (unknown present)",
   cls['unknown-only (checker declined)'] + cls['MIXED sat+unknown'], 127)
pw("rows sat-only", cls['sat-only (instantiation insufficient)'], 127)

print()
print("=== the MIXED rows: is the UNKNOWN set BIGGER than the SAT set? ===")
bigger = 0
for f, ds in mixed:
    sg = [d['g'] for d in ds if d['verdict'] == 'sat']
    ug = [d['g'] for d in ds if d['verdict'] == 'unknown']
    flag = 'UNKNOWN-BIGGER' if min(ug) > max(sg) else 'no'
    if min(ug) > max(sg):
        bigger += 1
    print(f"  {f.split('/')[-1][:46]:48s} sat_ground={sorted(sg)} unknown_ground={sorted(ug)}  {flag}")
print(f"  -> {bigger} of {len(mixed)} mixed rows have every unknown set strictly larger than every sat set")

print()
print("=== ground-set size by replay verdict (all 122 replays) ===")
for v in ('sat', 'unknown', 'unsat', 'error'):
    g = sorted(d['g'] for d in reps if d['verdict'] == v and d['g'] >= 0)
    if not g:
        continue
    print(f"  {v:8s} n={len(g):3d}  min={g[0]:5d}  p25={g[len(g)//4]:5d}  median={g[len(g)//2]:5d}  "
          f"p75={g[3*len(g)//4]:5d}  max={g[-1]:5d}  at-cap(8192)={sum(1 for x in g if x>=8192)}")

print()
print("=== refusal vs exhausted-clock among the 78 unknown replays ===")
REFUSAL = ('exceeding the deterministic admission bound', 'exceeding the secondary bound',
           'exceeds the joint resource boundary', 'no model within the bounded integer width',
           'SAT skeleton declined after round')
unk = [d for d in reps if d['verdict'] == 'unknown']
ref = [d for d in unk if any(k in d['why'].replace('_', ' ') for k in REFUSAL)]
to = [d for d in unk if d not in ref]
pw("REFUSED by a bound/boundary (no clock exhausted)", len(ref), len(unk))
pw("EXHAUSTED the 10 s clock", len(to), len(unk))
g = sorted(d['g'] for d in ref)
print(f"  refusals: ground median={g[len(g)//2]}, at-cap={sum(1 for x in g if x>=8192)}/{len(g)}")
ms = sorted(int(d['ms']) for d in ref)
print(f"  refusals: wall ms median={ms[len(ms)//2]}  (they decline CHEAPLY)")
g = sorted(d['g'] for d in to)
print(f"  timeouts: ground median={g[len(g)//2]}, at-cap={sum(1 for x in g if x>=8192)}/{len(g)}")
