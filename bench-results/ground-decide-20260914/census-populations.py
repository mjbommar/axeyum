import csv, glob, re, collections, sys

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
            d['why'] = (mw.group(1) if mw else '').replace('_', ' ')
            d['file'] = r['file']
            d['g'] = int(d.get('ground', -1))
            d['div'] = r['file'].split('/')[0]
            reps.append(d)
unk = [d for d in reps if d['verdict'] == 'unknown']

REFUSAL = ('exceeding the deterministic admission bound', 'exceeding the secondary bound',
           'exceeds the joint resource boundary', 'no model within the bounded integer width',
           'SAT skeleton declined after round')
for d in unk:
    d['cls'] = 'REFUSED' if any(k in d['why'] for k in REFUSAL) else 'TIMEOUT'

print("=== the 78 unknown replays: class x division ===")
t = collections.Counter((d['cls'], d['div']) for d in unk)
divs = sorted({d['div'] for d in unk})
print(f"  {'':10s} " + "".join(f"{x:>10s}" for x in divs))
for c in ('REFUSED', 'TIMEOUT'):
    print(f"  {c:10s} " + "".join(f"{t[(c,x)]:10d}" for x in divs))

print()
print("=== binding cause x division ===")


def canon(s):
    s = re.sub(r'\(.*', '', s)
    s = re.sub(r'\d+', 'N', s)
    return re.sub(r'\s+', ' ', s).strip().rstrip(';:,')


def innermost(w):
    cur = w
    for _ in range(6):
        m = re.search(r"the reduced solve's own reason was \[\w+\] (.*)$", cur)
        if m:
            cur = m.group(1); continue
        m = re.search(r'lazy function-consistency CEGAR inconclusive \(.*?\): (.*)$', cur)
        if m:
            cur = m.group(1); continue
        break
    return cur


agg = collections.defaultdict(lambda: collections.Counter())
for d in unk:
    agg[canon(innermost(d['why']))][d['div']] += 1
for k in sorted(agg, key=lambda k: -sum(agg[k].values())):
    tot = sum(agg[k].values())
    parts = " ".join(f"{dv}={agg[k][dv]}" for dv in divs if agg[k][dv])
    print(f"  {tot:4d}  {parts:28s}  {k[:72]}")

print()
print("=== ground-set size by class ===")
for c in ('REFUSED', 'TIMEOUT'):
    g = sorted(d['g'] for d in unk if d['cls'] == c)
    ms = sorted(int(d['ms']) for d in unk if d['cls'] == c)
    print(f"  {c}: n={len(g)} ground min={g[0]} med={g[len(g)//2]} max={g[-1]} | "
          f"ms med={ms[len(ms)//2]} (10s budget)")
