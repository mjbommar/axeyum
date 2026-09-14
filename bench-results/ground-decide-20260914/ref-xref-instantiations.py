import csv, glob, re, sys, collections
sys.path.insert(0, 'bench-results/ground-decide-20260914')
from importlib import import_module
cf = import_module('census-final'.replace('-', '_')) if False else None

base = '.'
rows = []
for f in sorted(glob.glob(base + '/bench-results/round-head-20260914/census/FAMILY.shard0*.tsv')):
    rows += list(csv.DictReader(open(f), delimiter='\t'))
still = [r for r in rows if r['c_verdict'] == 'unknown']
g = {}
for r in still:
    for col in ('r1_lines', 'r2_lines'):
        for rec in re.split(r';(?=QPROBE )', r.get(col) or ''):
            if 'held-set-replay' not in rec or 'joint_resource_boundary' not in rec:
                continue
            m = re.search(r'ground=(\d+)', rec)
            if m:
                g[r['file']] = max(g.get(r['file'], 0), int(m.group(1)))

ref = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
print(f"{'file':62s} {'cvc5':6s} {'ms':>6s} {'inst':>6s} {'our_ground':>10s}")
z = nz = 0
for r in ref:
    og = g.get(r['file'], -1)
    inst = int(r['inst_tuples'])
    print(f"{r['file'].split('/')[-1][:60]:62s} {r['verdict']:6s} {r['total_ms']:>6s} "
          f"{inst:>6d} {og:>10d}")
    if r['verdict'] == 'unsat':
        if inst == 0:
            z += 1
        else:
            nz += 1
print()
print(f"cvc5 refuted with ZERO instantiations: {z};  with >=1: {nz}")
caps = [f for f, v in g.items() if v >= 8192]
print(f"our held set AT THE 8192 ADMISSION CAP on {len(caps)} of {len(g)} of these files")
zf = [r['file'] for r in ref if r['verdict'] == 'unsat' and int(r['inst_tuples']) == 0]
print(f"of the {len(zf)} cvc5 refutes with zero instantiations, "
      f"{sum(1 for f in zf if g.get(f, 0) >= 8192)} are at OUR 8192 cap")
import statistics
ms = [int(r['total_ms']) for r in ref if r['verdict'] == 'unsat']
print(f"cvc5 totalTime on the {len(ms)} it refutes: median {statistics.median(ms):.0f} ms, "
      f"min {min(ms)}, max {max(ms)}")
