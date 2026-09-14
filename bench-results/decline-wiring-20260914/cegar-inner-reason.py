"""Why does the lazy function-consistency loop stop after 2 or 3 rounds?

There is NO round cap in `check_with_function_consistency` -- the loop runs until
the candidate model is functionally consistent, or until the inner `solve`
returns `Unsat` (done) or `Unknown` (give up). So `solve_rounds=2` is not "the
CEGAR converged in two rounds"; it is "the CEGAR's SECOND solve did not finish".

This extracts what the inner solve said, per observation, against the size of the
batch the previous round dumped into it.

Usage: cegar-inner-reason.py <repo-root>
"""
import csv, glob, re, sys, collections

base = sys.argv[1]
rows = []
for f in sorted(glob.glob(base + '/bench-results/round-head-20260914/census/FAMILY.shard0*.tsv')):
    rows += list(csv.DictReader(open(f), delimiter='\t'))

pat = re.compile(r'CEGAR[_ ]inconclusive[_ ]\(([^)]*)\):[_ ](.*?)(?=;QPROBE|\t|$)', re.S)
obs = []
for r in rows:
    blob = '\t'.join(v for v in r.values() if isinstance(v, str) and v)
    for m in pat.finditer(blob):
        d = {k.lstrip('_'): int(v) for k, v in re.findall(r'(\w+)=(-?\d+)', m.group(1))}
        inner = re.sub(r'\d+', 'N', m.group(2).replace('_', ' '))
        inner = re.sub(r'\(.*', '', inner)
        inner = re.sub(r'\s+', ' ', inner).strip().rstrip(';:,')
        obs.append((d.get('lemmas_added', -1), d.get('solve_rounds', -1), inner, r['file']))

seen, uniq = set(), []
for o in obs:
    if o in seen:
        continue
    seen.add(o)
    uniq.append(o)

print(f"observations with a readable inner reason: {len(uniq)}")
print()
print("=== inner reason, by whether the batch flooded ===")
for label, sel in (("lemmas_added >= 100 (FLOODED)", lambda x: x[0] >= 100),
                   ("lemmas_added == 0", lambda x: x[0] == 0)):
    sub = [o for o in uniq if sel(o)]
    print(f"\n{label}: {len(sub)}")
    for reason, n in collections.Counter(o[2] for o in sub).most_common():
        print(f"  {n:>3}  {reason[:88]}")

print()
print("=== per flooded observation ===")
print(f"{'lemmas':>7} {'rounds':>7}  inner reason")
for la, rd, inner, f in sorted((o for o in uniq if o[0] >= 100), reverse=True):
    print(f"{la:>7} {rd:>7}  {inner[:70]}")
