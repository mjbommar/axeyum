"""Distribution of the lazy function-consistency CEGAR stats across the committed
census. Method: the CEGAR stats parenthetical is emitted by
`FunctionConsistencyStats::summary` and survives into the give-up / replay
strings verbatim (spaces replaced by `_` in the QPROBE lines). Records are split
on ';QPROBE' per ADR-2020 R1.
"""
import csv, glob, re, sys, statistics, collections, json

base = sys.argv[1]
rows = []
for f in sorted(glob.glob(base + '/bench-results/round-head-20260914/census/FAMILY.shard0*.tsv')):
    rows += list(csv.DictReader(open(f), delimiter='\t'))

FIELDS = ('applications', 'function_groups', 'potential_pairs', 'solve_rounds',
          'elapsed_ms', 'sat_candidates', 'pair_checks', 'equal_arg_pairs',
          'violated_pairs', 'preseeded_lemmas', 'sibling_lemmas', 'lemmas_added',
          'last_new_lemmas')

obs = []
for r in rows:
    blob = '\t'.join(v or '' for v in r.values())
    for m in re.finditer(r'CEGAR[_ ]inconclusive[_ ]\(([^)]*)\)', blob):
        # NOTE: the separator inside the parenthetical is `,_`, and `\w` eats the
        # leading `_` into the key. Strip it, or every key but the first is
        # mis-named and the filter below silently drops every observation --
        # which is exactly what the first version of this script did (0 rows).
        d = {k.lstrip('_'): v for k, v in re.findall(r'(\w+)=(-?\d+)', m.group(1))}
        if 'lemmas_added' not in d:
            continue
        d = {k: int(v) for k, v in d.items() if k in FIELDS}
        d['file'] = r['file']
        d['c_verdict'] = r['c_verdict']
        obs.append(d)

# dedupe identical (file, full stat tuple) -- the same string can appear in both
# the give-up column and a replay column for one exit.
seen = set()
uniq = []
for d in obs:
    key = (d['file'],) + tuple(d.get(f, -1) for f in FIELDS)
    if key in seen:
        continue
    seen.add(key)
    uniq.append(d)

print(f"CEGAR stat observations: {len(obs)} raw, {len(uniq)} distinct "
      f"over {len({d['file'] for d in uniq})} files")
print(f"  of which the file's shipped verdict is unknown: "
      f"{sum(1 for d in uniq if d['c_verdict'] == 'unknown')}")
print()


def q(xs, p):
    xs = sorted(xs)
    if not xs:
        return -1
    return xs[min(len(xs) - 1, int(p * len(xs)))]


print(f"{'field':>20} {'n':>4} {'min':>8} {'p25':>8} {'med':>9} {'p75':>9} {'p90':>9} {'max':>9}")
for f in FIELDS:
    xs = [d[f] for d in uniq if f in d]
    if not xs:
        continue
    print(f"{f:>20} {len(xs):>4} {min(xs):>8} {q(xs,.25):>8} {q(xs,.5):>9} "
          f"{q(xs,.75):>9} {q(xs,.9):>9} {max(xs):>9}")

print()
print("=== per-observation, sorted by lemmas_added ===")
print(f"{'viol':>6} {'eqarg':>7} {'lemadd':>8} {'lastnew':>8} {'rounds':>7} {'apps':>6} "
      f"{'potpairs':>9} {'ms':>7}  file")
for d in sorted(uniq, key=lambda x: -x.get('lemmas_added', 0)):
    print(f"{d.get('violated_pairs',-1):>6} {d.get('equal_arg_pairs',-1):>7} "
          f"{d.get('lemmas_added',-1):>8} {d.get('last_new_lemmas',-1):>8} "
          f"{d.get('solve_rounds',-1):>7} {d.get('applications',-1):>6} "
          f"{d.get('potential_pairs',-1):>9} {d.get('elapsed_ms',-1):>7}  "
          f"{d['file'].split('/',1)[1][:60]}")

print()
print("=== how many observations would a per-round cap of N have bound? ===")
print("(bound == last_new_lemmas > N on the largest round we can see)")
for cap in (1, 8, 16, 32, 64, 128, 256, 512, 1024, 4096):
    n = sum(1 for d in uniq if d.get('last_new_lemmas', 0) > cap)
    tot = sum(1 for d in uniq if 'last_new_lemmas' in d)
    print(f"  cap={cap:>5}: binds {n}/{tot}")

json.dump(uniq, open(sys.argv[2], 'w'), indent=1)
