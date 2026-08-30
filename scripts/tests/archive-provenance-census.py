import json, os, re, collections, sys
ROOT = os.getcwd()
PAT = re.compile(r'check-[a-z0-9-]+\.(?:py|sh)')
cites = collections.defaultdict(set)   # script -> set of artifact paths
for dirpath, dirnames, filenames in os.walk('artifacts'):
    for fn in filenames:
        p = os.path.join(dirpath, fn)
        try:
            txt = open(p, encoding='utf-8', errors='replace').read()
        except Exception:
            continue
        for m in PAT.findall(txt):
            cites[m].add(p)
live = set(os.listdir('scripts'))
arch = set(os.listdir('scripts/archive')) if os.path.isdir('scripts/archive') else set()
buckets = collections.defaultdict(list)
for s, ps in cites.items():
    if s in live: b = 'LIVE'
    elif s in arch: b = 'ARCHIVED'
    else: b = 'MISSING'
    buckets[b].append((s, sorted(ps)))
for b in ('LIVE','ARCHIVED','MISSING'):
    print(f'{b}: {len(buckets[b])} distinct scripts, {sum(len(p) for _,p in buckets[b])} citation-artifact pairs')
print()
for b in ('ARCHIVED','MISSING'):
    print(f'--- {b} ---')
    for s, ps in sorted(buckets[b]):
        top = collections.Counter(p.split('/')[1] for p in ps)
        print(f'  {s}  [{len(ps)} artifacts: {dict(top)}]')
