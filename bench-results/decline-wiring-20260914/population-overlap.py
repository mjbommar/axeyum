import json, sys

sp = sys.argv[1]
base = sys.argv[2]
cegar = json.load(open(sp + '/cegar.json'))
L = base + '/bench-results/ground-decide-20260914/lists/'


def rd(n):
    return {l.strip() for l in open(L + n) if l.strip()}


skel = rd('files-skeleton.txt')
eager = rd('files-eager-ackermann.txt')
lazy = rd('files-lazy-ackermann.txt')
blast = rd('files-blast-ladder.txt')
all129 = rd('files-all129.txt')

hot = {d['file'] for d in cegar if d['lemmas_added'] >= 100}
cold = {d['file'] for d in cegar if d['lemmas_added'] == 0}
print(f"files with a CEGAR stat line at all: {len({d['file'] for d in cegar})}")
print(f"  lemmas_added >= 100 ('flooded'): {len(hot)}")
print(f"  lemmas_added == 0:               {len(cold)}")
print()
for name, s in (('skeleton-boundary (22)', skel), ('eager-ackermann (13)', eager),
                ('lazy-ackermann (8)', lazy), ('blast-ladder (11)', blast)):
    print(f"{name:<26} |set|={len(s):>3}  flooded∩={len(hot & s):>3}  zero∩={len(cold & s):>3}")
print()
print("=== flooded files, and which binding-cause list they are on ===")
for f in sorted(hot):
    tags = [t for t, s in (('SKELETON', skel), ('EAGER-ACK', eager), ('LAZY-ACK', lazy),
                           ('BLAST', blast)) if f in s]
    la = max(d['lemmas_added'] for d in cegar if d['file'] == f)
    vp = max(d['violated_pairs'] for d in cegar if d['file'] == f)
    amp = (la / vp) if vp else float('inf')
    print(f"  lemmas={la:>6} violated={vp:>5} amp={amp:>8.1f}x  {','.join(tags) or '-':<12} "
          f"{f.split('/', 1)[1][:58]}")
