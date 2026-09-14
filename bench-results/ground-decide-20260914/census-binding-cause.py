"""Full binding-cause census of the 78 `unknown` held-set replays.

Method notes (both bought with a wrong answer):
  * records inside r1_lines/r2_lines are separated by ';QPROBE', NOT by a bare
    ';' -- the why= detail itself contains ';'. Splitting on ';' truncates the
    largest bucket and hides its nested reason.
  * a why= string may WRAP another one ("the reduced solve's own reason was
    [Kind] ...") and may APPEND one after a stats parenthetical ("...): <inner>").
    The binding cause is the innermost.
"""
import csv, glob, re, collections, sys, json

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
            d['why_raw'] = mw.group(1).strip() if mw else '<none>'
            d['file'] = r['file']
            reps.append(d)


def innermost(w):
    """Peel wrappers until the binding cause is reached."""
    hops = []
    cur = w
    for _ in range(6):
        m = re.search(r"the_reduced_solve's_own_reason_was_\[\w+\]_(.*)$", cur)
        if m:
            hops.append('reduced-solve-wrapper')
            cur = m.group(1)
            continue
        # CEGAR stats parenthetical followed by an inner reason
        m = re.search(r'lazy_function-consistency_CEGAR_inconclusive_\(.*?\):_(.*)$', cur)
        if m:
            hops.append('cegar-wrapper')
            cur = m.group(1)
            continue
        break
    return cur, hops


def canon(s):
    s = s.replace('_', ' ')
    s = re.sub(r'\(.*', '', s)          # drop stats parentheticals
    s = re.sub(r'\d+', 'N', s)
    s = re.sub(r'\s+', ' ', s).strip().rstrip(';:,')
    return s


unk = [d for d in reps if d.get('verdict') == 'unknown']
print("DENOMINATOR: 127 still-failing rows; %d replays over %d rows; unknown replays = %d"
      % (len(reps), len({d['file'] for d in reps}), len(unk)))

outer = collections.Counter()
binding = collections.Counter()
wrapped = collections.Counter()
members = collections.defaultdict(list)
for d in unk:
    o = canon(d['why_raw'].split(';')[0])
    outer[o] += 1
    inner, hops = innermost(d['why_raw'])
    b = canon(inner)
    binding[b] += 1
    members[b].append(d)
    wrapped[len(hops)] += 1

print()
print("=== LEVEL 0: the outer string (what a naive census sees) ===")
for w, c in outer.most_common():
    print(f"{c:4d}  {w}")

print()
print("=== LEVEL N: the BINDING cause (wrappers peeled) ===")
tot = 0
for w, c in binding.most_common():
    tot += c
    print(f"{c:4d}  {w}")
print(f"{tot:4d}  TOTAL")

print()
print("wrapper depth distribution:", dict(wrapped))

# ground-set size and wall time per binding cause
print()
print("=== per binding cause: ground-set size and replay wall time ===")
for w, c in binding.most_common():
    g = sorted(int(d['ground']) for d in members[w] if d.get('ground', '').isdigit())
    ms = sorted(int(d['ms']) for d in members[w] if d.get('ms', '').isdigit())
    med = lambda x: x[len(x) // 2] if x else -1
    print(f"{c:4d}  ground med={med(g):6d} min={g[0] if g else -1:5d} max={g[-1] if g else -1:5d} "
          f"| ms med={med(ms):6d} max={ms[-1] if ms else -1:6d}  | {w[:70]}")

json.dump([{'file': d['file'], 'ground': d.get('ground'), 'ms': d.get('ms'),
            'exit': d.get('exit'), 'binding': canon(innermost(d['why_raw'])[0])}
           for d in unk], open(sys.argv[2], 'w'), indent=1)
