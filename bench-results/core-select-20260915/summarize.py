#!/usr/bin/env python3
"""CORE-SELECT -- the tables the ADR quotes, derived from the committed TSVs.

    summarize.py <lane-dir>

Every proportion carries its denominator and a Wilson 95 % interval (R10), and
the comparable denominator is printed beside any zero.  Nothing here is typed by
hand: if a table is empty, that is a finding about the measurement and the exit
status says so.
"""
import math
import os
import sys


def wilson(k, n, z=1.96):
    """Wilson score interval. With n ~ 13 the normal approximation is not
    honest and the interval is what gets quoted rather than k/n."""
    if n == 0:
        return (0.0, 0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z / d * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return (p, max(0.0, c - h), min(1.0, c + h))


def pct(k, n):
    p, lo, hi = wilson(k, n)
    return f'{k}/{n} = {100 * p:.1f}% [{100 * lo:.1f}, {100 * hi:.1f}]'


def read_tsv(path):
    if not os.path.exists(path):
        return []
    with open(path) as fh:
        head = fh.readline().rstrip('\n').split('\t')
        return [dict(zip(head, line.rstrip('\n').split('\t'))) for line in fh if line.strip()]


def quantiles(xs):
    if not xs:
        return 'n=0'
    s = sorted(xs)
    n = len(s)

    def q(f):
        return s[min(n - 1, int(f * (n - 1) + 0.5))]
    return (f'n={n} min={s[0]} p25={q(.25)} med={q(.5)} p75={q(.75)} '
            f'p90={q(.9)} max={s[-1]}')


def div(f):
    return f.split('/', 1)[0]


def main():
    W = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    R = os.path.join(W, 'ref')
    red = read_tsv(os.path.join(R, 'rederive-1400.tsv'))
    spl = {r['file']: r for r in read_tsv(os.path.join(R, 'split-1400.tsv'))}
    cor = read_tsv(os.path.join(R, 'core-census.tsv'))
    sim = read_tsv(os.path.join(R, 'sim-cores.tsv'))
    pos = {r['file']: r for r in read_tsv(os.path.join(R, 'positions.tsv'))}
    fail = 0

    # ---- 1. the population, re-derived (R1)
    print('## 1. The population, re-derived on this branch\n')
    if not red:
        print('  ref/rederive-1400.tsv MISSING -- nothing below has a population')
        sys.exit(6)
    byd = {}
    for r in red:
        d = div(r['file'])
        byd.setdefault(d, []).append(r)
    print(f'{"division":<10} {"n":>5} {"decided":>8} {"undecided":>10} {"aborted":>8}')
    tot = [0, 0, 0, 0]
    for d in sorted(byd, key=lambda d: -len(byd[d])):
        rs = byd[d]
        dec = sum(1 for r in rs if r['verdict'] in ('sat', 'unsat'))
        und = sum(1 for r in rs if r['verdict'] == 'unknown')
        ab = sum(1 for r in rs if r['verdict'] == 'NOVERDICT')
        print(f'{d:<10} {len(rs):>5} {dec:>8} {und:>10} {ab:>8}')
        tot = [tot[0] + len(rs), tot[1] + dec, tot[2] + und, tot[3] + ab]
    print(f'{"TOTAL":<10} {tot[0]:>5} {tot[1]:>8} {tot[2]:>10} {tot[3]:>8}')
    if tot[3]:
        print(f'\n  NOVERDICT rows are their own bucket, never folded: {tot[3]}')

    und_set = {r['file'] for r in red if r['verdict'] == 'unknown'}

    # ---- 2. the haystack
    print('\n## 2. The haystack (conjuncts after `and`-splitting)\n')
    print(f'{"division":<10} {"undecided rows":>15}  conjunct quantiles')
    for d in sorted(byd, key=lambda d: -len(byd[d])):
        xs = [int(spl[f]['conjuncts']) for f in und_set
              if div(f) == d and f in spl]
        print(f'{d:<10} {len(xs):>15}  {quantiles(xs)}')
    allx = [int(spl[f]['conjuncts']) for f in und_set if f in spl]
    print(f'{"ALL":<10} {len(allx):>15}  {quantiles(allx)}')

    # ---- 2b. how many rows have NOTHING TO SELECT, before any solver runs
    print('\n## 2b. Rows with nothing to select (structural, no solver)\n')
    print(f'{"division":<10} {"undecided":>10} {"conj<=1":>9} {"conj<=2":>9} {"conj<=5":>9}')
    t = [0, 0, 0, 0]
    for d in sorted(byd, key=lambda d: -len(byd[d])):
        xs = [int(spl[f]['conjuncts']) for f in und_set if div(f) == d and f in spl]
        a = [len(xs), sum(1 for x in xs if x <= 1), sum(1 for x in xs if x <= 2),
             sum(1 for x in xs if x <= 5)]
        print(f'{d:<10} {a[0]:>10} {a[1]:>9} {a[2]:>9} {a[3]:>9}')
        t = [t[i] + a[i] for i in range(4)]
    print(f'{"TOTAL":<10} {t[0]:>10} {t[1]:>9} {t[2]:>9} {t[3]:>9}')
    print(f'\n  conj<=2 over all undecided rows: {pct(t[2], t[0])}')
    print('  A file with <= 2 conjuncts has at most one assertion to drop.'
          ' Selection\n  cannot be the mechanism there, whatever the core size'
          ' turns out to be.')

    # ---- 3. the reference buckets (R2)
    print('\n## 3. Reference buckets over the re-derived-undecided rows (R2)\n')
    if not cor:
        print('  ref/core-census.tsv MISSING -- R2 not measured')
        fail = 7
    else:
        seen = {r['file'] for r in cor}
        missing = und_set - seen
        buckets = {'REF-UNSAT': [], 'REF-SAT': [], 'REF-NONE': [], 'OTHER': []}
        for r in cor:
            if r['file'] not in und_set:
                continue
            s = r['split']
            b = ('REF-UNSAT' if s == 'unsat' else 'REF-SAT' if s == 'sat'
                 else 'REF-NONE' if s in ('unknown', 'TIMEOUT') else 'OTHER')
            buckets[b].append(r)
        n = sum(len(v) for v in buckets.values())
        print(f'  censused {n} of {len(und_set)} re-derived-undecided rows'
              f' ({len(missing)} not censused)')
        for b in ('REF-UNSAT', 'REF-SAT', 'REF-NONE', 'OTHER'):
            print(f'  {b:<10} {pct(len(buckets[b]), n)}')
        if buckets['OTHER']:
            kinds = {}
            for r in buckets['OTHER']:
                kinds[r['split']] = kinds.get(r['split'], 0) + 1
            print('    OTHER kinds: ' + ', '.join(f'{k}={v}' for k, v in sorted(kinds.items())))

        # ---- 4. the three sizes (R3)
        print('\n## 4. Three sizes, never conflated (R3)\n')
        ru = buckets['REF-UNSAT']
        # A DISAGREEMENT and a NON-ANSWER are different findings and must not
        # share a bucket: folding "cvc5 did not answer" into "the authorities
        # split" turns 0 disagreements into 42 and drops 34 usable rows.
        agree, noans, split, recheck = [], [], [], []
        for r in ru:
            if r['core_z3'] != 'unsat':
                recheck.append(r)
            elif r['core_cvc5'] in ('unsat', 'NO-CVC5'):
                agree.append(r)
            elif r['core_cvc5'] == 'sat':
                split.append(r)
            else:
                noans.append(r)
        print(f'  REF-UNSAT rows                        {len(ru)}')
        print(f'  z3 AND cvc5 both refute the core      {len(agree)}')
        print(f'  cvc5 did NOT ANSWER (kept, flagged)   {len(noans)}')
        print(f'  AUTHORITY-SPLIT, cvc5 says sat        {len(split)}'
              f'   <- excluded; comparable denominator {len(agree) + len(split)}')
        print(f'  z3 cannot re-check its OWN core       {len(recheck)}'
              f'   <- excluded')
        for r in (split + recheck)[:10]:
            print(f'    {r["file"]}  z3={r["core_z3"]} cvc5={r["core_cvc5"]}')
        ok = agree + noans
        print(f'\n  haystack `conjuncts`  {quantiles([int(r["conjuncts"]) for r in ok])}')
        print(f'  `z3_core` (NOT minimal) {quantiles([int(r["z3_core"]) for r in ok if r["z3_core"].isdigit()])}')
        mini = [int(r['minimal']) for r in ok
                if r['minimal'].isdigit() and r['min_status'] == 'MINIMAL']
        capped = [r for r in ok if r['min_status'] != 'MINIMAL']
        print(f'  `minimal` (1-minimal)   {quantiles(mini)}')
        print(f'  minimisation capped     {len(capped)} rows'
              f' (reported as z3_core, never as a guess)')
        if mini:
            med = sorted(mini)[len(mini) // 2]
            print(f'\n  R5(a) median minimal = {med} (pre-registered bound <= 5):'
                  f' {"PASS" if med <= 5 else "FAIL"}')
            print(f'  R5(b) REF-UNSAT share = {pct(len(ru), n)} (pre-registered >= 20 %):'
                  f' {"PASS" if n and len(ru) / n >= 0.20 else "FAIL"}')
            for lim in (1, 2, 3, 5, 10):
                print(f'    minimal <= {lim:<3} {pct(sum(1 for x in mini if x <= lim), len(mini))}')

    # ---- 5. the ceiling (R6)
    print('\n## 5. Our solver on the reference core -- a CEILING, not a gain (R6)\n')
    if not sim:
        print('  ref/sim-cores.tsv MISSING -- the ceiling is NOT MEASURED')
        fail = fail or 8
    else:
        v = {}
        for r in sim:
            v[r['verdict']] = v.get(r['verdict'], 0) + 1
        nsim = len(sim)
        print(f'  subsets handed to our solver: {nsim}')
        for k in sorted(v, key=lambda k: -v[k]):
            print(f'    {k:<12} {pct(v[k], nsim)}')
        bad = [r for r in sim if r['verdict'] == 'sat']
        print(f'\n  soundness: a reference core is unsat, so any `sat` here is a'
              f' WRONG ANSWER -- count {len(bad)} of {nsim}')
        for r in bad[:10]:
            print(f'    {r["subset"]}')
        if bad:
            fail = 9
        ab = [r for r in sim if r['rc'] not in ('0',)]
        print(f'  exit-status channel: nonzero rc on {len(ab)} of {nsim}')

    # ---- 6. could a reference-free rule contain the core? (R7)
    print('\n## 6. Fixed-k reference-free rules: does the core LIE INSIDE? (R7)\n')
    if not pos:
        print('  ref/positions.tsv MISSING -- no strategy is sized')
        fail = fail or 10
    else:
        rows = list(pos.values())
        print(f'  rows with a core: {len(rows)}')
        print(f'  suffix_need  {quantiles([int(r["suffix_need"]) for r in rows])}')
        print(f'  prefix_need  {quantiles([int(r["prefix_need"]) for r in rows])}')
        print(f'  small_need   {quantiles([int(r["small_need"]) for r in rows])}')
        print(f'\n  {"k":>5} {"suffix(k)":>24} {"prefix(k) CONTROL":>24} {"small(k)":>24}')
        for k in (1, 2, 5, 10, 25, 50, 100):
            s = sum(1 for r in rows if int(r['suffix_need']) <= k)
            p = sum(1 for r in rows if int(r['prefix_need']) <= k)
            m = sum(1 for r in rows if int(r['small_need']) <= k)
            print(f'  {k:>5} {pct(s, len(rows)):>24} {pct(p, len(rows)):>24} {pct(m, len(rows)):>24}')
        print('\n  CONTAINING an unsat core is sufficient for the subset to be'
              ' unsat.\n  DECIDING it within 24 s is a separate claim, measured in § 7.')

    # ---- 7. the classification, and the ceiling per class
    print('\n## 7. What kind of row is it, and does the ceiling hold there?\n')
    joined = read_tsv(os.path.join(R, 'joined.tsv'))
    if not joined:
        print('  ref/joined.tsv MISSING -- run join-census.py')
        fail = fail or 13
    else:
        order = ['SINGLETON', 'NEEDLE', 'WHOLE', 'CORE-FAILED', 'REF-SAT',
                 'REF-NONE', 'ROW-ABORT', 'MIN-MISSING', 'NOT-CENSUSED']
        cls = {}
        for r in joined:
            cls.setdefault(r['class'], []).append(r)
        n = len(joined)
        print(f'{"class":<14} {"n":>5}  {"our verdict on the reference core"}')
        for c in order + sorted(k for k in cls if k not in order):
            rs = cls.get(c, [])
            if not rs:
                continue
            v = {}
            for r in rs:
                v[r['core_ours']] = v.get(r['core_ours'], 0) + 1
            detail = ' '.join(f'{k}={v[k]}' for k in sorted(v, key=lambda k: -v[k]))
            print(f'{c:<14} {len(rs):>5}  {detail}')
        print(f'{"TOTAL":<14} {n:>5}')

        # the ceiling, on the rows where a ceiling is even defined
        have = [r for r in joined if r['class'] in ('SINGLETON', 'NEEDLE', 'WHOLE')]
        dec = [r for r in have if r['core_ours'] == 'unsat']
        sim_ran = [r for r in have if r['core_ours'] != 'NOT-SIMULATED']
        print(f'\n  rows with a core                 {len(have)}')
        print(f'  simulated                        {len(sim_ran)}')
        print(f'  WOULD-DECIDE (our solver: unsat) {pct(len(dec), len(sim_ran))}')
        print('  This is the CEILING (R6): what selection could buy if selection'
              '\n  were free and perfect. It is not a gain and not a conversion.')
        byc = {}
        for r in sim_ran:
            k = r['class']
            byc.setdefault(k, [0, 0])
            byc[k][1] += 1
            byc[k][0] += 1 if r['core_ours'] == 'unsat' else 0
        for k in sorted(byc):
            print(f'    {k:<12} {pct(byc[k][0], byc[k][1])}')
        byd2 = {}
        for r in sim_ran:
            k = r['division']
            byd2.setdefault(k, [0, 0])
            byd2[k][1] += 1
            byd2[k][0] += 1 if r['core_ours'] == 'unsat' else 0
        print('\n  by division:')
        for k in sorted(byd2, key=lambda k: -byd2[k][1]):
            print(f'    {k:<12} {pct(byd2[k][0], byd2[k][1])}')

    # ---- 8. the reference-free strategies, decided by OUR solver (R7)
    print('\n## 8. Reference-free fixed-k rules, decided by OUR solver (R7)\n')
    strat = read_tsv(os.path.join(R, 'sim-subsets.tsv'))
    if not strat:
        print('  ref/sim-subsets.tsv MISSING -- no strategy was sized.'
              ' Reported as DID NOT RUN, never as zero.')
    else:
        agg = {}
        for r in strat:
            name = r['subset']
            # <flat>.<tag><k>.smt2
            mid = name[:-len('.smt2')].rsplit('.', 1)[-1]
            tag = mid.rstrip('0123456789')
            k = mid[len(tag):]
            if not k:
                continue
            agg.setdefault((tag, int(k)), []).append(r['verdict'])
        print(f'  {"rule":<10} {"k":>5} {"our unsat":>26}  {"sat":>5}')
        best = (0, None)
        for (tag, k) in sorted(agg, key=lambda t: (t[0], t[1])):
            vs = agg[(tag, k)]
            u = sum(1 for v in vs if v == 'unsat')
            s = sum(1 for v in vs if v == 'sat')
            print(f'  {tag:<10} {k:>5} {pct(u, len(vs)):>26}  {s:>5}')
            if u > best[0]:
                best = (u, (tag, k, len(vs)))
        print('\n  `prefix` is the CONTROL. If it scores like `suffix`, position'
              '\n  carries no information and the suffix rule is not a finding.')

        # R9: a strategy must reach the CEILING, not the population.  The
        # denominator is the ceiling-positive rows, because a rule cannot
        # convert a row we would not decide with the answer handed to us.
        ceil_n = len([r for r in joined if r.get('core_ours') == 'unsat']) if joined else 0
        if best[1] and ceil_n:
            tag, k, n_rows = best[1]
            frac = best[0] / ceil_n
            print(f'\n  best single fixed rule: {tag}({k}) -> {pct(best[0], ceil_n)}'
                  f' of the {ceil_n}-row CEILING')
            print(f'  R9 build gate (>= 50 % of the ceiling): '
                  f'{"PASS" if frac >= 0.50 else "FAIL"}')
            print(f'  against the whole undecided population: '
                  f'{pct(best[0], len(joined))}')

    sys.exit(fail)


main()
