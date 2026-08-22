"""Extend the Kaser--Lemire finite handoff: for each n, find an irreducible x^n + g with
deg g <= floor(n/2), preferring trinomials then pentanomials. flint factor() finds it; an
independent pure-Python Rabin test (lemire_anchor.is_irreducible_py) re-verifies each witness.
Output lines: n <shape> <exponents> verified=<bool> tests=<k>."""
import sys, time, itertools, random
sys.path.insert(0, '/home/mjbommar/projects/personal/axeyum/scripts/lemire-signed-trace')
import flint
from multiprocessing import Pool
from lemire_anchor import is_irreducible_py

def irreducible_flint(exps, n):
    coeffs = [0]*(n+1)
    for e in exps: coeffs[e] ^= 1
    coeffs[n] = 1; coeffs[0] = 1
    _, facs = flint.nmod_poly(coeffs, 2).factor()
    return len(facs) == 1 and facs[0][1] == 1

def search(n):
    half = n // 2
    tests = 0
    # trinomials x^n + x^k + 1, k <= half
    for k in range(1, half + 1):
        tests += 1
        if irreducible_flint((k,), n):
            return n, 'trinomial', (k,), tests
    # pentanomials: random order over a<b<c<=half (deterministic seed)
    rng = random.Random(n)
    seen = set()
    for _ in range(200000):
        a, b, c = sorted(rng.sample(range(1, half + 1), 3))
        if (a, b, c) in seen: continue
        seen.add((a, b, c)); tests += 1
        if irreducible_flint((a, b, c), n):
            return n, 'pentanomial', (a, b, c), tests
    return n, 'none-found', (), tests

def verify(n, exps):
    f = (1 << n) | 1
    for e in exps: f ^= 1 << e
    return is_irreducible_py(f)

def job(n):
    t = time.time()
    n, shape, exps, tests = search(n)
    ok = verify(n, exps) if exps else False
    return f"n={n} {shape} {list(exps)} verified={ok} tests={tests} secs={time.time()-t:.1f}"

if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    with Pool(32) as p:
        for line in p.imap(job, range(lo, hi + 1)):
            print(line, flush=True)
