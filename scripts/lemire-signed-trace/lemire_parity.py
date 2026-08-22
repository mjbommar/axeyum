import sys, flint
from multiprocessing import Pool
def count_chunk(args):
    n, lo, hi = args
    half = n // 2
    c = 0
    for g in range(lo, hi):
        # f = x^n + g, deg g <= half, constant term must be 1 for irreducibility (n>1)
        if not (g & 1): continue
        coeffs = [(g >> i) & 1 for i in range(half + 1)] + [0] * (n - half - 1) + [1]
        _, facs = flint.nmod_poly(coeffs, 2).factor()
        if len(facs) == 1 and facs[0][1] == 1: c += 1
    return c
def I(n):
    half = n // 2
    total = 1 << (half + 1)
    procs = 32
    chunk = (total + 4*procs - 1) // (4*procs)
    tasks = [(n, lo, min(total, lo + chunk)) for lo in range(0, total, chunk)]
    with Pool(procs) as p:
        return sum(p.map(count_chunk, tasks))
if __name__ == "__main__":
    for n in range(2, int(sys.argv[1]) + 1):
        c = I(n)
        print(f"n={n:2d} floor(n/2)={n//2:2d} I_n(1)={c:8d} parity={'odd' if c%2 else 'even'} mod4={c%4} mod8={c%8} ratio_to_2^(n-ell)/n={c/(2**(n - (n+1)//2 + 1)/n):.3f}", flush=True)
