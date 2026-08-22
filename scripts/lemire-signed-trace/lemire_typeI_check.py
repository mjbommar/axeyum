"""Check the exact Type-I identity of note 02, section 2.1, at small parameters.

Phi(y) = sum_{deg r < h} Lambda(x^n + y + r) must equal C + sum_{deg e < j} deg(e) * M(I_{y,e})
with C independent of y, where I_{y,e} = {d : d e in x^n + y + I(h)} and M(I) = sum_{d in I} mu(d).
Exits nonzero if the difference Phi - RHS is not constant over the four shifts of the top layer.
"""
import sys
import flint
from lemire_anchor import pdeg


def _factor(F):
    n = pdeg(F)
    return flint.nmod_poly([(F >> i) & 1 for i in range(n + 1)], 2).factor()[1]


def lam(F):
    facs = _factor(F)
    if len(facs) == 1:
        return facs[0][0].degree()
    return 0


def mu(F):
    facs = _factor(F)
    if any(e > 1 for _, e in facs):
        return 0
    return (-1) ** len(facs)


def pdivmod(a, b):
    q = 0
    db = pdeg(b)
    while a and pdeg(a) >= db:
        s = pdeg(a) - db
        q |= 1 << s
        a ^= b << s
    return q, a


def check(n, j):
    h = n - j
    m = j.bit_length() - 1
    ys = [0, 1 << h, 1 << (n - 2 ** m), (1 << (n - 2 ** m)) | (1 << h)]

    def Phi(y):
        return sum(lam((1 << n) | y | r) for r in range(1 << h))

    def RHS(y):
        tot = 0
        for k in range(1, j):
            for e in range(1 << k, 1 << (k + 1)):
                ds = set()
                for r in range(1 << h):
                    q, rem = pdivmod((1 << n) | y | r, e)
                    if rem == 0:
                        ds.add(q)
                tot += k * sum(mu(d) for d in ds)
        return tot

    vals = [(Phi(y), RHS(y)) for y in ys]
    diffs = [p - r for p, r in vals]
    print(f"n={n} j={j}: Phi={[v[0] for v in vals]} RHS={[v[1] for v in vals]} Phi-RHS={diffs}")
    return len(set(diffs)) == 1


if __name__ == "__main__":
    ok = all(check(n, j) for (n, j) in [(11, 5), (13, 6), (15, 7)])
    print("TYPE-I IDENTITY", "OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)
