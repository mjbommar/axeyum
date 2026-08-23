#!/usr/bin/env python3
"""Angle 4b: the L-function route to the horizontal conductor sums A_r(n,j),
and the G_m-quotient reduction of note 14.

For q = 2^r, E_j = (1 + x F_q[x])/x^{j+1}, and a character chi of E_j, the
completely multiplicative function F -> chi(<F>_j) on monic polynomials has

    L(chi,T) = sum_{m=0}^{j-1} c_m(chi) T^m,   c_m(chi) = sum_{v in V_m} chi(v),

with V_m = {1 + b_1 x + ... + b_m x^m} the (injective, m < j) image of the monic
degree-m polynomials under F -> <F>_j.  Newton's identities on e_k = (-1)^k c_k
give S_n(chi) = -p_n, and

    A_r(n,j) = sum_{chi of exact conductor j} S_n(chi)
             = q^j N_j(1) - q^{j-1} N_{j-1}(1),

the quantity `axeyum-lemire-horizontal` computes by window enumeration at cost
q^{n-j+1}.  This route costs ~ j q^j log q and is INDEPENDENT OF n.

Group structure used (note 14, Prop. A; proved here by control C1): with
h_{k,l} = 1 + z^l x^k (z a generator of F_q^*, k odd <= j, 0 <= l < r),

    E_j = prod_{k odd <= j} prod_{l<r} <h_{k,l}>,   ord(h_{k,l}) = 2^{e_k},
    e_k = floor(log2(j/k)) + 1,   sum_{k odd <= j} e_k = j,

because (1 + a x^k)^2 = 1 + a^2 x^{2k} in characteristic two.  A character has
exact conductor j iff some exponent in the block k0 = odd part of j is odd, so
#Prim_j(F_q) = q^{j-1}(q-1).  exponent(E_j) = 2^{floor(log2 j)+1}, so for j <= 7
every character value is an 8th root of unity and EVERYTHING below is exact in
Z[zeta_8] = Z[T]/(T^4+1).

This script is the independent (pure Python) cross-check of the Rust bulk engine
`axeyum-lemire-lfunc` (mirrored as axeyum-lemire-lfunc.rs.txt).  It exits
NONZERO if any control fails.

Usage:
    python lemire_horizontal_quotient.py                 # all controls
    python lemire_horizontal_quotient.py --dumps DIR     # + cross-check Rust dumps
    python lemire_horizontal_quotient.py --report OUT    # + write the weight table
    python lemire_horizontal_quotient.py --mutate K      # must exit nonzero
"""

from __future__ import annotations

import argparse
import glob
import itertools
import math
import os
import re
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
GRID = os.path.join(HERE, "data", "horizontal-grid.txt")

MUT = 0  # mutation id, set by --mutate; 0 = pristine


class ControlFailure(Exception):
    def __init__(self, name, msg):
        super().__init__(f"control {name}: {msg}")
        self.name = name


def require(cond, name, msg):
    if not cond:
        raise ControlFailure(name, msg)


# --------------------------------------------------------------------------
# F_{2^r}
# --------------------------------------------------------------------------
PRIMITIVE = {
    1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101, 6: 0b1000011,
    7: 0b10000011, 8: 0b100011101, 9: 0b1000010001,
}
AES = 0b100011101 ^ 0b100011101 | 0b100011011  # x^8+x^4+x^3+x+1: irreducible, NOT primitive


class GF:
    def __init__(self, r, modulus=None):
        self.r = r
        self.q = 1 << r
        self.mod = modulus if modulus is not None else PRIMITIVE[r]
        if MUT == 5 and r == 8:
            self.mod = AES
        q = self.q
        exp = [0] * (2 * q)
        log = [0] * q
        a = 1
        for i in range(q - 1):
            exp[i] = a
            log[a] = i
            a <<= 1
            if a & q:
                a ^= self.mod
        # C0: the modulus must be PRIMITIVE, not merely irreducible.  assert(a==1)
        # after q-1 steps does NOT detect the AES polynomial (ord(x) = 51): the
        # log table is then mostly zero and every product is wrong (note 12, C5).
        require(a == 1, "C0", f"modulus {bin(self.mod)} does not close the cycle")
        require(sorted(exp[:q - 1]) == list(range(1, q)), "C0",
                f"modulus {bin(self.mod)} is irreducible but NOT primitive "
                f"(log table is not a bijection onto F_q^*)")
        for i in range(q - 1, 2 * q):
            exp[i] = exp[i - (q - 1)]
        self.exp, self.log = exp, log

    def mul(self, a, b):
        return 0 if (a == 0 or b == 0) else self.exp[self.log[a] + self.log[b]]

    def pow(self, a, e):
        return 0 if a == 0 else self.exp[(self.log[a] * e) % (self.q - 1)]


# --------------------------------------------------------------------------
# Z[zeta_8] = Z[T]/(T^4+1)
# --------------------------------------------------------------------------
def cy_add(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3])


def cy_sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3])


def cy_scal(a, s):
    return (a[0] * s, a[1] * s, a[2] * s, a[3] * s)


def cy_mul(a, b):
    c = [0] * 7
    for i in range(4):
        if a[i]:
            ai = a[i]
            for k in range(4):
                c[i + k] += ai * b[k]
    return (c[0] - c[4], c[1] - c[5], c[2] - c[6], c[3])


def cy_zeta(e):
    e %= 8
    s = 1
    if e >= 4:
        e -= 4
        s = -1
    v = [0, 0, 0, 0]
    v[e] = s
    return tuple(v)


def cy_mul_zeta(a, e):
    e %= 8
    s = 1
    if e >= 4:
        e -= 4
        s = -1
    out = [0, 0, 0, 0]
    for i in range(4):
        k = i + e
        if k >= 4:
            out[k - 4] = -s * a[i]
        else:
            out[k] = s * a[i]
    return tuple(out)


def cy_conj(a):
    return (a[0], -a[3], -a[2], -a[1])


def cy_isint(a):
    return a[1] == 0 and a[2] == 0 and a[3] == 0


# --------------------------------------------------------------------------
# E_j
# --------------------------------------------------------------------------
def ek(j, k):
    e, t = 0, k
    while t <= j:
        e += 1
        t *= 2
    if MUT == 1:
        return max(1, e - 1)
    return e


class Ej:
    """E_j with the explicit basis h_{k,l} = 1 + z^l x^k and a discrete log."""

    def __init__(self, j, F: GF):
        self.j, self.F = j, F
        self.odd = [k for k in range(1, j + 1) if k % 2 == 1]
        self.e = {k: ek(j, k) for k in self.odd}
        require(sum(self.e.values()) == j, "C1",
                f"sum of e_k = {sum(self.e.values())} != j = {j}")
        require(max(self.e.values()) <= 3, "C1", "need exponent(E_j) <= 8, i.e. j <= 7")
        self.gens = [(k, l) for k in self.odd for l in range(F.r)]
        self.radix = [1 << self.e[k] for (k, _l) in self.gens]
        self.N = len(self.gens)
        self.stride, s = [], 1
        for R in self.radix:
            self.stride.append(s)
            s *= R
        self.size = s
        require(s == F.q ** j, "C1", f"index space {s} != |E_j| = {F.q ** j}")
        self.weight = [1 << (3 - self.e[k]) for (k, _l) in self.gens]
        if MUT == 2:
            self.weight = [w * 2 for w in self.weight]
        self.gidx = {g: i for i, g in enumerate(self.gens)}
        self.solve = {}
        for i in range(max(self.e.values())):
            cols = [F.pow(F.exp[l], 1 << i) for l in range(F.r)]
            self.solve[i] = _invert_bitmatrix(cols, F.r)
        # k0 = odd part of j: exact conductor j  <=>  some exponent there is odd
        k0 = j
        while k0 % 2 == 0:
            k0 //= 2
        self.k0 = k0

    def mul(self, u, v):
        j, F = self.j, self.F
        uu, vv = (1,) + tuple(u), (1,) + tuple(v)
        out = [0] * (j + 1)
        for a in range(j + 1):
            if uu[a]:
                for b in range(j + 1 - a):
                    if vv[b]:
                        out[a + b] ^= F.mul(uu[a], vv[b])
        return tuple(out[1:])

    def power(self, u, e):
        res = (0,) * self.j
        base = tuple(u)
        while e:
            if e & 1:
                res = self.mul(res, base)
            base = self.mul(base, base)
            e >>= 1
        return res

    def dlog(self, u):
        j, F = self.j, self.F
        g = [1] + list(u)
        exps = [0] * self.N
        for m in range(1, j + 1):
            i = (m & -m).bit_length() - 1
            k = m >> i
            c = g[m]
            if c:
                bits = 0
                v = c
                while v:
                    t = (v & -v).bit_length() - 1
                    bits ^= self.solve[i][t]
                    v &= v - 1
                for l in range(F.r):
                    if not (bits >> l) & 1:
                        continue
                    exps[self.gidx[(k, l)]] += 1 << i
                    a = F.pow(F.exp[l], 1 << i)
                    for d in range(m, j + 1):
                        g[d] ^= F.mul(a, g[d - m])
            require(g[m] == 0, "C1", f"dlog failed to clear x^{m}")
        for gi, (k, _l) in enumerate(self.gens):
            require(0 <= exps[gi] < (1 << self.e[k]), "C1", "exponent out of range")
        return exps

    def index(self, exps):
        return sum(exps[i] * self.stride[i] for i in range(self.N))


def _invert_bitmatrix(cols, r):
    basis = [(0, 0)] * 64
    for l in range(r):
        v, c = cols[l], 1 << l
        while True:
            require(v != 0, "C1", "generator columns are dependent")
            p = v.bit_length() - 1
            if basis[p][0] == 0:
                basis[p] = (v, c)
                break
            v ^= basis[p][0]
            c ^= basis[p][1]

    def solve(target):
        v, out = target, 0
        while v:
            p = v.bit_length() - 1
            require(basis[p][0] != 0, "C1", "target not in span")
            v ^= basis[p][0]
            out ^= basis[p][1]
        return out

    return [solve(1 << t) for t in range(r)]


def V_elements(j, F):
    for tup in itertools.product(range(F.q), repeat=j - 1):
        b = list(tup) + [0]
        d = 0
        for i in range(j - 1):
            if b[i]:
                d = i + 1
        yield tuple(b), d


# --------------------------------------------------------------------------
# c_m(chi) for all chi, by the fast transform over E_j
# --------------------------------------------------------------------------
def all_cm(j, F):
    G = Ej(j, F)
    size = G.size
    arr = [[(0, 0, 0, 0)] * size for _ in range(j)]
    for g, dg in V_elements(j, F):
        idx = G.index(G.dlog(g))
        arr[dg][idx] = cy_add(arr[dg][idx], (1, 0, 0, 0))
    for m in range(j):
        A = arr[m]
        for gi in range(G.N):
            R, st, w = G.radix[gi], G.stride[gi], G.weight[gi]
            block = st * R
            for base in range(0, size, block):
                for off in range(st):
                    src = [A[base + off + t * st] for t in range(R)]
                    for v in range(R):
                        acc = (0, 0, 0, 0)
                        for t in range(R):
                            acc = cy_add(acc, cy_mul_zeta(src[t], v * t * w))
                        A[base + off + v * st] = acc
    return G, arr


def power_sums(cm, nmax):
    d = len(cm) - 1
    e = [cy_scal(cm[k], (-1) ** k) for k in range(d + 1)]
    if MUT == 4:
        e = [cy_scal(cm[k], 1) for k in range(d + 1)]  # drop the (-1)^k in e_k = (-1)^k c_k
    p = [(0, 0, 0, 0)] * (nmax + 1)
    for n in range(1, nmax + 1):
        acc = (0, 0, 0, 0)
        for i in range(1, min(n - 1, d) + 1):
            t = cy_mul(e[i], p[n - i])
            acc = cy_add(acc, t) if i % 2 == 1 else cy_sub(acc, t)
        if n <= d:
            t = cy_scal(e[n], n)
            acc = cy_add(acc, t) if n % 2 == 1 else cy_sub(acc, t)
        p[n] = acc
    return [cy_scal(p[n], -1) for n in range(1, nmax + 1)]


def A_table(j, r, nmax, purity=True):
    """A_r(n,j) for n = 1..nmax, plus the exact-conductor count."""
    F = GF(r)
    q = F.q
    G, arr = all_cm(j, F)
    d = j - 1
    prim = [i for i, (k, _l) in enumerate(G.gens) if k == G.k0]
    A = [(0, 0, 0, 0)] * nmax

    def is_exact(vv):
        if MUT == 3:
            return True  # drop the exact-conductor filter
        return any(vv[i] % 2 == 1 for i in prim)

    chars = [vv for vv in itertools.product(*[range(R) for R in G.radix]) if is_exact(vv)]
    npr = len(chars)
    require(npr == q ** (j - 1) * (q - 1), "C8",
            f"#Prim_{j}(F_{q}) = {npr} != q^{{j-1}}(q-1) = {q ** (j - 1) * (q - 1)} "
            f"(the exact-conductor-j test is 'some exponent in the k0 = {G.k0} block is odd')")
    for vv in chars:
        idx = G.index(list(vv))
        cm, acc = [], (0, 0, 0, 0)
        for m in range(j):
            acc = cy_add(acc, arr[m][idx])
            cm.append(acc)
        if purity:
            # C2: Weil.  |c_{j-1}|^2 = q^{j-1} (deg L = j-1, all |alpha_i| = sqrt q)
            # and the functional equation conj(c_m) c_{j-1} = q^m c_{j-1-m}.
            nm = cy_mul(cm[d], cy_conj(cm[d]))
            require(cy_isint(nm) and nm[0] == q ** d, "C2",
                    f"|c_{{j-1}}(chi)|^2 = {nm} != q^{d} = {q ** d} at chi = {vv} (j={j}, r={r})")
            for m in range(d + 1):
                lhs = cy_mul(cy_conj(cm[m]), cm[d])
                rhs = cy_scal(cm[d - m], q ** m)
                require(lhs == rhs, "C2",
                        f"functional equation fails at chi = {vv}, m = {m} (j={j}, r={r})")
        for n, s in enumerate(power_sums(cm, nmax)):
            A[n] = cy_add(A[n], s)
    # C3 / C4: A_r is a rational integer and (q-1) | A_r
    out = []
    for n in range(nmax):
        require(cy_isint(A[n]), "C3",
                f"A_{r}({n + 1},{j}) = {A[n]} is not a rational integer")
        v = A[n][0]
        require(v % (q - 1) == 0, "C4",
                f"(q-1) = {q - 1} does not divide A_{r}({n + 1},{j}) = {v}")
        out.append(v)
    return out, npr


# --------------------------------------------------------------------------
# controls
# --------------------------------------------------------------------------
def read_grid(path):
    ref = {}
    if not os.path.exists(path):
        return ref
    for block in re.split(r"^### ", open(path).read(), flags=re.M)[1:]:
        lines = block.strip().split("\n")
        meta = dict(kv.split("=") for kv in lines[1].split("|")[1:])
        n, r = int(meta["n"]), int(meta["r"])
        for line in lines[2:]:
            p = line.split("|")
            if p[0] == "A":
                ref[(n, int(p[1]), r)] = int(p[2])
    return ref


def read_dumps(dumpdir, pattern="j*-r*.txt"):
    cells = {}
    for f in sorted(glob.glob(os.path.join(dumpdir, pattern))):
        meta, A, MOM, ORD, ordinf = {}, {}, {}, {}, None
        for line in open(f):
            p = line.strip().split("|")
            if p[0] == "META":
                meta = dict(kv.split("=") for kv in p[1:])
            elif p[0] == "A":
                A[int(p[1])] = int(p[2])
            elif p[0] == "MOM":
                MOM[(int(p[1]), int(p[2]))] = [int(x) for x in p[3:7]]
            elif p[0] == "ORD":
                ORD[int(p[1])] = int(p[2])
            elif p[0] == "ORDINF":
                ordinf = int(p[1])
        if meta:
            cells[(int(meta["j"]), int(meta["r"]))] = dict(
                meta=meta, A=A, MOM=MOM, ORD=ORD, ordinf=ordinf)
    return cells


def control_structure():
    """C1: the basis h_{k,l} = 1 + z^l x^k really is a basis of E_j."""
    for j in range(2, 8):
        for r in (1, 2, 3):
            if j * r > 12:
                continue
            F = GF(r)
            G = Ej(j, F)
            for (k, l) in G.gens:
                h = [0] * j
                h[k - 1] = F.exp[l]
                h = tuple(h)
                o = 1 << G.e[k]
                require(G.power(h, o) == (0,) * j, "C1",
                        f"ord(1 + z^{l} x^{k}) does not divide 2^{G.e[k]} (j={j}, r={r})")
                require(G.power(h, o // 2) != (0,) * j, "C1",
                        f"ord(1 + z^{l} x^{k}) is smaller than 2^{G.e[k]} (j={j}, r={r})")
            # the discrete log is a bijection E_j -> prod Z/2^{e_k}
            seen = set()
            for tup in itertools.product(range(F.q), repeat=j):
                seen.add(G.index(G.dlog(tup)))
            require(len(seen) == G.size, "C1",
                    f"dlog is not a bijection (j={j}, r={r}): {len(seen)} of {G.size}")


def control_freeness():
    """C9: the G_m-action on Prim_j(F_q) is free iff gcd(j, q-1) = 1.

    sigma_t scales the m-th big-Witt coordinate by t^m, so #{g in E_j :
    sigma_t g = g} = q^{#{m <= j : t^m = 1}}, and a fixed character has exact
    conductor j iff ord(t) divides j.  Note 12 said "j | q-1"; the correct
    condition is gcd(j, q-1) > 1.
    """
    for j in range(2, 8):
        for r in (1, 2, 3, 4):
            if j * r > 12:
                continue
            F = GF(r)
            G = Ej(j, F)
            jodd = j
            while jodd % 2 == 0:
                jodd //= 2
            expect_free = math.gcd(jodd, F.q - 1) == 1
            if MUT == 6:
                expect_free = (F.q - 1) % j != 0   # note 12's criterion "j | q-1"
            # direct: count exact-conductor-j characters with a nontrivial stabiliser
            prim = [i for i, (k, _l) in enumerate(G.gens) if k == G.k0]
            W = G.weight
            stab = 0
            chars = list(itertools.product(*[range(R) for R in G.radix]))
            # sigma_t on E_j: (b_1..b_j) -> (t b_1, t^2 b_2, ...)
            for t in range(1, F.q):
                if t == 1:
                    continue
                perm = {}
                for tup in itertools.product(range(F.q), repeat=j):
                    im = tuple(F.mul(F.pow(t, m + 1), tup[m]) for m in range(j))
                    perm[G.index(G.dlog(tup))] = G.index(G.dlog(im))
                for vv in chars:
                    if not any(vv[i] % 2 == 1 for i in prim):
                        continue
                    # chi_vv fixed by sigma_t  <=>  chi_vv(sigma_t g) = chi_vv(g) for all g
                    ok = True
                    for tup in itertools.product(range(F.q), repeat=j):
                        a = G.dlog(tup)
                        b = G.dlog(tuple(F.mul(F.pow(t, m + 1), tup[m]) for m in range(j)))
                        ea = sum(vv[i] * a[i] * W[i] for i in range(G.N)) % 8
                        eb = sum(vv[i] * b[i] * W[i] for i in range(G.N)) % 8
                        if ea != eb:
                            ok = False
                            break
                    if ok:
                        stab += 1
                if stab:
                    break
            require((stab == 0) == expect_free, "C9",
                    f"freeness mismatch at j={j}, r={r}: gcd({jodd},{F.q - 1})="
                    f"{math.gcd(jodd, F.q - 1)} predicts free={expect_free} "
                    f"but {stab} stabilised exact-conductor characters were found")


def closed_form_checks(table):
    """C7: reproduce the note-12 closed forms."""
    def A(j, r, n):
        return table[(j, r)][n - 1]

    for r in range(1, 5):
        q = 1 << r
        for n in range(1, 13):
            v = A(2, r, n)
            if n % 4 == 2:
                require(v == 0, "C7", f"Prop.3: A_{r}({n},2) = {v} != 0 for n = 2 mod 4")
            elif n % 2 == 1:
                require(abs(v) == q ** ((n + 3) // 2) - q ** ((n + 1) // 2), "C7",
                        f"Prop.3: |A_{r}({n},2)| = {abs(v)} != q^{(n + 3) // 2} - q^{(n + 1) // 2}")
            else:
                require(abs(v) == q ** ((n + 4) // 2) - q ** ((n + 2) // 2), "C7",
                        f"Prop.3: |A_{r}({n},2)| = {abs(v)} != q^{(n + 4) // 2} - q^{(n + 2) // 2}")
        # note 12: A_r(7,3) = 64^r - 32^r exactly
        require(A(3, r, 7) == 64 ** r - 32 ** r, "C7",
                f"A_{r}(7,3) = {A(3, r, 7)} != 64^{r} - 32^{r}")
        # note 12: N_3(1) = q^{n-3} on the nose at n = 9, so A_r(9,3) = -(q-1) q^5
        require(A(3, r, 9) == -(q - 1) * q ** 5, "C7",
                f"A_{r}(9,3) = {A(3, r, 9)} != -(q-1) q^5")
        # note 12: A_r(7,4) = -(q-1) q^4 (q+1) for 3 nmid r, +(q-1) q^4 (2q-1) for 3 | r
        want = (q - 1) * q ** 4 * (2 * q - 1) if r % 3 == 0 else -(q - 1) * q ** 4 * (q + 1)
        require(A(4, r, 7) == want, "C7", f"A_{r}(7,4) = {A(4, r, 7)} != {want}")


def run_controls(dumpdir=None, verbose=True):
    def say(*a):
        if verbose:
            print(*a)

    say("== C0 field primitivity, C1 group structure of E_j ==")
    control_structure()
    say("   C1 ok: h_{k,l} = 1 + z^l x^k has order 2^{e_k} and the dlog is a bijection")

    say("== C8 exact-conductor count, C2 Weil purity, C3 integrality, C4 (q-1) | A_r ==")
    table = {}
    cells = [(j, r) for j in range(2, 8) for r in range(1, 9) if 2 <= j * r <= 16]
    for (j, r) in cells:
        nmax = max(14, 2 * j + 2)
        A, _npr = A_table(j, r, nmax)
        table[(j, r)] = A
    say(f"   ok on {len(cells)} cells (j,r): {cells}")

    say("== C5 agreement with the note-12 window-scan grid (independent algorithm) ==")
    ref = read_grid(GRID)
    require(len(ref) > 0, "C5", f"no reference grid at {GRID}")
    hits = 0
    for (n, j, r), v in sorted(ref.items()):
        if (j, r) in table and n <= len(table[(j, r)]):
            require(table[(j, r)][n - 1] == v, "C5",
                    f"L-function route gives A_{r}({n},{j}) = {table[(j, r)][n - 1]}, "
                    f"window scan gives {v}")
            hits += 1
    require(hits >= 100, "C5", f"only {hits} overlapping cells checked")
    say(f"   C5 ok on {hits} overlapping (n,j,r) cells")

    say("== C7 note-12 closed forms (j = 2 family; (7,3); (9,3); (7,4)) ==")
    closed_form_checks(table)
    say("   C7 ok")

    say("== C9 freeness of the G_m-action <=> gcd(j, q-1) = 1 ==")
    control_freeness()
    say("   C9 ok")

    if dumpdir:
        say("== C6 agreement with the Rust bulk engine axeyum-lemire-lfunc ==")
        cs = read_dumps(dumpdir)
        require(len(cs) > 0, "C6", f"no dumps in {dumpdir}")
        hits = 0
        for (j, r), d in sorted(cs.items()):
            if (j, r) not in table:
                continue
            for n, v in d["A"].items():
                if n <= len(table[(j, r)]):
                    require(table[(j, r)][n - 1] == v, "C6",
                            f"python gives A_{r}({n},{j}) = {table[(j, r)][n - 1]}, "
                            f"rust gives {v}")
                    hits += 1
        require(hits >= 50, "C6", f"only {hits} overlapping cells checked ({len(cs)} dumps)")
        say(f"   C6 ok on {hits} overlapping (n,j,r) cells from {len(cs)} dumps")
    return table


# --------------------------------------------------------------------------
# analysis: closed forms and the delta table
# --------------------------------------------------------------------------
def v2(x):
    x = abs(x)
    n = 0
    while x and x % 2 == 0:
        x //= 2
        n += 1
    return n


def solve_exact(rows, rhs):
    m, n = len(rows), len(rows[0])
    M = [[Fraction(x) for x in rows[i]] + [Fraction(rhs[i])] for i in range(m)]
    piv, r0 = [], 0
    for c in range(n):
        p = next((i for i in range(r0, m) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r0], M[p] = M[p], M[r0]
        inv = M[r0][c]
        M[r0] = [x / inv for x in M[r0]]
        for i in range(m):
            if i != r0 and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r0])]
        piv.append(c)
        r0 += 1
        if r0 == m:
            break
    if len(piv) < n:
        return None
    sol = [Fraction(0)] * n
    for i, c in enumerate(piv):
        sol[c] = M[i][n]
    for i in range(len(piv), m):
        if M[i][n] != 0:
            return None
    return sol


def closed_form(seq, rs, n, minspare=1):
    """A_r = (q-1) q^k sum_{i<=D} a_i(r mod m) q^i with integer a_i; k read off
    the exact 2-adic ladder v2(A_r/(q-1)) = k r + c.  Verified on >= minspare
    points beyond the m(D+1) used to solve."""
    if all(x == 0 for x in seq):
        return dict(kind="zero", delta=None)
    if any(x == 0 for x in seq):
        return None
    qs = [2 ** r for r in rs]
    B = []
    for a, q in zip(seq, qs):
        if a % (q - 1):
            return None
        B.append(a // (q - 1))
    t = [v2(b) for b in B]
    ds = [t[i + 1] - t[i] for i in range(len(t) - 1)]
    tail = ds[1:] if len(ds) > 2 else ds
    if len(set(tail)) != 1 or tail[0] < 0:
        return None
    k = tail[0]
    C = []
    for b, q in zip(B, qs):
        if b % q ** k:
            return None
        C.append(b // q ** k)
    for m in (1, 2, 3, 4, 6):
        for D in range(0, 8):
            npar = m * (D + 1)
            if len(rs) < npar + minspare:
                continue
            rows, rhs = [], []
            for r, q, cc in zip(rs, qs, C):
                row = [0] * npar
                for i in range(D + 1):
                    row[(r % m) * (D + 1) + i] = q ** i
                rows.append(row)
                rhs.append(cc)
            sol = solve_exact(rows[:npar], rhs[:npar])
            if sol is None or any(x.denominator != 1 for x in sol):
                continue
            if not all(sum(rows[u][i] * sol[i] for i in range(npar)) == rhs[u]
                       for u in range(len(rs))):
                continue
            deg = max((i for c in range(m) for i in range(D + 1)
                       if sol[c * (D + 1) + i] != 0), default=0)
            return dict(kind="poly", m=m, D=D, k=k, coeffs=[int(x) for x in sol],
                        delta=2 * (k + deg + 1) - n, modes=sum(1 for x in sol if x != 0),
                        spare=len(rs) - npar)
    return None


def delta_estimates(seq, rs, n):
    good = [(r, math.log2(abs(a))) for r, a in zip(rs, seq) if a]
    if len(good) < 3:
        return None, None
    def reg(pts):
        k = len(pts)
        sx = sum(p[0] for p in pts); sy = sum(p[1] for p in pts)
        sxx = sum(p[0] ** 2 for p in pts); sxy = sum(p[0] * p[1] for p in pts)
        return (k * sxy - sx * sy) / (k * sxx - sx * sx)
    return 2 * reg(good[-4:]) - n, 2 * reg(good[-3:]) - n


def write_report(dumpdir, out):
    cs = read_dumps(dumpdir)
    lines = []
    w = lines.append
    w("== A_r(n,j) by the L-function route (engine axeyum-lemire-lfunc) ==")
    w("   delta(n,j) = (top Frobenius weight) - n.  Deligne + the trivial bound give")
    w("   (HWO-agg) only if  delta <= 2j - 2 log2(8 ell C/(j-1)),  which in the (HWO)")
    w("   range a <= j <= ell (so ell/(j-1) -> 1) is  delta <= 2j - 6.14 - 2 log2 C.")
    w("   CLOSED = exact fit A_r = (q-1) q^k P_{r mod m}(q) verified on spare points.")
    w("")
    for j in range(2, 8):
        rs = sorted(r for (jj, r) in cs if jj == j)
        if not rs:
            continue
        nmax = min(max(cs[(j, r)]["A"]) for r in rs)
        w(f"-- j = {j}   r = {rs}   j+1={j + 1}  2j-2={2 * j - 2}  2j-1={2 * j - 1}  2j={2 * j}")
        w("     n  crit  delta(closed form / regression)          form")
        for n in range(1, nmax + 1):
            seq = [cs[(j, r)]["A"][n] for r in rs]
            crit = "*" if n in (2 * j + 1, 2 * j + 2) else " "
            f = closed_form(seq, rs, n)
            d4, d3 = delta_estimates(seq, rs, n)
            if f and f["kind"] == "zero":
                w(f"    {n:2d}   {crit}   A == 0 identically")
            elif f:
                w(f"    {n:2d}   {crit}   delta = {f['delta']:3d}  (exact)"
                  f"                     m={f['m']} k={f['k']} D={f['D']} "
                  f"modes={f['modes']} spare={f['spare']} a={f['coeffs']}")
            else:
                s4 = "  n/a " if d4 is None else f"{d4:6.2f}"
                s3 = "  n/a " if d3 is None else f"{d3:6.2f}"
                w(f"    {n:2d}   {crit}   delta ~ {s4} (last 4 r), {s3} (last 3 r)   unresolved")
        w("")
    w("== Sato-Tate moments of tr = -S_1(chi) = -c_1(chi), normalised by sqrt q ==")
    w("   Haar on U(N), N = j-1:  E[tr] = 0, E[tr^2] = 0, E|tr|^2 = 1, E|tr|^4 = 2,")
    w("   E|tr|^6 = 6 (N >= 3; 5 for N = 2, 1 for N = 1).")
    w("    j  r      N   M10      M11      M20      M22      M33")
    for (j, r) in sorted(cs):
        d = cs[(j, r)]
        q = int(d["meta"]["q"]); npr = int(d["meta"]["nprim"])
        vals = []
        for (a, b) in [(1, 0), (1, 1), (2, 0), (2, 2), (3, 3)]:
            v = d["MOM"][(a, b)]
            vals.append(v[0] / (npr * q ** ((a + b) / 2)) if cy_isint(tuple(v)) else float("nan"))
        w("   %2d %2d   %4d  %s" % (j, r, j - 1, " ".join("%8.5f" % x for x in vals)))
    w("")
    w("== Frobenius torsion: fraction of chi in Prim_j(F_q) whose normalised")
    w("   eigenvalues alpha_i/sqrt q are roots of unity of order <= NORD ==")
    w("   (exact test: p_{n0}(chi) = (j-1) q^{n0/2} for some even n0 <= NORD)")
    w("    j  r   NORD   nprim        torsion fraction   orders seen")
    tors = {}
    for src in (cs, read_dumps(dumpdir, "ord-j*-r*.txt")):
        for (j, r), d in src.items():
            nord = int(d["meta"].get("nord", 0))
            if not nord:
                continue
            if (j, r) not in tors or nord > tors[(j, r)][0]:
                tors[(j, r)] = (nord, int(d["meta"]["nprim"]), sum(d["ORD"].values()),
                                sorted(d["ORD"]))
    for (j, r) in sorted(tors):
        nord, npr, tot, orders = tors[(j, r)]
        w("   %2d %2d   %4d %11d   %16.6f   %s" %
          (j, r, nord, npr, tot / npr, "{" + ",".join(map(str, orders)) + "}"))
    open(out, "w").write("\n".join(lines) + "\n")
    return out


def main():
    global MUT
    ap = argparse.ArgumentParser()
    ap.add_argument("--dumps", default=None, help="directory of axeyum-lemire-lfunc dumps")
    ap.add_argument("--report", default=None, help="write the weight/monodromy table here")
    ap.add_argument("--mutate", type=int, default=0,
                    help="1 e_k off by one; 2 wrong character weight; 3 no conductor "
                         "filter; 4 drop the (-1)^k in e_k; 5 non-primitive modulus; "
                         "6 note-12 freeness criterion 'j | q-1'")
    a = ap.parse_args()
    MUT = a.mutate
    try:
        run_controls(dumpdir=a.dumps)
    except ControlFailure as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    if a.mutate:
        print(f"FAIL: mutation {a.mutate} was not caught by any control", file=sys.stderr)
        return 1
    if a.report:
        if not a.dumps:
            print("FAIL: --report needs --dumps", file=sys.stderr)
            return 1
        print("wrote", write_report(a.dumps, a.report))
    print("ALL CONTROLS PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
