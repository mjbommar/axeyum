#!/usr/bin/env python3
"""Ground-truth enumeration for route B.

Establishes, by direct enumeration (no solver involved), the facts the symbolic
encodings will then be asked to prove:

  G1. The shell colouring's N and chi, re-derived from the brief, and
      solution-freeness at k=2 and k=3 for b<a, gcd(a,b)=1.
  G2. Whether gcd(a,b)=1 is actually NEEDED at k=2 and k=3 (the brief suggests
      checking rather than assuming).
  G3. The b=a+1 counterexample family at k=3: verify (x,y,z)=(a b^2+1, 1, a^2 b)
      is in range, satisfies the equation, and is monochromatic -- and record
      the exact closed forms so the symbolic proof knows what to prove.
  G4. The k=2 case analysis: which conjuncts are actually needed.
"""
from math import gcd


def val(j, a):
    """a-adic valuation of j (largest e with a^e | j)."""
    if j == 0:
        return 10**9
    e = 0
    while j % a == 0:
        j //= a
        e += 1
    return e


def shell_N(a, b, k):
    L = {i: a ** (i - 1) * b for i in range(2, k + 1)}
    return 2 * sum(L[i] for i in range(2, k)) + L[k]


def shell_chi(a, b, k):
    """Returns (N, chi) with chi a dict j -> colour in 1..k, per the brief."""
    L = {i: a ** (i - 1) * b for i in range(2, k + 1)}
    N = 2 * sum(L[i] for i in range(2, k)) + L[k]
    c = {1: 0}
    for i in range(2, k):
        c[i] = c[i - 1] + L[i]
    chi = {}
    for j in range(1, N + 1):
        if j % a == 0:
            chi[j] = min(val(j, a), k)
        else:
            col = k
            for i in range(2, k):
                if (c[i - 1] + 1 <= j <= c[i]) or (N - c[i] + 1 <= j <= N - c[i - 1]):
                    col = i
                    break
            chi[j] = col
    return N, chi


def mono_solutions(a, b, k):
    """All monochromatic solutions of a(x-y)=bz in [1,N] under the shell chi.

    Uses the parameterisation x-y = b t, z = a t, t>=1 when gcd(a,b)=1; for the
    non-coprime probe it falls back to a full scan so the answer is honest.
    """
    N, chi = shell_chi(a, b, k)
    out = []
    if gcd(a, b) == 1:
        t = 1
        while a * t <= N:
            z = a * t
            for y in range(1, N + 1):
                x = y + b * t
                if x > N:
                    break
                if chi[x] == chi[y] == chi[z]:
                    out.append((x, y, z, t))
            t += 1
    else:
        for z in range(1, N + 1):
            for y in range(1, N + 1):
                num = b * z + a * y
                if num % a:
                    continue
                x = num // a
                if 1 <= x <= N and x != y and chi[x] == chi[y] == chi[z]:
                    out.append((x, y, z, None))
    return N, out


print("=" * 78)
print("G1/G2. Solution-freeness sweep. 'FREE' = no monochromatic solution.")
print("=" * 78)
print(f"{'a':>3} {'b':>3} {'k':>2} {'gcd':>4} {'N':>7} {'regime':>8}  result")
rows = []
for k in (2, 3):
    for a in range(2, 9):
        for b in range(1, 9):
            N = shell_N(a, b, k)
            if N > 4000:
                continue
            N, sols = mono_solutions(a, b, k)
            g = gcd(a, b)
            regime = "b<a" if b < a else ("b=a" if b == a else "b>a")
            res = "FREE" if not sols else f"DEFECT {sols[0][:3]}"
            rows.append((a, b, k, g, N, regime, res, len(sols)))
            print(f"{a:>3} {b:>3} {k:>2} {g:>4} {N:>7} {regime:>8}  {res}")

print()
print("=" * 78)
print("G2 summary: is gcd(a,b)=1 needed?")
print("=" * 78)
for k in (2, 3):
    for want_g1 in (True, False):
        sel = [r for r in rows if r[2] == k and r[5] == "b<a" and ((r[3] == 1) == want_g1)]
        free = [r for r in sel if r[7] == 0]
        bad = [r for r in sel if r[7] > 0]
        tag = "gcd=1" if want_g1 else "gcd>1"
        print(f"  k={k} b<a {tag}: {len(free)}/{len(sel)} solution-free"
              + (f"   DEFECTS: {[(r[0], r[1]) for r in bad]}" if bad else ""))

print()
print("=" * 78)
print("G3. b=a+1, k=3 counterexample family: closed form check")
print("=" * 78)
print(f"{'a':>3} {'b':>3} {'N':>7} {'x=ab^2+1':>10} {'z=a^2 b':>9} "
      f"{'chi(x)':>7} {'chi(1)':>7} {'chi(z)':>7} {'N-ab+1':>8} {'in range':>9}")
for a in range(2, 12):
    b = a + 1
    k = 3
    N, chi = shell_chi(a, b, k)
    x, y, z = a * b * b + 1, 1, a * a * b
    ok_eq = a * (x - y) == b * z
    inr = 1 <= x <= N and 1 <= z <= N
    cx = chi.get(x)
    cy = chi.get(y)
    cz = chi.get(z)
    print(f"{a:>3} {b:>3} {N:>7} {x:>10} {z:>9} {str(cx):>7} {str(cy):>7} "
          f"{str(cz):>7} {N - a*b + 1:>8} {str(inr):>9}   eq={ok_eq} "
          f"mono={cx == cy == cz}  x==N-ab+1? {x == N - a*b + 1}")

print()
print("  closed forms with b=a+1, k=3:")
print("    N        = 2ab + a^2 b = a(a+1)(a+2) = a^3+3a^2+2a")
print("    x        = a b^2 + 1   = a(a+1)^2+1  = a^3+2a^2+a+1")
print("    N-ab+1   = a^3+3a^2+2a - a^2-a + 1   = a^3+2a^2+a+1   == x   <-- x is")
print("               EXACTLY the left endpoint of the right-hand shell")
for a in range(2, 12):
    b = a + 1
    assert a * b * b + 1 == a**3 + 2 * a**2 + a + 1
    assert shell_N(a, b, 3) == a**3 + 3 * a**2 + 2 * a
    assert shell_N(a, b, 3) - a * b + 1 == a**3 + 2 * a**2 + a + 1
print("    (asserted for a=2..11: all three closed forms exact)")

print()
print("=" * 78)
print("G4. k=2 case analysis -- which conjuncts does the refutation need?")
print("=" * 78)
print("""
  k=2:  L_2 = a*b,  N = a*b,  no shell strata (range 2..k-1 empty).
        chi(j) = 1  iff  a | j  and  a^2 does not divide j     (v(j)=1)
        chi(j) = 2  otherwise                     (units, and v(j)>=2)

  A monochromatic solution needs y>=1, t>=1, x=y+bt<=N, z=at<=N.
  z = a*t <= a*b  and a>0  =>  t <= b.  With b < a:  1 <= t <= b < a.

  CASE 2 (all colour 2). The z-conjunct is  NOT(a|z AND a^2 not| z).
        a|z holds (z=at), so it forces a^2 | z, i.e. t = a*q for some q.
        1 <= t = a*q and a >= 2  =>  q >= 1  =>  t = a*q >= a > b >= t.
        CONTRADICTION using ONLY the z-conjunct.  Purely existential.

  CASE 1 (all colour 1). Needs a|x, a|y (drop the a^2-nondivisibility
        conjuncts: dropping them WEAKENS the hypothesis, so refuting the
        weaker version proves more).
        a|x and a|y => a | (x-y) = b t.  gcd(a,b)=1 (Bezout au+bv=1)
        => t = t(au+bv) = a(tu) + v(bt) => a | t => t = a*w, and
        1 <= a*w <= b < a  =>  0 < w < 1.  CONTRADICTION.
        gcd IS used here, via Bezout, which is EXISTENTIAL -- so it can be
        added as two extra free variables u,v in the refutation query.
""")
# sanity: confirm the case analysis by brute force at k=2
print("  brute-force cross-check of the k=2 case analysis:")
for a in range(2, 10):
    for b in range(1, a):
        if gcd(a, b) != 1:
            continue
        N, chi = shell_chi(a, b, 2)
        # all solutions, recording which case each mono-candidate would fall in
        seen = []
        t = 1
        while a * t <= N:
            for y in range(1, N + 1):
                x = y + b * t
                if x > N:
                    break
                if chi[x] == chi[y] == chi[a * t]:
                    seen.append((x, y, a * t))
            t += 1
        assert not seen, (a, b, seen)
print("    k=2, all coprime b<a with 2<=a<=9: NO monochromatic solution. OK")
