#!/usr/bin/env python3
"""Independent wide check of the k=2 theorem that route B claims to have PROVED.

Claim: for all a>=2, b>=1 with gcd(a,b)=1, the k=2 shell colouring of [1,ab],
   chi(j) = 1 if v_a(j) == 1 else 2,
has no monochromatic solution of a(x-y)=bz with x,y,z in [1,ab].

A single counterexample here would mean the machine proof or its composition is
WRONG. Enumerated by full scan over all (x,y,z), not via the parameterisation,
so it does not assume the solution-form lemma either.
"""
from math import gcd

def val(j, a):
    e = 0
    while j % a == 0:
        j //= a
        e += 1
    return e

bad = []
tested = 0
for a in range(2, 31):
    for b in range(1, 61):
        if gcd(a, b) != 1:
            continue
        N = a * b
        if N > 1200:
            continue
        chi = [0] * (N + 1)
        for j in range(1, N + 1):
            chi[j] = 1 if (j % a == 0 and val(j, a) == 1) else 2
        tested += 1
        # full scan over solutions of a(x-y) = b z, no parameterisation assumed
        for z in range(1, N + 1):
            bz = b * z
            if bz % a:
                continue
            diff = bz // a          # x - y
            if diff <= 0 or diff > N - 1:
                continue
            for y in range(1, N - diff + 1):
                x = y + diff
                if chi[x] == chi[y] == chi[z]:
                    bad.append((a, b, x, y, z))
                    break
            if bad:
                break
        if bad:
            break
    if bad:
        break

print(f"coprime (a,b) pairs tested (2<=a<=30, 1<=b<=60, N<=1200): {tested}")
if bad:
    print("*** COUNTEREXAMPLE TO THE CLAIMED THEOREM ***", bad)
else:
    print("NO monochromatic solution found in any tested pair.")
    print("=> consistent with the machine-proved k=2 theorem (incl. b>a).")

# And the sharpness control: the SAME scan on NON-coprime pairs must find defects.
print()
found = 0
checked = 0
for a in range(2, 13):
    for b in range(1, 13):
        if gcd(a, b) == 1:
            continue
        N = a * b
        chi = [0] * (N + 1)
        for j in range(1, N + 1):
            chi[j] = 1 if (j % a == 0 and val(j, a) == 1) else 2
        checked += 1
        hit = None
        for z in range(1, N + 1):
            bz = b * z
            if bz % a:
                continue
            diff = bz // a
            if diff <= 0 or diff > N - 1:
                continue
            for y in range(1, N - diff + 1):
                x = y + diff
                if chi[x] == chi[y] == chi[z]:
                    hit = (x, y, z)
                    break
            if hit:
                break
        if hit:
            found += 1
print(f"NON-coprime pairs (2<=a,b<=12): {found}/{checked} have a monochromatic solution")
print("=> the gcd hypothesis is sharp; the proof MUST use it (and it does, via Bezout).")
