#!/usr/bin/env python3
"""Canonical CNF generator for the claim family rado-colouring-a(x-y)=bz.

Emits the formula F_n^k(E) for E: a(x-y) = bz — satisfiable iff there is a
k-colouring of [n] with no monochromatic solution to E, i.e. iff
R_k(E) > n.

This file is the generator of record named by claim.json formal.generator.
scripts/check-claim-certificates.py contains an INDEPENDENTLY WRITTEN encoder
and requires byte-identical output on every stored instance, so a divergence
between the two implementations is caught on every ledger re-check.

Encoding (documented in artifacts/claims/rado/SEMANTICS.md):
  variable v(j,i) = (j-1)*k + i   <=>  integer j has colour i
  1. positive clauses: each j in [n] has at least one colour
  2. negative clauses: for each solution {x,y,z} (distinct members, sorted),
     for each colour i: not all of them have colour i
     (solutions enumerated as x-y = b't, z = a't for t = 1, 2, ... with
      g = gcd(a,b), a' = a/g, b' = b/g; inner loop over y ascending)
  3. at-most-one-colour clauses per integer
  4. symmetry breaking: integer 1 has colour 1; integer j may take colour
     i > 1 only if some j' < j has colour i-1 (colour classes ordered by
     least element; sound because colour names are interchangeable)

usage: gen-rado-instance.py a b k n [outfile]
"""

from __future__ import annotations

import math
import sys


def generate(a: int, b: int, k: int, n: int) -> str:
    def var(j: int, i: int) -> int:
        return (j - 1) * k + i

    clauses: list[list[int]] = []
    for j in range(1, n + 1):
        clauses.append([var(j, i) for i in range(1, k + 1)])
    g = math.gcd(a, b)
    ap, bp = a // g, b // g
    t = 1
    while ap * t <= n and bp * t + 1 <= n:
        z, dx = ap * t, bp * t
        for y in range(1, n - dx + 1):
            trip = sorted({y + dx, y, z})
            for i in range(1, k + 1):
                clauses.append([-var(v, i) for v in trip])
        t += 1
    for j in range(1, n + 1):
        for i1 in range(1, k + 1):
            for i2 in range(i1 + 1, k + 1):
                clauses.append([-var(j, i1), -var(j, i2)])
    clauses.append([var(1, 1)])
    for j in range(2, n + 1):
        for i in range(2, k + 1):
            if j <= i - 1:
                clauses.append([-var(j, i)])
            else:
                clauses.append([-var(j, i)] + [var(jp, i - 1) for jp in range(1, j)])
    lines = [f"p cnf {n * k} {len(clauses)}\n"]
    lines.extend(" ".join(map(str, cl)) + " 0\n" for cl in clauses)
    return "".join(lines)


def main() -> None:
    if len(sys.argv) < 5:
        print(__doc__, file=sys.stderr)
        raise SystemExit(2)
    a, b, k, n = (int(x) for x in sys.argv[1:5])
    text = generate(a, b, k, n)
    if len(sys.argv) > 5:
        with open(sys.argv[5], "w") as f:
            f.write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
