#!/usr/bin/env python3
"""Independent ground truth for the CAS/SMT arithmetic capability corpus.

**Nothing in this file calls axeyum.** That is the point: a corpus whose expected
verdicts come from the tool under test measures nothing. Every expected verdict
in `corpus.md` is established here by one of five methods, and the method is
recorded per query:

  witness  — a concrete integer assignment, evaluated with Python's exact
             big-integer arithmetic. A verified witness PROVES `sat`.
  scan     — exhaustive enumeration over an explicitly stated finite box.
             For a `sat` claim a hit is a proof. For an `unsat` claim it is
             CORROBORATION WITHIN THE BOX ONLY, never a proof; every `unsat`
             justified by `scan` also carries a `proof` or `theorem`.
  proof    — a hand proof, written out in the entry's `why` string.
  theorem  — a classical theorem cited by name.
  open     — believed unsettled by mathematics as of 2026. NO expected verdict.
             Any decisive answer from any solver must be independently checked
             before it is believed.

Run:  python3 ground_truth.py
Exit: 0 iff every checkable claim checks out.
"""

from __future__ import annotations

import itertools
import sys

FAILURES: list[str] = []
CHECKED = 0


def ok(cond: bool, msg: str) -> None:
    global CHECKED
    CHECKED += 1
    if cond:
        print(f"  OK    {msg}")
    else:
        print(f"  FAIL  {msg}")
        FAILURES.append(msg)


def section(name: str) -> None:
    print(f"\n=== {name} ===")


# ---------------------------------------------------------------- axis A
# Units and variable-divisor divisibility: the headline failure mode.
def axis_a() -> None:
    section("A — units (a*p = 1) and variable-divisor divisibility")

    # A1 unit-direct: a >= 2 /\ a*p = 1  ->  UNSAT.
    # proof: a >= 2 and a*p = 1 force p != 0, so |p| >= 1 and |a*p| >= 2 > 1.
    ok(
        not any(a * p == 1 for a in range(2, 400) for p in range(-400, 401)),
        "A1  unit-direct        unsat: no a in [2,400), p in [-400,400] with a*p=1 (proof: |a*p|>=2)",
    )
    # A2 control: a >= 1 /\ a*p = 1  ->  SAT at a=1,p=1.
    ok(1 * 1 == 1 and 1 >= 1, "A2  unit-control-a1    sat  : witness a=1 p=1")
    # A3 unit-neg: a <= -2 /\ a*p = 1 -> UNSAT (same magnitude argument).
    ok(
        not any(a * p == 1 for a in range(-400, -1) for p in range(-400, 401)),
        "A3  unit-neg           unsat: no a<=-2, |p|<=400 with a*p=1 (proof: |a*p|>=2)",
    )
    # A4 control: a <= -1 /\ a*p = 1 -> SAT at a=-1,p=-1.
    ok((-1) * (-1) == 1 and -1 <= -1, "A4  unit-control-neg   sat  : witness a=-1 p=-1")
    # A5 unit-signed: a >= 2 /\ p >= 1 /\ a*p = 1 -> UNSAT (a*p >= 2).
    ok(
        not any(a * p == 1 for a in range(2, 400) for p in range(1, 400)),
        "A5  unit-signed        unsat: a>=2,p>=1 => a*p>=2 (proof)",
    )
    # A6 unit-product: a >= 2 /\ b >= 1 /\ (a*b)*p = 1 -> UNSAT (composite divisor).
    ok(
        not any(
            (a * b) * p == 1 for a in range(2, 60) for b in range(1, 60) for p in range(-200, 201)
        ),
        "A6  unit-product       unsat: a*b >= 2 so (a*b)*p != 1 (proof); scan empty",
    )
    # A7 notdiv-1-witness: a >= 2 |= 1 = a*0 + 1 /\ 1 <= 1 <= a-1. Refutation of
    # the negation. proof: 1 = a*0+1 holds identically; 1 <= a-1 <=> a >= 2.
    ok(
        all(1 == a * 0 + 1 and 1 <= 1 <= a - 1 for a in range(2, 5000)),
        "A7  notdiv-1-witness   unsat: side conditions hold for every a in [2,5000)",
    )
    # A8 control: the same with r := 0 is a BOGUS witness (1 <= 0 is false), so
    # the negation is satisfiable -> SAT.
    ok(not (1 <= 0), "A8  notdiv-1-wit-ctrl  sat  : r=0 violates 1<=r, so the negation holds")
    # A9 div-var-x: a >= 2 /\ b >= 1 /\ x = a*b^2 + 1 /\ x = a*p -> UNSAT.
    # proof: a | x and a | a*b^2 give a | 1, contradiction with a >= 2.
    ok(
        not any(
            a * b * b + 1 == a * p
            for a in range(2, 60)
            for b in range(1, 60)
            for p in range(0, 4000)
        ),
        "A9  div-var-x          unsat: scan a<60,b<60,p<4000 empty (proof: a|1)",
    )
    # A10 witness direction of A9: s := b^2, r := 1.
    ok(
        all(
            a * b * b + 1 == a * (b * b) + 1 and 1 <= 1 <= a - 1
            for a in range(2, 200)
            for b in range(1, 200)
        ),
        "A10 nondiv-x-witness   unsat: s=b^2,r=1 side conditions hold for all a>=2",
    )
    # A11 control: x = a*b^2 (no +1) IS divisible -> SAT with p = b^2.
    ok(3 * 4 * 4 == 3 * 16, "A11 div-var-x-control  sat  : witness a=3 b=4 x=48 p=16")
    # A12 cube-nondiv: a >= 2 /\ z = a^2*(a+1) /\ z = a^3*p -> UNSAT.
    # proof: a^3*p = a^3 + a^2  =>  a*(p-1) = 1  =>  contradiction (A1).
    ok(
        not any(
            a * a * (a + 1) == a * a * a * p for a in range(2, 200) for p in range(-50, 200)
        ),
        "A12 cube-nondiv        unsat: scan a<200,p in[-50,200) empty (proof: a*(p-1)=1)",
    )
    # A13 control: z = a^3*(a+1) IS divisible by a^3 -> SAT with p = a+1.
    ok(2**3 * 3 == 2**3 * 3, "A13 cube-nondiv-ctrl   sat  : witness a=2 z=24 p=3")
    # A14 mod phrasing: a >= 2 /\ (1 mod a) != 1 -> UNSAT (Euclidean mod, 0<=r<|a|).
    ok(
        all(1 % a == 1 for a in range(2, 5000)),
        "A14 mod-phrasing       unsat: 1 mod a = 1 for every a in [2,5000)",
    )
    # A15 control: a >= 1 admits a = 1, where 1 mod 1 = 0 != 1 -> SAT.
    ok(1 % 1 == 0, "A15 mod-phrasing-ctrl  sat  : witness a=1, 1 mod 1 = 0 != 1")


# ---------------------------------------------------------------- axis B
# Opaque symbol vs instantiated: "generalising a lemma made it harder".
def axis_b() -> None:
    section("B — opaque symbol vs instantiated form")

    # B1 opaque-window: M >= 1 /\ 1 <= M*c /\ M*c <= M-1 -> UNSAT.
    # proof: M*c >= 1 and M*c <= M-1 give M >= 2; then M*c >= 1 with M >= 2
    # forces c >= 1, so M*c >= M > M-1. Contradiction.
    ok(
        not any(
            1 <= m * c <= m - 1 for m in range(1, 300) for c in range(-300, 300)
        ),
        "B1  opaque-window      unsat: scan M<300,|c|<300 empty (proof above)",
    )
    # B2 control: widen the window to M*c <= M -> SAT at M=1,c=1.
    ok(1 <= 1 * 1 <= 1, "B2  opaque-window-ctrl sat  : witness M=1 c=1")
    # B3 instantiated-window: a >= 2 /\ r = a^2*(w-s) /\ 1 <= r <= a^2-1 -> UNSAT.
    # Same fact at M := a^2 (>= 4).
    ok(
        not any(
            1 <= a * a * (w - s) <= a * a - 1
            for a in range(2, 60)
            for w in range(-60, 60)
            for s in range(-60, 60)
        ),
        "B3  instantiated-window unsat: scan a<60,|w|,|s|<60 empty (M:=a^2 case of B1)",
    )
    # B4 control: widen to r <= a^2 -> SAT at a=2,w=1,s=0,r=4.
    ok(1 <= 2 * 2 * (1 - 0) <= 2 * 2, "B4  inst-window-ctrl   sat  : witness a=2 w=1 s=0 r=4")
    # B5 opaque-window-bounded: M >= 4 /\ 1 <= M*c <= M-1 -> UNSAT (B1 + bound).
    ok(
        not any(1 <= m * c <= m - 1 for m in range(4, 300) for c in range(-300, 300)),
        "B5  opaque-window-M>=4 unsat: scan M in [4,300), |c|<300 empty",
    )
    # B6 opaque-mono: M >= 1 /\ w >= 1 /\ M*w < M -> UNSAT (M*w >= M*1 = M).
    ok(
        not any(m * w < m for m in range(1, 400) for w in range(1, 400)),
        "B6  opaque-mono        unsat: M,w>=1 => M*w>=M (proof)",
    )
    # B7 instantiated-mono: a>=2 /\ b>=1 /\ w>=1 /\ (a*b)*w < a*b -> UNSAT.
    ok(
        not any(
            (a * b) * w < a * b for a in range(2, 60) for b in range(1, 60) for w in range(1, 60)
        ),
        "B7  instantiated-mono  unsat: M:=a*b case of B6",
    )
    # B8 control: claim M*w > M strictly; assert M*w <= M -> SAT at M=1,w=1.
    ok(1 * 1 <= 1, "B8  opaque-mono-ctrl   sat  : witness M=1 w=1")
    # B9 uf-opaque-identity: (f(x)+y)^2 = f(x)^2 + 2f(x)y + y^2, f uninterpreted.
    # Valid for ANY value of the opaque atom f(x); the negation is UNSAT.
    ok(
        all((u + y) ** 2 == u * u + 2 * u * y + y * y for u in range(-40, 40) for y in range(-40, 40)),
        "B9  uf-opaque-identity unsat: ring identity, holds for every value of the opaque atom",
    )
    # B10 control: same identity + 1 -> the negation is SAT (u=0,y=0: 0 != 1).
    ok((0 + 0) ** 2 != 0 * 0 + 2 * 0 * 0 + 0 * 0 + 1, "B10 uf-opaque-ident-ctrl sat: witness f(x)=0 y=0")


# ---------------------------------------------------------------- axis C
# Monolithic vs decomposed hypothesis sets.
def axis_c() -> None:
    section("C — monolithic vs decomposed hypothesis sets (k=2 colour-1 chain)")

    # The monolithic query, hypotheses H:
    #   a>=2, b>=1, t>=1, N = a*b, z = a*t, x = y + b*t, y>=1, x<=N,
    #   x = a*px, y = a*py, a*u + b*v = 1
    # C1 mono-k2-colour1 -> UNSAT.
    # proof: a | x and a | y  =>  a | x-y = b*t.  Bezout gives gcd(a,b)=1, so
    # a | t, say t = a*w with w >= 1 (t >= 1, a >= 2).  Then x - y = b*t = a*b*w
    # = N*w >= N.  But x <= N and y >= 1 give x - y <= N - 1.  Contradiction.
    def mono_sat(with_bezout: bool, hi: int) -> tuple | None:
        for a in range(2, hi):
            for b in range(1, hi):
                if with_bezout:
                    # gcd(a,b) == 1 is exactly solvability of a*u+b*v=1 over Z.
                    from math import gcd

                    if gcd(a, b) != 1:
                        continue
                for t in range(1, hi):
                    for py in range(1, hi):
                        y = a * py
                        x = y + b * t
                        if x > a * b:
                            continue
                        if x % a == 0:
                            return (a, b, t, x, y)
        return None

    ok(mono_sat(True, 26) is None, "C1  mono-k2-colour1    unsat: scan a,b,t,py<26 coprime empty (proof above)")
    # C2 control: DROP the Bezout hypothesis -> SAT.  Hand witness a=4,b=2,t=2:
    #   N=8, y=4 (py=1), x=y+b*t=8 (px=2), z=a*t=8, x<=N ok.
    a, b, t, py = 4, 2, 2, 1
    y = a * py
    x = y + b * t
    ok(
        a >= 2 and b >= 1 and t >= 1 and y >= 1 and x <= a * b and x % a == 0,
        f"C2  mono-k2-no-gcd     sat  : witness a=4 b=2 t=2 y=4 x=8 N=8 (x={x}, N={a*b})",
    )
    # The decomposition, each an independently valid implication over Z:
    # C3 L1: a>=2 /\ a*t = a^2*q  |=  t = a*q      (cancel a != 0)
    # NON-VACUITY: count the hypothesis-satisfying triples actually examined.
    hits = [
        (a, t, q)
        for a in range(2, 40)
        for t in range(-200, 200)
        for q in range(-40, 40)
        if a * t == a * a * q
    ]
    ok(
        len(hits) > 1000 and all(t == a * q for a, t, q in hits),
        f"C3  L1-cancel          unsat: {len(hits)} hypothesis-satisfying triples, all give t=a*q",
    )
    # C4 control for L1: claim t = a*q + 1 -> SAT (a=2,t=0,q=0).
    ok(2 * 0 == 4 * 0 and 0 != 2 * 0 + 1, "C4  L1-cancel-ctrl     sat  : witness a=2 t=0 q=0")
    # C5 L2: a>=2 /\ t>=1 /\ t = a*w  |=  w >= 1
    hits = [(a, w) for a in range(2, 60) for w in range(-60, 60) if a * w >= 1]
    ok(
        len(hits) > 1000 and all(w >= 1 for _, w in hits),
        f"C5  L2-positivity      unsat: {len(hits)} hypothesis-satisfying pairs, all give w>=1",
    )
    # C6 control: claim w >= 2 -> SAT (a=2,t=2,w=1).
    ok(2 * 1 == 2 and not (1 >= 2), "C6  L2-positivity-ctrl sat  : witness a=2 t=2 w=1")
    # C7 L3 MONO: a>=2 /\ b>=1 /\ w>=1 /\ t = a*w  |=  b*t >= a*b
    ok(
        all(
            b * (a * w) >= a * b
            for a in range(2, 40)
            for b in range(1, 40)
            for w in range(1, 40)
        ),
        "C7  L3-mono            unsat: b*t = (a*b)*w >= a*b for w>=1 (proof)",
    )
    # C8 control: claim b*t > a*b strictly -> SAT at w=1 (equality).
    ok(1 * (2 * 1) == 2 * 1, "C8  L3-mono-ctrl       sat  : witness a=2 b=1 w=1 t=2 (equality)")
    # C9 L4: y>=1 /\ x = y + P /\ P >= M /\ x <= M  |=  false
    ok(
        not any(
            y >= 1 and (y + P) <= M and P >= M
            for y in range(1, 60)
            for P in range(-60, 60)
            for M in range(-60, 60)
        ),
        "C9  L4-endpoint        unsat: x=y+P<=M and P>=M give y<=0, contra y>=1 (proof)",
    )
    # C10 control: weaken to P >= M-1 -> SAT (y=1,P=0,M=1).
    ok(1 >= 1 and (1 + 0) <= 1 and 0 >= 1 - 1, "C10 L4-endpoint-ctrl   sat  : witness y=1 P=0 M=1")
    # C11 L5: a|x /\ a|y /\ x - y = b*t  |=  b*t = a*(px - py)
    ok(
        all(
            (a * px) - (a * py) == a * (px - py)
            for a in range(2, 40)
            for px in range(-40, 40)
            for py in range(-40, 40)
        ),
        "C11 L5-distribute      unsat: ring identity a*px - a*py = a*(px-py)",
    )
    # C12 control: claim b*t = a*(px-py) + 1 -> SAT.
    ok(
        (2 * 3) - (2 * 1) != 2 * (3 - 1) + 1,
        "C12 L5-distribute-ctrl sat  : witness a=2 px=3 py=1 (4 != 5)",
    )
    # C13 L6 BEZOUT: a*u + b*v = 1 /\ b*t = a*d  |=  t = a*(t*u + v*d)
    # NON-VACUITY: the hypothesis set is narrow (Bezout AND a | b*t), so count.
    hits = [
        (a, b, u, v, t, d)
        for a in range(2, 14)
        for b in range(1, 14)
        for u in range(-14, 14)
        for v in range(-14, 14)
        if a * u + b * v == 1
        for t in range(-14, 14)
        for d in range(-40, 40)
        if b * t == a * d
    ]
    ok(
        len(hits) > 500 and all(t == a * (t * u + v * d) for a, b, u, v, t, d in hits),
        f"C13 L6-bezout          unsat: {len(hits)} hypothesis-satisfying tuples, all give t=a*(t*u+v*d)",
    )
    # C14 control: drop the Bezout hypothesis -> SAT (a=4,b=2,t=-2,u=-1,v=4,d=-1).
    a, b, t, u, v, d = 4, 2, -2, -1, 4, -1
    ok(
        b * t == a * d and t != a * (t * u + v * d),
        f"C14 L6-bezout-ctrl     sat  : witness a=4 b=2 t=-2 d=-1 u=-1 v=4 ({t} != {a*(t*u+v*d)})",
    )


# ---------------------------------------------------------------- axis D
# Polynomial identities, degree 2-4, 2-3 variables (+ minimal near-miss).
def axis_d() -> None:
    section("D — polynomial identities degree 2-4 in 2-3 variables")

    R = range(-12, 13)
    pairs = list(itertools.product(R, R))
    triples = list(itertools.product(range(-7, 8), repeat=3))

    def ident2(name: str, f, g) -> None:
        ok(all(f(x, y) == g(x, y) for x, y in pairs), f"{name} unsat: identity verified on [-12,12]^2")

    def ident3(name: str, f, g) -> None:
        ok(
            all(f(x, y, z) == g(x, y, z) for x, y, z in triples),
            f"{name} unsat: identity verified on [-7,7]^3",
        )

    ident2("D1  id2-square         ", lambda x, y: (x + y) ** 2, lambda x, y: x * x + 2 * x * y + y * y)
    ok((0 + 0) ** 2 != 0 + 1, "D2  id2-square-ctrl    sat  : witness x=0 y=0 (0 != 1)")
    ident2(
        "D3  id3-cube           ",
        lambda x, y: (x + y) ** 3,
        lambda x, y: x**3 + 3 * x * x * y + 3 * x * y * y + y**3,
    )
    ok((0 + 0) ** 3 != 0 + 1, "D4  id3-cube-ctrl      sat  : witness x=0 y=0")
    ident2(
        "D5  id3-sumcubes       ",
        lambda x, y: x**3 + y**3,
        lambda x, y: (x + y) * (x * x - x * y + y * y),
    )
    ok(0**3 + 0**3 != (0 + 0) * (0 - 0 + 0) + 1, "D6  id3-sumcubes-ctrl  sat  : witness x=0 y=0")
    ident2(
        "D7  id4-binom          ",
        lambda x, y: (x + y) ** 4,
        lambda x, y: x**4 + 4 * x**3 * y + 6 * x * x * y * y + 4 * x * y**3 + y**4,
    )
    ok((0 + 0) ** 4 != 0 + 1, "D8  id4-binom-ctrl     sat  : witness x=0 y=0")
    ident3(
        "D9  id2-three-var      ",
        lambda x, y, z: (x + y + z) ** 2,
        lambda x, y, z: x * x + y * y + z * z + 2 * x * y + 2 * x * z + 2 * y * z,
    )
    ok((0 + 0 + 0) ** 2 != 0 + 1, "D10 id2-three-var-ctrl sat  : witness x=y=z=0")
    ident3(
        "D11 id3-cyclic         ",
        lambda x, y, z: x**3 + y**3 + z**3 - 3 * x * y * z,
        lambda x, y, z: (x + y + z) * (x * x + y * y + z * z - x * y - y * z - z * x),
    )
    ok(
        0**3 + 0**3 + 0**3 - 3 * 0 * 0 * 0 != (0 + 0 + 0) * (0 + 0 + 0 - 0 - 0 - 0) + 1,
        "D12 id3-cyclic-ctrl    sat  : witness x=y=z=0 (LHS 0 != RHS+1 = 1)",
    )
    ident2(
        "D13 id4-sophie-germain ",
        lambda x, y: x**4 + 4 * y**4,
        lambda x, y: (x * x + 2 * y * y - 2 * x * y) * (x * x + 2 * y * y + 2 * x * y),
    )
    ok(
        1**4 + 4 * 0**4 != (1 + 0 - 0) * (1 + 0 + 0) + 1,
        "D14 id4-sophie-ctrl    sat  : witness x=1 y=0 (LHS 1 != RHS+1 = 2)",
    )
    ident2(
        "D15 id4-difference     ",
        lambda x, y: x**4 - y**4,
        lambda x, y: (x - y) * (x + y) * (x * x + y * y),
    )
    ok(
        2**4 - 1**4 != (2 - 1) * (2 + 1) * (4 + 1) + 1,
        "D16 id4-difference-ctrl sat : witness x=2 y=1 (15 != 16)",
    )
    # D17 conditional congruence: x = y  |=  x^3 = y^3.
    ok(
        all(x**3 == y**3 for x, y in pairs if x == y),
        "D17 id-congruence      unsat: every pair on [-12,12]^2 with x=y has x^3=y^3",
    )
    ok(2**3 != 1**3, "D18 id-congruence-ctrl sat  : witness x=2 y=1 (x=y+1, 8 != 1)")
    # D19 degree-4 three-variable identity (Lagrange/Euler four-square-ish slice):
    #     (x^2+y^2)*(z^2+1) = (x*z - y)^2 + (x + y*z)^2
    ident3(
        "D19 id4-brahmagupta    ",
        lambda x, y, z: (x * x + y * y) * (z * z + 1),
        lambda x, y, z: (x * z - y) ** 2 + (x + y * z) ** 2,
    )
    ok(
        (1 + 0) * (0 + 1) != (0 - 0) ** 2 + (1 + 0) ** 2 + 1,
        "D20 id4-brahmagupta-ctrl sat: witness x=1 y=0 z=0 (1 != 2)",
    )


# ---------------------------------------------------------------- axis F
# "Not identically zero" does NOT mean satisfiable over Z. These are the traps
# for any route that decides via a polynomial zero-test alone.
def axis_f() -> None:
    section("F — nonzero-polynomial-but-UNSAT traps + their sat controls")

    # F1 x*x = 2 -> UNSAT over Z (x^2 - 2 is not the zero polynomial!).
    ok(
        not any(x * x == 2 for x in range(-10**5, 10**5)),
        "F1  square-eq-2        unsat: no x with |x|<1e5 has x^2=2 (proof: 1^2<2<2^2)",
    )
    # F2 x*x = 4 -> SAT.
    ok(2 * 2 == 4, "F2  square-eq-4        sat  : witness x=2")
    # F3 x^2 + y^2 = 3 -> UNSAT (a sum of two squares is never 3 mod 4).
    ok(
        not any(x * x + y * y == 3 for x in range(-4, 5) for y in range(-4, 5)),
        "F3  sum2sq-3           unsat: theorem (n = 3 mod 4 is not a sum of two squares)",
    )
    # F4 x^2 + y^2 = 5 -> SAT.
    ok(1 * 1 + 2 * 2 == 5, "F4  sum2sq-5           sat  : witness x=1 y=2")
    # F5 x^2 + y^2 + z^2 = 7 -> UNSAT (Legendre: n = 4^a(8b+7) is not a sum of 3 squares).
    ok(
        not any(
            x * x + y * y + z * z == 7 for x in range(-3, 4) for y in range(-3, 4) for z in range(-3, 4)
        ),
        "F5  sum3sq-7           unsat: Legendre three-square theorem (7 = 8*0+7)",
    )
    # F6 x^2 + y^2 + z^2 = 6 -> SAT.
    ok(1 + 1 + 4 == 6, "F6  sum3sq-6           sat  : witness x=1 y=1 z=2")
    # F7 x^2 + y^2 = z^2 /\ x = 3 /\ y = 5 -> UNSAT (34 is not a perfect square).
    ok(
        not any(z * z == 34 for z in range(-10, 11)),
        "F7  pythag-3-5         unsat: 34 is not a perfect square (5^2=25 < 34 < 36=6^2)",
    )
    # F8 control: x = 3, y = 4 -> SAT with z = 5.
    ok(3 * 3 + 4 * 4 == 5 * 5, "F8  pythag-3-4         sat  : witness z=5")
    # F9 4x + 6y = 3 -> UNSAT (LHS is even).
    ok(3 % 2 == 1, "F9  linear-gcd-3       unsat: 4x+6y is even, 3 is odd (proof)")
    # F10 control: 4x + 6y = 2 -> SAT.
    ok(4 * (-1) + 6 * 1 == 2, "F10 linear-gcd-2       sat  : witness x=-1 y=1")
    # F11 x*x = 2*y*y /\ y >= 1 -> UNSAT (irrationality of sqrt 2; infinite descent).
    ok(
        not any(x * x == 2 * y * y for x in range(0, 900) for y in range(1, 640)),
        "F11 sqrt2-descent      unsat: theorem (sqrt 2 irrational); scan x<900,y<640 empty",
    )
    # F12 control: x*x = 4*y*y /\ y >= 1 -> SAT.
    ok(2 * 2 == 4 * 1 * 1, "F12 sqrt2-descent-ctrl sat  : witness x=2 y=1")
    # F13 x^2 = y^3 /\ x >= 2 /\ y >= 2 -> SAT (x=8, y=4: 64 = 64).
    ok(8**2 == 4**3, "F13 square-eq-cube     sat  : witness x=8 y=4 (64=64)")
    # F14 x^2 = y^3 + 7 /\ ... -> Mordell curve y^3 = x^2 - 7 has NO integer point.
    # (Classical: x^2 + 7 = y^3 is Ramanujan-Nagell adjacent; x^2 = y^3 + 7 has no
    # solutions because x must be odd, then x^2+1 = y^3+8 = (y+2)(y^2-2y+4) with
    # y^2-2y+4 = (y-1)^2+3 having a prime factor = 3 mod 4, impossible.)
    ok(
        not any(x * x == y**3 + 7 for x in range(-4000, 4000) for y in range(-2, 260)),
        "F14 mordell-7          unsat: Mordell y^3 = x^2 - 7 has no integer point (classical)",
    )


# ---------------------------------------------------------------- axis G
# Soundness tripwires and must-remain-unknown queries.
def axis_g() -> None:
    section("G — tripwires: huge witnesses, hard theorems, and OPEN problems")

    # G1 Pell d=61: x^2 - 61 y^2 = 1, y >= 1 -> SAT. Smallest witness is famous.
    x, y = 1766319049, 226153980
    ok(x * x - 61 * y * y == 1, f"G1  pell-61            sat  : witness x={x} y={y} (verified exactly)")
    # G2 Pell d=109 -> SAT with a ~1.6e14 witness. Well beyond any 32-bit blast.
    x, y = 158070671986249, 15140424455100
    ok(x * x - 109 * y * y == 1, f"G2  pell-109           sat  : witness x={x} y={y} (verified exactly)")
    # G3 negative Pell d=61: x^2 - 61 y^2 = -1 -> SAT.
    x, y = 29718, 3805
    ok(x * x - 61 * y * y == -1, f"G3  pell-61-neg        sat  : witness x={x} y={y} (verified exactly)")
    # G4 x^2 - 4 y^2 = 2 -> UNSAT ((x-2y)(x+2y) = 2 needs both factors of the
    # same parity, but their product is 2 = 2*1).
    ok(
        not any(x * x - 4 * y * y == 2 for x in range(-300, 300) for y in range(-300, 300)),
        "G4  pell-square-d      unsat: (x-2y)(x+2y)=2 impossible by parity (proof)",
    )
    # G5 FLT n=4: x^4 + y^4 = z^4, x,y,z >= 1 -> UNSAT (Fermat's own descent).
    ok(
        not any(
            x**4 + y**4 == z**4 for x in range(1, 60) for y in range(1, 60) for z in range(1, 60)
        ),
        "G5  flt-4              unsat: Fermat n=4 (elementary descent); scan <60 empty",
    )
    # G6 near-miss control: x^4 + y^4 = z^4 + 1 -> SAT (1+1 = 1+1).
    ok(1**4 + 1**4 == 1**4 + 1, "G6  flt-4-nearmiss     sat  : witness x=y=z=1")
    # G7 FLT n=3: x^3 + y^3 = z^3, x,y,z >= 1 -> UNSAT (Euler).
    ok(
        not any(
            x**3 + y**3 == z**3 for x in range(1, 90) for y in range(1, 90) for z in range(1, 90)
        ),
        "G7  flt-3              unsat: Euler n=3; scan <90 empty",
    )
    # G8 taxicab: x^3 + y^3 = 1729, x,y >= 1 -> SAT.
    ok(1**3 + 12**3 == 1729 and 9**3 + 10**3 == 1729, "G8  taxicab-1729       sat  : witness x=9 y=10")
    # G9 three cubes = 4 -> UNSAT (n = 4 or 5 mod 9 is impossible; cubes are
    # 0, 1, 8 mod 9, and no three of those sum to 4 mod 9).
    cubes_mod9 = {(i**3) % 9 for i in range(9)}
    ok(
        cubes_mod9 == {0, 1, 8}
        and not any((a + b + c) % 9 == 4 for a in cubes_mod9 for b in cubes_mod9 for c in cubes_mod9),
        "G9  three-cubes-4      unsat: cubes are {0,1,8} mod 9; no triple sums to 4 mod 9 (proof)",
    )
    # G10 three cubes = 5 -> UNSAT, same mod-9 obstruction.
    ok(
        not any((a + b + c) % 9 == 5 for a in cubes_mod9 for b in cubes_mod9 for c in cubes_mod9),
        "G10 three-cubes-5      unsat: no triple of {0,1,8} sums to 5 mod 9 (proof)",
    )
    # G11 three cubes = 3 -> SAT (1,1,1) and famously (4,4,-5).
    ok(1 + 1 + 1 == 3 and 4**3 + 4**3 + (-5) ** 3 == 3, "G11 three-cubes-3      sat  : witness (1,1,1)")
    # G12 three cubes = 33 -> SAT, but only with the 2019 witness (~8.9e15).
    x, y, z = 8866128975287528, -8778405442862239, -2736111468807040
    ok(x**3 + y**3 + z**3 == 33, "G12 three-cubes-33     sat  : the 2019 witness verifies exactly (|x| ~ 8.9e15)")
    # G13 / G14 OPEN: x^3 + y^3 + z^3 = 114 and = 390 are, to the best of public
    # knowledge as of 2026, UNRESOLVED. No expected verdict.
    print("  OPEN  G13 three-cubes-114  expected=UNKNOWN: unresolved as of 2026 —")
    print("        a `sat` must be checked against Python before it is believed;")
    print("        an `unsat` would be a research-level theorem, not a feature.")
    print("  OPEN  G14 three-cubes-390  expected=UNKNOWN: same status.")
    # G15 Brocard: n! + 1 = m^2 has only n in {4,5,7} known; the general question
    # is open, but we pose the DECIDABLE instance 5! + 1 = m^2 -> SAT (m=11).
    ok(120 + 1 == 11 * 11, "G15 brocard-5          sat  : witness m=11 (5!+1 = 121)")


# ---------------------------------------------------------------- axis H
# Anchors: shapes the solver decides TODAY. A change that breaks these is a
# regression, whatever else it gains.
def axis_h() -> None:
    section("H — anchors that must not regress")

    ok(2 + 1 == 3 and 2 - 1 == 1, "H1  linear-sat         sat  : witness x=2 y=1")
    ok(3 != 4, "H2  linear-unsat       unsat: x+y cannot equal both 3 and 4 (proof)")
    ok(
        all(a * b >= 1 for a in range(2, 200) for b in range(1, 200)),
        "H3  mul-lower-bound    unsat: a>=2,b>=1 => a*b>=2>=1 (proof)",
    )
    # H4 difference logic negative cycle: x-y<=3, y-z<=2, z-x<=-6 sums to -1 < 0.
    ok(3 + 2 - 6 == -1, "H4  dl-negative-cycle  unsat: cycle weight 3+2-6 = -1 < 0 (proof)")
    # H5 control: z-x <= -5 sums to 0 -> SAT (tight assignment exists).
    ok(3 + 2 - 5 == 0, "H5  dl-zero-cycle      sat  : witness x=5 y=2 z=0 (3,2,-5 all tight)")


def main() -> int:
    print("Independent ground truth — axeyum is NOT consulted anywhere in this file.")
    axis_a()
    axis_b()
    axis_c()
    axis_d()
    axis_f()
    axis_g()
    axis_h()
    print(f"\n=== checked {CHECKED} claims, {len(FAILURES)} failed ===")
    for f in FAILURES:
        print(f"  FAILED: {f}")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
