"""Exhaustiveness audit of the Route-A case tree.

For every (a,b,k) in range and every monochromatic PAIR x > y (chi(x)=chi(y)=c):

  1. classify the pair into one of the branches of the written proof.
     A pair that no branch claims is reported as UNCOVERED -> the proof's case
     analysis would be incomplete.  This is the exhaustiveness test.
  2. assert the numeric/divisibility fact that branch *states* actually holds
     for this pair.  This is the soundness-of-each-branch test.
  3. independently of 1 and 2, check directly that the pair admits no t with
     x - y = b t, a t <= N, chi(a t) = c.  This is the ground truth.

If (3) ever finds an admissible t while (1)/(2) reported the pair handled, the
written proof is WRONG and the audit says so.

Branch labels mirror the LaTeX proof:
  B1  c=1,          both v=1                     (valuation)
  B2  2<=c<=k-1,    both v=c                     (valuation)
  B3  any c>=2,     one multiple of a, one unit  (valuation)
  B4  2<=c<=k-1,    both units, same interval    (shell width)
  B5  2<=c<=k-1,    both units, opposite ends    (Lemma 4, the hard branch)
  B6  c=k,          both v>=k                    (size: 2a^k > N)
  B7  c=k,          both units in the core        (core width)
"""

import sys
from itertools import combinations
from math import gcd

from shell import N_shell, chi_array, cuts, valuation

STATS = {}
PROBLEMS = []


def audit(a, b, k, verbose=False):
    N = N_shell(a, b, k)
    C = chi_array(a, b, k)
    cc = cuts(a, b, k)
    ak = a**k

    classes = {c: [] for c in range(1, k + 1)}
    for j in range(1, N + 1):
        classes[int(C[j])].append(j)

    n_pairs = 0
    counts = {}
    for c, members in classes.items():
        for y, x in combinations(members, 2):  # y < x, members ascending
            n_pairs += 1
            vx, vy = valuation(x, a), valuation(y, a)
            ux, uy = (vx == 0), (vy == 0)
            d = x - y

            # ---- 1. classify + 2. check the branch's own claim -------------
            label = None
            if c == 1:
                assert not ux and not uy, "colour 1 contains a unit"
                assert vx == 1 and vy == 1
                label = "B1"
                ok = (d % a == 0)  # v(x-y) >= 1, contradicting v(t) = 0
            elif ux != uy:
                label = "B3"
                ok = (d % a != 0)  # v(x-y) = 0, contradicting v(t) >= 1
            elif c <= k - 1:
                if not ux:  # both multiples of a with v = c
                    assert vx == c and vy == c
                    label = "B2"
                    ok = (d % a**c == 0)  # v(x-y) >= c, contradicting v(t)=c-1
                else:  # both units in shell c
                    L_c = a ** (c - 1) * b
                    left = (cc[c - 1] + 1, cc[c])
                    right = (N - cc[c] + 1, N - cc[c - 1])
                    inl = lambda j, iv: iv[0] <= j <= iv[1]
                    if (inl(x, left) and inl(y, left)) or (inl(x, right) and inl(y, right)):
                        label = "B4"
                        ok = d <= L_c - 1
                    elif inl(x, right) and inl(y, left):
                        label = "B5"
                        ok = (d >= N - 2 * cc[c] + 1) and (
                            b * a ** (c - 1) * (N // a**c) <= N - 2 * cc[c]
                        )
                    else:
                        label = "UNCOVERED-shell"
                        ok = False
            else:  # c == k
                if not ux:  # both v >= k
                    assert vx >= k and vy >= k
                    label = "B6"
                    ok = (x >= 2 * ak) and (N < 2 * ak)
                else:  # both units, must be in the core
                    lo, hi = cc[k - 1] + 1, N - cc[k - 1]
                    label = "B7" if (lo <= y and x <= hi) else "UNCOVERED-core"
                    ok = (d <= b * a ** (k - 1) - 1) if label == "B7" else False

            counts[label] = counts.get(label, 0) + 1
            if not ok:
                PROBLEMS.append(("branch-claim-false", (a, b, k), c, label, (x, y)))

            # ---- 3. ground truth -------------------------------------------
            if d % b == 0:
                t = d // b
                z = a * t
                if z <= N and int(C[z]) == c:
                    PROBLEMS.append(("MONOCHROMATIC-SOLUTION", (a, b, k), c, label, (x, y, z)))

    for lab, n in counts.items():
        STATS[lab] = STATS.get(lab, 0) + n
    return n_pairs, counts


def main():
    a_max = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    k_max = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    n_cap = int(sys.argv[3]) if len(sys.argv) > 3 else 1400

    total_pairs = 0
    points = 0
    print(f"{'a':>3} {'b':>3} {'k':>3} {'N':>7} {'mono pairs':>12}   branch histogram")
    for a in range(2, a_max + 1):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            for k in range(2, k_max + 1):
                N = N_shell(a, b, k)
                if N > n_cap:
                    continue
                np_, counts = audit(a, b, k)
                total_pairs += np_
                points += 1
                hist = " ".join(f"{lab}:{n}" for lab, n in sorted(counts.items()))
                print(f"{a:>3} {b:>3} {k:>3} {N:>7} {np_:>12}   {hist}")

    print()
    print(f"parameter points audited     : {points}")
    print(f"monochromatic pairs examined : {total_pairs}")
    print(f"branch totals                : {dict(sorted(STATS.items()))}")
    uncovered = sum(v for kk, v in STATS.items() if kk.startswith("UNCOVERED"))
    print(f"UNCOVERED pairs              : {uncovered}")
    print(f"problems                     : {len(PROBLEMS)}")
    for p in PROBLEMS[:10]:
        print("   ", p)
    if PROBLEMS or uncovered:
        sys.exit(1)
    print("AUDIT PASS: every monochromatic pair is covered by a branch, every")
    print("branch claim holds on it, and no admissible t exists for any of them.")


if __name__ == "__main__":
    main()
