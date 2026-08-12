"""Per-lemma stress tests for the Route-A proof of Theorem 1.

Each check() call prints (name, #cases, pass/fail).  A check that examines 0
cases is reported as VACUOUS and treated as a failure of the harness, not a
success of the lemma.
"""

import sys
from math import gcd

from shell import N_shell, chi_array, chi_scalar, cuts, levels, valuation

FAILED = []


def check(name, cases_iter, pred, expect_true=True):
    n = 0
    bad = []
    for case in cases_iter:
        n += 1
        ok = pred(*case)
        if ok != expect_true and len(bad) < 5:
            bad.append(case)
    status = "PASS" if (not bad and n > 0) else ("VACUOUS" if n == 0 else "FAIL")
    if status != "PASS":
        FAILED.append((name, status, bad[:5]))
    print(f"  [{status:7}] {name:52s} cases={n:>9}  {('' if not bad else 'first bad: ' + str(bad[:3]))}")
    return status == "PASS"


def S(a, m):
    """S_m = a + a^2 + ... + a^m, S_0 = 0."""
    return sum(a**i for i in range(1, m + 1))


# ---------------------------------------------------------------- parameters
def params(a_max, k_max, b_pred):
    for a in range(2, a_max + 1):
        for b in range(1, 3 * a_max + 2):
            if gcd(a, b) != 1 or not b_pred(a, b):
                continue
            for k in range(2, k_max + 1):
                yield a, b, k


def params_c(a_max, k_max, b_pred):
    for a, b, k in params(a_max, k_max, b_pred):
        for c in range(2, k):  # 2 <= c <= k-1
            yield a, b, k, c


BLT = lambda a, b: b < a
BGT = lambda a, b: b > a


def main():
    A = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 10

    print(f"\n=== Structural identities (definition sanity), a<={A}, k<={K} ===")

    # N = b(a^{k-1} + 2 S_{k-2})
    check(
        "N = b(a^{k-1} + 2 S_{k-2})",
        params(A, K, BLT),
        lambda a, b, k: N_shell(a, b, k) == b * (a ** (k - 1) + 2 * S(a, k - 2)),
    )
    # c_i = b S_{i-1}
    check(
        "c_i = b*S_{i-1} for 1<=i<=k-1",
        params(A, K, BLT),
        lambda a, b, k: all(cuts(a, b, k)[i] == b * S(a, i - 1) for i in range(1, k)),
    )
    # (a-1) S_m = a^{m+1} - a
    check(
        "(a-1) S_m = a^{m+1} - a",
        ((a, m) for a in range(2, A + 1) for m in range(0, K + 1)),
        lambda a, m: (a - 1) * S(a, m) == a ** (m + 1) - a,
    )
    # core width
    check(
        "N - 2 c_{k-1} = b a^{k-1}  (core width = L_k)",
        params(A, K, BLT),
        lambda a, b, k: N_shell(a, b, k) - 2 * cuts(a, b, k)[k - 1] == b * a ** (k - 1),
    )
    # splitting identity used in Lemma 4
    def T_of(a, k, c):
        """T = 1 + a + ... + a^{k-2-c}, = 0 when c = k-1."""
        return (a ** (k - 1 - c) - 1) // (a - 1)

    check(
        "N - 2c_c = b a^{k-1} + 2 b a^c T,  T = (a^{k-1-c}-1)/(a-1)",
        params_c(A, K, BLT),
        lambda a, b, k, c: N_shell(a, b, k) - 2 * cuts(a, b, k)[c]
        == b * a ** (k - 1) + 2 * b * a**c * T_of(a, k, c),
    )
    check(
        "T = 0 exactly when c = k-1; S_{k-2} = S_{c-1} + a^c T",
        params_c(A, K, BLT),
        lambda a, b, k, c: (T_of(a, k, c) == 0) == (c == k - 1)
        and S(a, k - 2) == S(a, c - 1) + a**c * T_of(a, k, c),
    )

    print(f"\n=== Lemma 2 (the colour classes are what we claim), a<=8, k<=5 ===")

    def small_params(bpred=BLT):
        for a in range(2, 9):
            for b in range(1, 15):
                if gcd(a, b) != 1 or not bpred(a, b):
                    continue
                for k in range(2, 6):
                    if N_shell(a, b, k) <= 20000:
                        yield a, b, k

    def classes_ok(a, b, k):
        N = N_shell(a, b, k)
        c = cuts(a, b, k)
        C = chi_array(a, b, k)
        for j in range(1, N + 1):
            v = valuation(j, a)
            col = int(C[j])
            if v >= 1:
                if col != min(v, k):
                    return False
            else:
                # unit: shell membership
                want = k
                for i in range(2, k):
                    if c[i - 1] + 1 <= j <= c[i] or N - c[i] + 1 <= j <= N - c[i - 1]:
                        want = i
                        break
                if col != want:
                    return False
        return True

    check("chi_array == definition, pointwise on all of [1,N]", small_params(), classes_ok)

    def no_unit_gets_colour_1(a, b, k):
        N = N_shell(a, b, k)
        C = chi_array(a, b, k)
        return all(not (valuation(j, a) == 0 and int(C[j]) == 1) for j in range(1, N + 1))

    check("colour 1 = {v(j)=1} exactly; no unit is coloured 1", small_params(), no_unit_gets_colour_1)

    def core_is_interval(a, b, k):
        N = N_shell(a, b, k)
        c = cuts(a, b, k)
        C = chi_array(a, b, k)
        lo, hi = c[k - 1] + 1, N - c[k - 1]
        for j in range(1, N + 1):
            if valuation(j, a) == 0:
                inside = lo <= j <= hi
                if (int(C[j]) == k) != inside:
                    return False
        return True

    check("units coloured k  <=>  in core [c_{k-1}+1, N-c_{k-1}]", small_params(), core_is_interval)

    print(f"\n=== Lemma 4 (shell gap), b < a,  a<={A}, k<={K}, 2<=c<=k-1 ===")

    check(
        "0 < 2 b S_{c-1} / a^c < 2   (so floor <= 1)",
        params_c(A, K, BLT),
        lambda a, b, k, c: 0 < 2 * b * S(a, c - 1) and 2 * b * S(a, c - 1) < 2 * a**c,
    )
    check(
        "b a^{c-1} * floor(N/a^c)  <=  N - 2 c_c",
        params_c(A, K, BLT),
        lambda a, b, k, c: b * a ** (c - 1) * (N_shell(a, b, k) // a**c)
        <= N_shell(a, b, k) - 2 * cuts(a, b, k)[c],
    )

    # the same statement in the "for all admissible s" form actually used.
    # Enumerating s explicitly is only feasible on a small grid; on the large
    # grid the floor form above is logically equivalent (the max over s is
    # attained at s = floor(N/a^c)).  Both are run.
    def gap_all_s(a, b, k, c):
        N = N_shell(a, b, k)
        cc = cuts(a, b, k)[c]
        smax = N // a**c
        return all(b * a ** (c - 1) * s <= N - 2 * cc for s in range(1, smax + 1))

    check(
        "for all s>=1 with a^c s <= N:  b a^{c-1} s <= N - 2c_c  (explicit s)",
        ((a, b, k, c) for a, b, k, c in params_c(7, 5, BLT)),
        gap_all_s,
    )

    # and it must FAIL for b > a, k >= 3, c = 2 -- that is the defect
    def gap_fails(a, b, k, c):
        N = N_shell(a, b, k)
        cc = cuts(a, b, k)[c]
        smax = N // a**c
        return b * a ** (c - 1) * smax > N - 2 * cc

    check(
        "Lemma 4 FAILS at c=2 when b>a, k>=3 (sharpness)",
        ((a, b, k, 2) for a, b, k in params(A, K, BGT) if k >= 3),
        gap_fails,
    )

    print(f"\n=== Lemma 5 (size bound for colour k), b < a, a<={A}, k<={K} ===")

    check(
        "N <= a^k + a^{k-1} - 2a",
        params(A, K, BLT),
        lambda a, b, k: N_shell(a, b, k) <= a**k + a ** (k - 1) - 2 * a,
    )
    check(
        "N < 2 a^k",
        params(A, K, BLT),
        lambda a, b, k: N_shell(a, b, k) < 2 * a**k,
    )
    check(
        "N < a^k (1+b)",
        params(A, K, BLT),
        lambda a, b, k: N_shell(a, b, k) < a**k * (1 + b),
    )
    # Consequence of N < 2a^k: branch B6 of the case tree is VACUOUS, because
    # [1,N] contains at most one multiple of a^k.
    check(
        "#{ j in [1,N] : a^k | j } <= 1   (so branch B6 is vacuous)",
        params(A, K, BLT),
        lambda a, b, k: N_shell(a, b, k) // a**k <= 1,
    )
    check(
        "k=2, ANY b coprime to a:  N = ab < a^2 b",
        ((a, b, 2) for a in range(2, A + 1) for b in range(1, 3 * A + 2) if gcd(a, b) == 1),
        lambda a, b, k: N_shell(a, b, k) == a * b and a * b < a**2 * b,
    )

    print("\n=== Summary ===")
    if FAILED:
        print(f"  {len(FAILED)} CHECK(S) NOT PASSING:")
        for name, status, bad in FAILED:
            print(f"    {status}: {name}  {bad}")
        sys.exit(1)
    print("  all checks PASS")


if __name__ == "__main__":
    main()
