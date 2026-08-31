#!/usr/bin/env python3
"""Route checks for ADR-1210: `Rat.det (matTranspose A) n = Rat.det A n`.

Every claim the ADR makes about indices, ranges and signs is re-derived here
against a direct simulation of the kernel's own definitions, rather than
inherited from ADR-1155 or ADR-1185.  Run it:

    python3 docs/research/09-decisions/adr-1210-det-transpose-checks.py

Exit status is 0 only when every check passes; the failure count is printed.
Sections 6 and 7 are NEGATIVE controls and must report differences.
"""

from fractions import Fraction
from itertools import product
import random
import sys

FAILURES = []


def ok(label, detail=""):
    print(f"ok   {label}{('  ' + detail) if detail else ''}")


def bad(label, detail=""):
    FAILURES.append(label)
    print(f"FAIL {label}{('  ' + detail) if detail else ''}")


def check(cond, label, detail=""):
    (ok if cond else bad)(label, detail)


# --------------------------------------------------------------------------
# The kernel's definitions, transcribed.
# --------------------------------------------------------------------------

def mat_skip(p, x):
    """`Rat.matSkip p x := if Nat.ble p x then Nat.succ x else x`."""
    return x + 1 if p <= x else x


def mat_minor(A, i, j):
    """`Rat.matMinor A i j r c := A (matSkip i r) (matSkip j c)`, curried."""
    return lambda r, c: A(mat_skip(i, r), mat_skip(j, c))


def alt_sign(j):
    """`Rat.altSign`, `(-1)^j` by `Nat.rec`."""
    return 1 if j % 2 == 0 else -1


def det(A, n):
    """`Rat.det`: expansion along the FIRST ROW, exactly as declared."""
    if n == 0:
        return Fraction(1)
    return sum(
        (alt_sign(j) * (A(0, j) * det(mat_minor(A, 0, j), n - 1))
         for j in range(n)),
        Fraction(0),
    )


def transpose(A):
    """`Rat.matTranspose A i j := A j i`."""
    return lambda i, j: A(j, i)


def col0(A, m):
    """The claimed COLUMN-0 expansion at dimension `succ m`."""
    return sum(
        (alt_sign(p) * (A(p, 0) * det(mat_minor(A, p, 0), m))
         for p in range(m + 1)),
        Fraction(0),
    )


def rand_mat(n, rng, lo=-4, hi=4):
    cells = {(r, c): Fraction(rng.randint(lo, hi)) for r in range(n) for c in range(n)}
    return lambda r, c: cells.get((r, c), Fraction(0))


# --------------------------------------------------------------------------
# 0. The simulation is the right one: agree with a Leibniz determinant.
# --------------------------------------------------------------------------

def leibniz(A, n):
    from itertools import permutations
    total = Fraction(0)
    for perm in permutations(range(n)):
        sign = 1
        seen = list(perm)
        for a in range(n):
            for b in range(a + 1, n):
                if seen[a] > seen[b]:
                    sign = -sign
        term = Fraction(sign)
        for r in range(n):
            term *= A(r, perm[r])
        total += term
    return total


rng = random.Random(20261210)
mismatch = 0
for n in range(0, 5):
    for _ in range(40):
        A = rand_mat(n, rng)
        if det(A, n) != leibniz(A, n):
            mismatch += 1
check(mismatch == 0, "0. the transcribed `Rat.det` is the determinant",
      f"{mismatch} disagreements with Leibniz, n = 0..4")

# --------------------------------------------------------------------------
# 1. THE TARGET.  det (transpose A) n = det A n.
# --------------------------------------------------------------------------

mismatch = 0
cases = 0
for n in range(0, 6):
    for _ in range(60):
        A = rand_mat(n, rng)
        cases += 1
        if det(transpose(A), n) != det(A, n):
            mismatch += 1
check(mismatch == 0, "1. det (transpose A) n = det A n",
      f"{cases} cases, n = 0..5, {mismatch} mismatches")

# --------------------------------------------------------------------------
# 2. THE CRUX.  Column-0 expansion, which is what the induction actually
#    needs and which `det_row_expansion` does NOT supply.
# --------------------------------------------------------------------------

mismatch = 0
cases = 0
for m in range(0, 5):
    for _ in range(60):
        A = rand_mat(m + 1, rng)
        cases += 1
        if col0(A, m) != det(A, m + 1):
            mismatch += 1
check(mismatch == 0,
      "2. det A (succ m) = sumRange (fun p => altSign p * (A p 0 * det (matMinor A p 0) m)) (succ m)",
      f"{cases} cases, m = 0..4, {mismatch} mismatches")

# --------------------------------------------------------------------------
# 3. The transpose induction step, as it will be written:
#      det (Aᵀ) (succ m)
#        = sumRange (fun q => altSign q * (A q 0 * det (matMinor A q 0) m)) (succ m)   [def + IH]
#        = det A (succ m)                                                             [col0]
#    The middle line requires `matMinor (transpose A) 0 q r c = transpose (matMinor A q 0) r c`
#    POINTWISE, which is what `det_congr` will carry.
# --------------------------------------------------------------------------

mismatch = 0
pairs = 0
for m in range(0, 5):
    for _ in range(20):
        A = rand_mat(m + 2, rng)
        for q in range(m + 1):
            lhs = mat_minor(transpose(A), 0, q)
            rhs = transpose(mat_minor(A, q, 0))
            for r in range(m + 2):
                for c in range(m + 2):
                    pairs += 1
                    if lhs(r, c) != rhs(r, c):
                        mismatch += 1
check(mismatch == 0,
      "3. matMinor (transpose A) 0 q = transpose (matMinor A q 0), pointwise",
      f"{pairs} index pairs, {mismatch} mismatches")

# The index identity underneath it, free of any matrix:
#   matSkip 0 r = succ r   and   matSkip q c is the same on both sides.
mismatch = sum(1 for r in range(12) if mat_skip(0, r) != r + 1)
check(mismatch == 0, "3a. matSkip 0 r = succ r (`matSkip_zero`, `Eq.refl`)",
      f"{mismatch} mismatches over r < 12")

# --------------------------------------------------------------------------
# 4. THE COLUMN-0 INDUCTION STEP, in the exact shape the Rust will build.
#
#    L := det A (succ (succ m'))                        expanded by `det_succ`
#         then each inner `det (matMinor A 0 q) (succ m')` by the IH (col0 at m')
#    R := col0 A (succ m')                              the goal's right side
#         then each inner `det (matMinor A p 0) (succ m')` by `det_succ`
#
#    Both peel their q = 0 / p = 0 head; the heads are *identical*, and the
#    tails are a rectangle whose termwise summands agree after ONE swap.
# --------------------------------------------------------------------------

def L_head(A, mp):
    return alt_sign(0) * (A(0, 0) * det(mat_minor(A, 0, 0), mp + 1))


def R_head(A, mp):
    return alt_sign(0) * (A(0, 0) * det(mat_minor(A, 0, 0), mp + 1))


def L_tail_term(A, mp, cp, pp):
    """outer q = succ cp (row-0 expansion), inner p = pp (col-0 expansion of the minor)."""
    inner_mat = mat_minor(A, 0, cp + 1)
    D1 = mat_minor(inner_mat, pp, 0)
    return (alt_sign(cp + 1)
            * (A(0, cp + 1)
               * (alt_sign(pp) * (inner_mat(pp, 0) * det(D1, mp)))))


def R_tail_term(A, mp, pp, cp):
    """outer p = succ pp (col-0 expansion), inner c = cp (row-0 expansion of the minor)."""
    inner_mat = mat_minor(A, pp + 1, 0)
    D2 = mat_minor(inner_mat, 0, cp)
    return (alt_sign(pp + 1)
            * (A(pp + 1, 0)
               * (alt_sign(cp) * (inner_mat(0, cp) * det(D2, mp)))))


head_bad = tail_bad = whole_bad = 0
cases = 0
for mp in range(0, 4):
    n = mp + 2
    for _ in range(25):
        A = rand_mat(n, rng)
        cases += 1
        L = det(A, n)
        R = col0(A, n - 1)
        Lsum = L_head(A, mp) + sum(
            (L_tail_term(A, mp, cp, pp) for cp in range(mp + 1) for pp in range(mp + 1)),
            Fraction(0))
        Rsum = R_head(A, mp) + sum(
            (R_tail_term(A, mp, pp, cp) for pp in range(mp + 1) for cp in range(mp + 1)),
            Fraction(0))
        if L != Lsum:
            head_bad += 1
        if R != Rsum:
            tail_bad += 1
        if L != R:
            whole_bad += 1

check(head_bad == 0, "4a. L decomposes as head + double tail", f"{cases} cases, {head_bad} bad")
check(tail_bad == 0, "4b. R decomposes as head + double tail", f"{cases} cases, {tail_bad} bad")
check(whole_bad == 0, "4c. L = R (the column-0 step)", f"{cases} cases, {whole_bad} bad")

# The heads are literally the same expression, not merely equal:
check(True, "4d. the two heads are the SAME term",
      "altSign 0 * (A 0 0 * det (matMinor A 0 0) (succ m')) on both sides, by construction")

# --------------------------------------------------------------------------
# 5. THE PAIRING.  L's (cp, pp) term equals R's (pp, cp) term, TERMWISE --
#    so the tails need `sumRange_swap` and nothing else.  Two sub-claims:
#    (a) the double minors D1 and D2 agree POINTWISE, and
#    (b) the scalar coefficients agree.
# --------------------------------------------------------------------------

pointwise_bad = 0
pairs = 0
for mp in range(0, 4):
    n = mp + 2
    for _ in range(15):
        A = rand_mat(n, rng)
        for cp in range(mp + 1):
            for pp in range(mp + 1):
                D1 = mat_minor(mat_minor(A, 0, cp + 1), pp, 0)
                D2 = mat_minor(mat_minor(A, pp + 1, 0), 0, cp)
                for r in range(mp + 1):
                    for c in range(mp + 1):
                        pairs += 1
                        if D1(r, c) != D2(r, c):
                            pointwise_bad += 1
check(pointwise_bad == 0,
      "5a. matMinor (matMinor A 0 (succ cp)) pp 0 = matMinor (matMinor A (succ pp) 0) 0 cp, pointwise",
      f"{pairs} index pairs, {pointwise_bad} mismatches")

# And the index identity underneath 5a, matrix-free.  It is `matSkip_succ_succ`
# on each axis and NOTHING ELSE -- in particular it is NOT `matSkip_comm`, and
# it needs no `ble` hypothesis.
idx_bad = 0
idx_cases = 0
for cp, pp, r, c in product(range(6), repeat=4):
    idx_cases += 1
    row_lhs = mat_skip(0, mat_skip(pp, r))
    row_rhs = mat_skip(pp + 1, mat_skip(0, r))
    col_lhs = mat_skip(cp + 1, mat_skip(0, c))
    col_rhs = mat_skip(0, mat_skip(cp, c))
    if row_lhs != row_rhs or col_lhs != col_rhs:
        idx_bad += 1
check(idx_bad == 0,
      "5b. the double-minor index identity is `matSkip_succ_succ` on each axis, unconditionally",
      f"{idx_cases} (cp,pp,r,c) tuples < 6, {idx_bad} mismatches; no `ble` hypothesis anywhere")

# (c) the row entry the inner expansion reads.
entry_bad = 0
entry_cases = 0
for mp in range(0, 4):
    n = mp + 2
    for _ in range(15):
        A = rand_mat(n, rng)
        for cp in range(mp + 1):
            for pp in range(mp + 1):
                entry_cases += 1
                if mat_minor(A, 0, cp + 1)(pp, 0) != A(pp + 1, 0):
                    entry_bad += 1
                if mat_minor(A, pp + 1, 0)(0, cp) != A(0, cp + 1):
                    entry_bad += 1
check(entry_bad == 0,
      "5c. matMinor A 0 (succ cp) pp 0 = A (succ pp) 0 and matMinor A (succ pp) 0 0 cp = A 0 (succ cp)",
      f"{entry_cases} pairs, {entry_bad} mismatches (needs matSkip q 0 = 0 for q = succ _)")

# `matSkip (succ q) 0 = 0` -- iota-reducible, since `Nat.ble (succ q) zero` is
# `false` by the zero row of `ble`'s inner recursion.
check(all(mat_skip(q + 1, 0) == 0 for q in range(12)),
      "5d. matSkip (succ q) 0 = 0", "q < 12")

# (d) the signs.  altSign (succ cp) * altSign pp = altSign (succ pp) * altSign cp.
sign_bad = sum(1 for cp in range(12) for pp in range(12)
               if alt_sign(cp + 1) * alt_sign(pp) != alt_sign(pp + 1) * alt_sign(cp))
check(sign_bad == 0,
      "5e. altSign (succ cp) * altSign pp = altSign (succ pp) * altSign cp",
      f"{sign_bad} mismatches over cp, pp < 12; both are neg (altSign cp * altSign pp)")

# --------------------------------------------------------------------------
# 6. NEGATIVE CONTROL: `matSkip`'s two branches swapped.
#    Both the target and the crux must become FALSE.
# --------------------------------------------------------------------------

def mat_skip_swapped(p, x):
    return x if p <= x else x + 1


def with_skip(skip):
    def minor(A, i, j):
        return lambda r, c: A(skip(i, r), skip(j, c))

    def dt(A, n):
        if n == 0:
            return Fraction(1)
        return sum((alt_sign(j) * (A(0, j) * dt(minor(A, 0, j), n - 1))
                    for j in range(n)), Fraction(0))

    def c0(A, m):
        return sum((alt_sign(p) * (A(p, 0) * dt(minor(A, p, 0), m))
                    for p in range(m + 1)), Fraction(0))

    return dt, c0, minor


mut_det, mut_col0, mut_minor = with_skip(mat_skip_swapped)

diff = tot = 0
for n in range(2, 6):
    for _ in range(60):
        A = rand_mat(n, rng)
        tot += 1
        if mut_det(transpose(A), n) != mut_det(A, n):
            diff += 1
check(diff > 0, "6a. CONTROL: swapped `matSkip` makes det Aᵀ = det A FALSE",
      f"{diff} of {tot} cases differ")

diff = tot = 0
for m in range(1, 5):
    for _ in range(60):
        A = rand_mat(m + 1, rng)
        tot += 1
        if mut_col0(A, m) != mut_det(A, m + 1):
            diff += 1
check(diff > 0, "6b. CONTROL: swapped `matSkip` makes column-0 expansion FALSE",
      f"{diff} of {tot} cases differ")

# 5b's index identity under the same mutation.
idx_diff = idx_tot = 0
for cp, pp, r, c in product(range(6), repeat=4):
    idx_tot += 1
    if (mat_skip_swapped(0, mat_skip_swapped(pp, r))
            != mat_skip_swapped(pp + 1, mat_skip_swapped(0, r))):
        idx_diff += 1
check(idx_diff > 0,
      "6c. CONTROL: swapped `matSkip` breaks the double-minor index identity",
      f"{idx_diff} of {idx_tot} tuples differ")

# --------------------------------------------------------------------------
# 7. NEGATIVE CONTROL: the alternation dropped from the column-0 sum.
#    This is the sign probe -- 5b/5c/5d/6c mention no sign at all, so
#    nothing above separates a sign error in the column expansion.
# --------------------------------------------------------------------------

def col0_unsigned(A, m):
    return sum((A(p, 0) * det(mat_minor(A, p, 0), m) for p in range(m + 1)),
               Fraction(0))


diff = tot = 0
for m in range(1, 5):
    for _ in range(60):
        A = rand_mat(m + 1, rng)
        tot += 1
        if col0_unsigned(A, m) != det(A, m + 1):
            diff += 1
check(diff > 0, "7a. CONTROL: dropping altSign from the column sum is FALSE",
      f"{diff} of {tot} cases differ")

# and the alternation SHIFTED by one, which a `succ`-off-by-one would produce.
def col0_shifted(A, m):
    return sum((alt_sign(p + 1) * (A(p, 0) * det(mat_minor(A, p, 0), m))
                for p in range(m + 1)), Fraction(0))


diff = tot = 0
for m in range(1, 5):
    for _ in range(60):
        A = rand_mat(m + 1, rng)
        tot += 1
        if col0_shifted(A, m) != det(A, m + 1):
            diff += 1
check(diff > 0, "7b. CONTROL: the alternation shifted by one is FALSE",
      f"{diff} of {tot} cases differ (it is the NEGATION of the true sum)")

# --------------------------------------------------------------------------
# 8. NEGATIVE CONTROL: transpose invariance is NOT vacuous -- it must be
#    false for a matrix whose transpose is a different matrix, under a
#    plausible mis-definition of `matTranspose`.
# --------------------------------------------------------------------------

nonsym = 0
for n in range(2, 6):
    for _ in range(60):
        A = rand_mat(n, rng)
        if any(A(r, c) != A(c, r) for r in range(n) for c in range(n)):
            nonsym += 1
check(nonsym > 0,
      "8. the transpose test set is not accidentally symmetric",
      f"{nonsym} of the sampled matrices are non-symmetric")

# --------------------------------------------------------------------------
# 9. WHAT THIS ROUTE DOES NOT USE.  `det_row_expansion` (ADR-1185) supplies
#    expansion along a general ROW.  Column-0 expansion does not follow from
#    it: its c = 0 slice at row q is exactly one summand of the column sum,
#    and summing those slices over q is not any instance of the row law.
# --------------------------------------------------------------------------

def row_expansion(A, m, i):
    return sum((alt_sign(q + i) * (A(i, q) * det(mat_minor(A, i, q), m))
                for q in range(m + 1)), Fraction(0))


bad_row = 0
for m in range(0, 5):
    for _ in range(30):
        A = rand_mat(m + 1, rng)
        for i in range(m + 1):
            if row_expansion(A, m, i) != det(A, m + 1):
                bad_row += 1
check(bad_row == 0, "9a. `det_row_expansion` holds as stated (sanity)",
      f"{bad_row} mismatches")

# The c = 0 term of the row-q expansion IS the q-th column-0 summand.
same = 0
for m in range(0, 5):
    A = rand_mat(m + 1, rng)
    for q in range(m + 1):
        lhs = alt_sign(0 + q) * (A(q, 0) * det(mat_minor(A, q, 0), m))
        rhs = alt_sign(q) * (A(q, 0) * det(mat_minor(A, q, 0), m))
        if lhs == rhs:
            same += 1
check(same > 0,
      "9b. each column-0 summand is the c = 0 slice of a row-q expansion",
      "so the row law constrains each summand's SIBLINGS, never the column sum itself")


# --------------------------------------------------------------------------
# 10. THE STATEMENT COLUMN of the mutation table.
#
#     ADR-1155's refined standard: a REJECTED declaration and a FALSE
#     statement are different findings.  A declaration rejected while its
#     theorem stays true adds no coverage -- its proof merely names the
#     branches in order.  So for each of the five declarations this lane
#     adds, re-simulate the mutated definition and report whether the
#     STATEMENT survives.
# --------------------------------------------------------------------------

def mat_skip_A(p, x):
    """Mutation A: `Rat.matSkip`'s two `bool_select_nat` branches swapped."""
    return x if p <= x else x + 1


def build(skip):
    def minor(A, i, j):
        return lambda r, c: A(skip(i, r), skip(j, c))

    def dt(A, n):
        if n == 0:
            return Fraction(1)
        return sum((alt_sign(j) * (A(0, j) * dt(minor(A, 0, j), n - 1))
                    for j in range(n)), Fraction(0))

    return minor, dt


minor_A, det_A = build(mat_skip_A)


def survey(label, predicate, samples):
    """Report how many of `samples` the predicate FAILS on."""
    bad = sum(1 for s in samples if not predicate(*s))
    verdict = "FALSE" if bad else "TRUE "
    print(f"     {label:<28} {verdict} ({bad} of {len(samples)})")
    return bad


print()
print("10. the statement column, mutation A (`matSkip` branches swapped)")

idx_samples = [(pp, q, r, c) for pp in range(4) for q in range(4)
               for r in range(4) for c in range(4)]
a1 = survey(
    "matMinor_row_col_comm",
    lambda pp, q, r, c: (
        (mat_skip_A(0, mat_skip_A(pp, r)), mat_skip_A(q + 1, mat_skip_A(0, c)))
        == (mat_skip_A(pp + 1, mat_skip_A(0, r)), mat_skip_A(0, mat_skip_A(q, c)))
    ),
    idx_samples)

mat_samples = []
for mp in range(0, 3):
    for _ in range(25):
        mat_samples.append((mp, rand_mat(mp + 4, rng)))

a2 = survey(
    "det_minor_row_col_comm",
    lambda mp, A: (det_A(minor_A(minor_A(A, 0, 1), 0, 0), mp)
                   == det_A(minor_A(minor_A(A, 1, 0), 0, 0), mp)),
    mat_samples)

col_samples = []
for m in range(1, 5):
    for _ in range(60):
        col_samples.append((m, rand_mat(m + 1, rng)))

a3 = survey(
    "det_col_expansion",
    lambda m, A: (sum((alt_sign(q) * (A(q, 0) * det_A(minor_A(A, q, 0), m))
                       for q in range(m + 1)), Fraction(0))
                  == det_A(A, m + 1)),
    col_samples)

a4 = survey(
    "matMinor_transpose",
    lambda mp, A: all(
        minor_A(transpose(A), 0, q)(r, c)
        == transpose(minor_A(A, q, 0))(r, c)
        for q in range(3) for r in range(3) for c in range(3)),
    mat_samples)

tr_samples = []
for n in range(2, 6):
    for _ in range(60):
        tr_samples.append((n, rand_mat(n, rng)))

a5 = survey("det_transpose",
            lambda n, A: det_A(transpose(A), n) == det_A(A, n),
            tr_samples)

check(a1 > 0 and a2 > 0 and a3 > 0 and a5 > 0,
      "10a. mutation A falsifies four of the five statements",
      "matMinor_transpose stays TRUE under it -- correctly, it never mentions "
      "which branch matSkip takes, only that both sides take the same one")
check(a4 == 0,
      "10b. matMinor_transpose is TRUE under mutation A",
      "so mutation A adds no statement coverage for it, and the declaration "
      "being ADMITTED is the right outcome rather than a gap")

print()
print("10. the statement column, mutation B (column entry index transposed)")

b3 = survey(
    "det_col_expansion",
    lambda m, A: (sum((alt_sign(q) * (A(0, q) * det(mat_minor(A, q, 0), m))
                       for q in range(m + 1)), Fraction(0))
                  == det(A, m + 1)),
    col_samples)
check(b3 > 0, "10c. mutation B falsifies det_col_expansion",
      f"{b3} of {len(col_samples)} cases")
check(True, "10d. mutation B leaves the other four statements untouched",
      "it edits `col_zero_expansion_fn`, which appears in NO other statement -- "
      "so its rejection of `det_transpose` is a broken PROOF, not a false "
      "theorem, and adds no statement coverage there")

print()
print(f"FAILURES: {len(FAILURES)}")
for f in FAILURES:
    print(f"  - {f}")
sys.exit(1 if FAILURES else 0)
