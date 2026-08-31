#!/usr/bin/env python3
"""ADR-1185: numeric checks of the EXACT summand shape this lane builds.

Not ADR-1155's ``W`` verbatim.  That one writes the inner minor's row as ``0``;
the double expansion needs it to be ``i-1``, because the inner expansion runs
along row ``i-1`` OF THE MINOR.  Re-derived and re-checked here rather than
inherited -- CLAUDE.md's standing rule, and ADR-1155's own first draft of one
check was wrong.

Exits 1 if any claim fails.  Verified to FAIL when ``matSkip``'s branches are
swapped and when the summand's diagonal guard is removed (both are controls
below, and each is asserted to break).
"""

import random
from fractions import Fraction as F

FAILS = []


def check(name, ok, detail=""):
    print(f"{'ok  ' if ok else 'FAIL'} {name}{'  ' + detail if detail else ''}")
    if not ok:
        FAILS.append(name)


# --- the kernel's definitions, simulated -----------------------------------
def ble(a, b):
    return a <= b


def beq(a, b):
    return a == b


def pred(n):
    return n - 1 if n > 0 else 0


def mat_skip(p, x):
    return x + 1 if ble(p, x) else x


def unskip_ble(p, q):
    "the `ble`/`pred` closed form ADR-1155 names"
    return pred(q) if ble(p + 1, q) else q


def unskip_rec(p, q):
    "the DOUBLE Nat.rec form this lane declares (all three rows definitional)"
    if p == 0:
        return pred(q)
    if q == 0:
        return 0
    return 1 + unskip_rec(p - 1, q - 1)


def alt_sign(k):
    return F(-1) ** k


def minor(a, i, j):
    return lambda r, c: a(mat_skip(i, r), mat_skip(j, c))


def det(a, n):
    if n == 0:
        return F(1)
    return sum(alt_sign(j) * (a(0, j) * det(minor(a, 0, j), n - 1)) for j in range(n))


def mk(rows):
    return lambda r, c: F(rows[min(r, len(rows) - 1)][min(c, len(rows[0]) - 1)])


def rand_mat(n, lo=-3, hi=3):
    return mk([[random.randint(lo, hi) for _ in range(n)] for _ in range(n)])


# --- 1. the two `unskip` forms agree ---------------------------------------
BAD = [(p, q) for p in range(8) for q in range(8) if unskip_ble(p, q) != unskip_rec(p, q)]
check("unskip: double-Nat.rec form == ble/pred closed form (64 pairs)", not BAD, str(BAD[:3]))


def unskip_wrong(p, q):
    "NEGATIVE CONTROL: a succ row that forgets its own `succ`"
    if p == 0:
        return pred(q)
    if q == 0:
        return 0
    return unskip_wrong(p - 1, q - 1)


BAD_W = [(p, q) for p in range(8) for q in range(8) if unskip_wrong(p, q) != unskip_rec(p, q)]
check("  (control) a succ row that forgets its `succ` DIFFERS", len(BAD_W) > 0,
      f"{len(BAD_W)} of 64 differ")

# --- 2. the two index lemmas -----------------------------------------------
BAD = [(p, c) for p in range(9) for c in range(9) if unskip_rec(p, mat_skip(p, c)) != c]
check("unskip p (matSkip p c) = c (81 pairs)", not BAD, str(BAD[:3]))
BAD = [(j, k) for j in range(9) for k in range(9) if beq(j, mat_skip(j, k))]
check("beq j (matSkip j k) = false (81 pairs)", not BAD, str(BAD[:3]))
BAD = [(q, c) for q in range(9) for c in range(9) if beq(mat_skip(q, c), q)]
check("beq (matSkip q c) q = false (81 pairs)", not BAD, str(BAD[:3]))


# --- 3. the summand W, and the two identifications -------------------------
def summand(a, ip, m, p, q):
    """`ip` is i' (the expansion row is i = succ i'); the matrix is (m+2)^2."""
    if beq(p, q):
        return F(0)
    u = unskip_rec(p, q)
    return alt_sign(p) * (a(0, p) * (alt_sign(u + ip) * (
        a(ip + 1, q) * det(minor(minor(a, 0, p), ip, u), m))))


def lhs_term(a, ip, m, p, c):
    "expand along row 0 at column p, then that minor along ITS row i' at column c"
    return alt_sign(p) * (a(0, p) * (alt_sign(c + ip) * (
        a(ip + 1, mat_skip(p, c)) * det(minor(minor(a, 0, p), ip, c), m))))


def rhs_term(a, ip, m, q, c):
    "expand along row i = succ i' at column q, then that minor along ITS row 0"
    return alt_sign(q + ip + 1) * (a(ip + 1, q) * (alt_sign(c) * (
        a(0, mat_skip(q, c)) * det(minor(minor(a, ip + 1, q), 0, c), m))))


random.seed(20260831)
BAD_L = BAD_R = TOT = 0
for m_ in range(0, 4):                    # inner dimension; the matrix is (m+2)^2
    n_ = m_ + 2
    for ip_ in range(0, m_ + 1):          # i' with ble i' m
        for _ in range(20):
            A = rand_mat(n_)
            for p_ in range(n_):
                for c_ in range(n_ - 1):
                    TOT += 1
                    if summand(A, ip_, m_, p_, mat_skip(p_, c_)) != lhs_term(A, ip_, m_, p_, c_):
                        BAD_L += 1
                    if summand(A, ip_, m_, mat_skip(p_, c_), p_) != rhs_term(A, ip_, m_, p_, c_):
                        BAD_R += 1
check("W j (matSkip j k) is the LHS summand", BAD_L == 0, f"{BAD_L} of {TOT}")
check("W (matSkip q c) q is the RHS summand", BAD_R == 0, f"{BAD_R} of {TOT}")

# --- 4. the sign identity, in the form the RHS identification needs --------
BAD = 0
for ip_ in range(5):
    for q_ in range(8):
        for c_ in range(8):
            p_ = mat_skip(q_, c_)
            LO = alt_sign(p_) * alt_sign(unskip_rec(p_, q_) + ip_)
            RO = alt_sign(q_ + ip_ + 1) * alt_sign(c_)
            if LO != RO:
                BAD += 1
check("sign identity altSign p * altSign(unskip p q + i') = altSign(q+i'+1) * altSign c'",
      BAD == 0, f"{BAD} mismatches over 320")

# --- 5. the double-minor bridge, POINTWISE ---------------------------------
BAD = TOT5 = 0
for ip_ in range(4):
    for q_ in range(7):
        for c_ in range(7):
            p_ = mat_skip(q_, c_)
            u_ = unskip_rec(p_, q_)
            for r_ in range(6):
                for s_ in range(6):
                    TOT5 += 1
                    LEFT = (mat_skip(0, mat_skip(ip_, r_)), mat_skip(p_, mat_skip(u_, s_)))
                    RIGHT = (mat_skip(ip_ + 1, mat_skip(0, r_)), mat_skip(q_, mat_skip(c_, s_)))
                    if LEFT != RIGHT:
                        BAD += 1
check("double-minor index bridge holds pointwise", BAD == 0, f"{BAD} of {TOT5}")

BAD = [(ip_, r_) for ip_ in range(8) for r_ in range(8)
       if mat_skip(0, mat_skip(ip_, r_)) != mat_skip(ip_ + 1, mat_skip(0, r_))]
check("  row half = matSkip_comm at a=0 (unconditional)", not BAD, str(BAD[:3]))

MISM = []
for q_ in range(8):
    for c_ in range(8):
        p_ = mat_skip(q_, c_)
        u_ = unskip_rec(p_, q_)
        for s_ in range(7):
            if ble(q_, c_):        # p = succ c, so p > q and u = q
                OK = (p_ == c_ + 1 and u_ == q_
                      and mat_skip(c_ + 1, mat_skip(q_, s_)) == mat_skip(q_, mat_skip(c_, s_)))
            else:                  # p = c < q, so u = pred q
                OK = (p_ == c_ and u_ == q_ - 1
                      and mat_skip(c_, mat_skip(q_ - 1, s_)) == mat_skip(q_, mat_skip(c_, s_)))
            if not OK:
                MISM.append((q_, c_, s_))
check("  column half is matSkip_comm in both orientations", not MISM, str(MISM[:3]))

# --- 6. the whole assembly, end to end -------------------------------------
BAD = TOT6 = 0
for m_ in range(0, 4):
    n_ = m_ + 2
    for ip_ in range(0, m_ + 1):
        for _ in range(15):
            A = rand_mat(n_)
            TOT6 += 1
            TARGET = det(A, n_)
            LSUM = sum(sum(summand(A, ip_, m_, p_, q_) for q_ in range(n_)) for p_ in range(n_))
            RSUM = sum(sum(summand(A, ip_, m_, p_, q_) for p_ in range(n_)) for q_ in range(n_))
            ROW_I = sum(alt_sign(q_ + ip_ + 1)
                        * (A(ip_ + 1, q_) * det(minor(A, ip_ + 1, q_), n_ - 1))
                        for q_ in range(n_))
            if not (LSUM == TARGET and RSUM == TARGET and ROW_I == TARGET):
                BAD += 1
check("det A n = Sigma_p Sigma_q W = Sigma_q Sigma_p W = row-i expansion",
      BAD == 0, f"{BAD} of {TOT6}")


def summand_noguard(a, ip, m, p, q):
    "NEGATIVE CONTROL: the same summand with the diagonal guard removed"
    u = unskip_rec(p, q)
    return alt_sign(p) * (a(0, p) * (alt_sign(u + ip) * (
        a(ip + 1, q) * det(minor(minor(a, 0, p), ip, u), m))))


BAD_NC = 0
for m_ in range(1, 4):
    n_ = m_ + 2
    for ip_ in range(0, m_ + 1):
        for _ in range(15):
            A = rand_mat(n_)
            LSUM = sum(sum(summand_noguard(A, ip_, m_, p_, q_) for q_ in range(n_))
                       for p_ in range(n_))
            if LSUM != det(A, n_):
                BAD_NC += 1
check("  (control) removing the `beq p q` guard BREAKS it", BAD_NC > 0, f"{BAD_NC} broken")

# --- 7. the STATEMENT column of the mutation table -------------------------
#
# ADR-1155's standard: a rejected declaration and a false statement are
# DIFFERENT findings, and only the pair is honest.  A declaration whose proof
# breaks under a mutation while its theorem stays TRUE adds no coverage against
# that mutation -- its proof merely names the branches in order.
#
# The mutation is the same one ADR-1135 and ADR-1155 use: `Rat.matSkip`'s two
# `bool_select_nat` branches swapped.  Everything downstream is re-simulated
# against it, `Rat.det` included, because `det` is built on `matSkip` too.


def mat_skip_mut(p, x):
    "matSkip with its branches swapped"
    return x if ble(p, x) else x + 1


def minor_mut(a, i, j):
    return lambda r, c: a(mat_skip_mut(i, r), mat_skip_mut(j, c))


def det_mut(a, n):
    if n == 0:
        return F(1)
    return sum(alt_sign(j) * (a(0, j) * det_mut(minor_mut(a, 0, j), n - 1))
               for j in range(n))


def summand_mut(a, ip, m, p, q):
    if beq(p, q):
        return F(0)
    u = unskip_rec(p, q)
    return alt_sign(p) * (a(0, p) * (alt_sign(u + ip) * (
        a(ip + 1, q) * det_mut(minor_mut(minor_mut(a, 0, p), ip, u), m))))


print()
print("statement column, under the `matSkip` branch swap "
      "(counterexamples out of instances tried):")

ROWS = []


def survey(label, bad, total):
    ROWS.append((label, bad, total))
    verdict = "TRUE (no coverage)" if bad == 0 else f"FALSE ({bad} of {total})"
    print(f"  {label:<26} {verdict}")


survey("unskip_matSkip",
       sum(1 for p_ in range(9) for c_ in range(9)
           if unskip_rec(p_, mat_skip_mut(p_, c_)) != c_), 81)
survey("beq_matSkip",
       sum(1 for j_ in range(9) for k_ in range(9) if beq(j_, mat_skip_mut(j_, k_))), 81)
survey("beq_matSkip_left",
       sum(1 for j_ in range(9) for k_ in range(9) if beq(mat_skip_mut(j_, k_), j_)), 81)

BAD = TOT = 0
for ip_ in range(4):
    for u_ in range(6):
        for v_ in range(6):
            if not ble(u_, v_):
                continue
            for r_ in range(5):
                for c_ in range(5):
                    TOT += 1
                    LEFT = (mat_skip_mut(0, mat_skip_mut(ip_, r_)),
                            mat_skip_mut(u_, mat_skip_mut(v_, c_)))
                    RIGHT = (mat_skip_mut(ip_ + 1, mat_skip_mut(0, r_)),
                             mat_skip_mut(mat_skip_mut(0, v_), mat_skip_mut(u_, c_)))
                    if LEFT != RIGHT:
                        BAD += 1
survey("matMinor_double_comm_lo", BAD, TOT)

BAD = TOT = 0
random.seed(1185)
for _ in range(300):
    m_ = random.randint(0, 2)
    n_ = m_ + 2
    ip_ = random.randint(0, m_)
    A = rand_mat(n_ + 2)
    p_ = random.randint(0, n_ - 1)
    c_ = random.randint(0, n_ - 2)
    TOT += 1
    LHS = summand_mut(A, ip_, m_, p_, mat_skip_mut(p_, c_))
    RHS = alt_sign(p_) * (A(0, p_) * (alt_sign(c_ + ip_) * (
        A(ip_ + 1, mat_skip_mut(p_, c_))
        * det_mut(minor_mut(minor_mut(A, 0, p_), ip_, c_), m_))))
    if LHS != RHS:
        BAD += 1
survey("laplaceSummand_rowZero", BAD, TOT)

BAD = TOT = 0
for _ in range(300):
    m_ = random.randint(0, 2)
    n_ = m_ + 2
    ip_ = random.randint(0, m_)
    A = rand_mat(n_ + 2)
    q_ = random.randint(0, n_ - 1)
    c_ = random.randint(0, n_ - 2)
    TOT += 1
    LHS = summand_mut(A, ip_, m_, mat_skip_mut(q_, c_), q_)
    RHS = alt_sign(q_ + ip_ + 1) * (A(ip_ + 1, q_) * (alt_sign(c_) * (
        A(0, mat_skip_mut(q_, c_))
        * det_mut(minor_mut(minor_mut(A, ip_ + 1, q_), 0, c_), m_))))
    if LHS != RHS:
        BAD += 1
survey("laplaceSummand_rowI", BAD, TOT)

BAD = TOT = 0
for m_ in range(0, 3):
    n_ = m_ + 1
    for i_ in range(0, m_ + 1):
        for _ in range(20):
            A = rand_mat(n_ + 1)
            TOT += 1
            LHS = det_mut(A, n_ + 1)
            RHS = sum(alt_sign(q_ + i_) * (A(i_, q_) * det_mut(minor_mut(A, i_, q_), m_))
                      for q_ in range(n_ + 1))
            if LHS != RHS:
                BAD += 1
survey("det_row_expansion", BAD, TOT)

print("  (unskip_zero/_succ_zero/_succ_succ, unskip_le, unskip_gt,")
print("   ble_flip_of_false, altSign_succ_add, mul_perm4, laplaceSummand_diag")
print("   mention no `matSkip` at all, so all stay TRUE and add no coverage)")

MUT_COVERAGE = sum(1 for _lbl, bad, _tot in ROWS if bad > 0)
check("the mutation is discriminating on at least half the surveyed statements",
      MUT_COVERAGE * 2 >= len(ROWS), f"{MUT_COVERAGE} of {len(ROWS)}")

print()
print(f"FAILURES: {len(FAILS)}" + ("  " + ", ".join(FAILS) if FAILS else ""))
raise SystemExit(1 if FAILS else 0)
