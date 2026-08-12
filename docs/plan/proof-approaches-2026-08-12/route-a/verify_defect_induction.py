"""The combinatorial core of the Rigidity Theorem, brute-forced.

DEFECT INDUCTION.  Let e_c <= 1 for c = 2..k-1, E_1 = 0, E_j = e_2 + ... + e_j,
and suppose e_c = 1 only when E_{c-1} = -1 (mod a).  Then E_j <= 0 for all j.

CONSEQUENCE (M = N+1).  2 E_{k-1} + e_K = 1, with e_K <= 1 and e_K = 1 only when
E_{k-1} = -1 (mod a), is unsatisfiable.  [e_K<=0 => E_{k-1}>=1, contra; e_K=1 =>
E_{k-1}=0 but must be = -1 mod a, absurd for a>=2.]

CONSEQUENCE (M = N).  At M = N no obstruction can occur (a | N, and an
obstruction forces M = -1 mod a), so every e <= 0; with 2E + e_K = 0 that forces
every e_c = 0 and e_K = 0, i.e. the canonical vector.
"""
import sys
from itertools import product

LO = -6  # far below any defect that geometry permits


def main():
    viol = seqs = sat = 0
    for a in range(2, 7):
        for m in range(1, 6):
            for e in product(range(LO, 2), repeat=m):
                E, ok, partial = 0, True, []
                for ej in e:
                    if ej == 1 and (E + 1) % a != 0:
                        ok = False
                        break
                    E += ej
                    partial.append(E)
                if not ok:
                    continue
                seqs += 1
                if any(p > 0 for p in partial):
                    viol += 1
                for eK in range(LO, 2):
                    if eK == 1 and (E + 1) % a != 0:
                        continue
                    if 2 * E + eK == 1:
                        sat += 1
    sat0 = 0
    for a in range(2, 7):
        for m in range(1, 6):
            for e in product(range(LO, 1), repeat=m):
                E = sum(e)
                for eK in range(LO, 1):
                    if 2 * E + eK == 0 and (any(x != 0 for x in e) or eK != 0):
                        sat0 += 1
    print(f"admissible defect sequences examined            : {seqs}")
    print(f"sequences with some E_j > 0 (lemma says 0)      : {viol}")
    print(f"solutions of 2E + e_K = 1  (M=N+1; says 0)      : {sat}")
    print(f"non-canonical 2E + e_K = 0, all e<=0 (says 0)   : {sat0}")
    sys.exit(1 if (viol or sat or sat0) else 0)


if __name__ == "__main__":
    main()
