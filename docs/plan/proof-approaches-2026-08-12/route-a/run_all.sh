#!/bin/sh
# Reproduce every computational claim in REPORT.md / proof.tex.
# Pure Python + numpy; no cargo, no solver.  Total runtime ~30s on one core.
set -e
cd "$(dirname "$0")"

echo "############ 1. brute force, b < a  (Theorem 1) ############"
python3 verify_bruteforce.py 10 5 12 blt | tail -6

echo
echo "############ 2. brute force, b > a  (sharpness) ############"
python3 verify_bruteforce.py 6 5 14 bgt | tail -4

echo
echo "############ 3. per-lemma stress tests ############"
python3 verify_lemmas.py 80 14

echo
echo "############ 4. case-tree exhaustiveness audit ############"
python3 verify_casetree.py 7 5 1400 | tail -8

echo
echo "############ 5. Theorem 2 (defect family) ############"
python3 verify_theorem2.py 12 40 8

echo
echo "############ 6. rigidity cross-check ############"
python3 verify_rigidity.py | tail -22

echo
echo "############ 7. bound comparison ############"
python3 compare_bounds.py
