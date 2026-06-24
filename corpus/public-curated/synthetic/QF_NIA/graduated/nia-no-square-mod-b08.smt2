(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status unsat)
; STATUS-PROOF: squares mod 8 are [0, 1, 4]; 5 is a quadratic non-residue, so no integer x has x^2 = 5 (mod 8). Asserted x^2 = 8*t + 5, 0<=x<64, t>=0 -> infeasible.
(declare-fun x () Int)
(declare-fun t () Int)

(assert (= (* x x) (+ (* 8 t) 5)))
(assert (and (<= 0 x) (< x 64)))
(assert (>= t 0))
(check-sat)
