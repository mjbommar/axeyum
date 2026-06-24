(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status unsat)
; STATUS-PROOF: squares mod 5 are [0, 1, 4]; 2 is a quadratic non-residue, so no integer x has x^2 = 2 (mod 5). Asserted x^2 = 5*t + 2, 0<=x<20, t>=0 -> infeasible.
(declare-fun x () Int)
(declare-fun t () Int)

(assert (= (* x x) (+ (* 5 t) 2)))
(assert (and (<= 0 x) (< x 20)))
(assert (>= t 0))
(check-sat)
