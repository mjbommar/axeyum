(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status unsat)
; STATUS-PROOF: squares mod 5 are [0, 1, 4]; 3 is a quadratic non-residue, so no integer x has x^2 = 3 (mod 5). Asserted x^2 = 5*t + 3, 0<=x<25, t>=0 -> infeasible.
(declare-fun x () Int)
(declare-fun t () Int)

(assert (= (* x x) (+ (* 5 t) 3)))
(assert (and (<= 0 x) (< x 25)))
(assert (>= t 0))
(check-sat)
