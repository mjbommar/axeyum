(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status unsat)
; STATUS-PROOF: squares mod 4 are [0, 1]; 2 is a quadratic non-residue, so no integer x has x^2 = 2 (mod 4). Asserted x^2 = 4*t + 2, 0<=x<8, t>=0 -> infeasible.
(declare-fun x () Int)
(declare-fun t () Int)

(assert (= (* x x) (+ (* 4 t) 2)))
(assert (and (<= 0 x) (< x 8)))
(assert (>= t 0))
(check-sat)
