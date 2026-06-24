(set-logic QF_NIA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status unsat)
; STATUS-PROOF: squares mod 7 are [0, 1, 2, 4]; 3 is a quadratic non-residue, so no integer x has x^2 = 3 (mod 7). Asserted x^2 = 7*t + 3, 0<=x<42, t>=0 -> infeasible.
(declare-fun x () Int)
(declare-fun t () Int)

(assert (= (* x x) (+ (* 7 t) 3)))
(assert (and (<= 0 x) (< x 42)))
(assert (>= t 0))
(check-sat)
