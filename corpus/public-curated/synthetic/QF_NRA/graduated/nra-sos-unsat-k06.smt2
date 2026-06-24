(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status unsat)
; STATUS-PROOF: sum of squares (each >= 0) plus 1 is >= 1 > 0 over the reals, asserted < 0 -> infeasible (sum-of-squares positivity).
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)

(assert (< (+ (* x1 x1) (* x2 x2) (* x3 x3) (* x4 x4) (* x5 x5) (* x6 x6) 1.0) 0.0))
(check-sat)
