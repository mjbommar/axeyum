(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)
(set-info :status unsat)
; STATUS-PROOF: (x-1)^8 + (y-2)^8 + 1 is a sum of even powers plus 1, hence >= 1 > 0; asserted < 0 -> infeasible.
(declare-fun x () Real)
(declare-fun y () Real)

(assert (< (+ (* (- x 1.0) (- x 1.0) (- x 1.0) (- x 1.0) (- x 1.0) (- x 1.0) (- x 1.0) (- x 1.0)) (* (- y 2.0) (- y 2.0) (- y 2.0) (- y 2.0) (- y 2.0) (- y 2.0) (- y 2.0) (- y 2.0)) 1.0) 0.0))
(check-sat)
