; (push 0) and (pop 0) are no-ops per the SMT-LIB standard and must not
; affect scoping at all.
; check-sat-order: sat unsat
(set-logic QF_LIA)
(declare-fun x () Int)
(push 0)
(assert (> x 0))
(check-sat)
(pop 0)
(assert (< x 0))
(check-sat)
