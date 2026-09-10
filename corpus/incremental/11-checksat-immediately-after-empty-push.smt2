; check-sat immediately after a push with no new assertions yet must equal
; the enclosing scope's verdict -- an empty scope changes nothing.
; check-sat-order: sat sat unsat
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(push 1)
(check-sat)
(assert (< x 0))
(check-sat)
