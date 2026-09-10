; Three independent push/assert/check/pop cycles, each returning to the same
; base state. A leak that only accumulates after several cycles (e.g. an
; assertion list that keeps growing instead of truncating) surfaces here
; even though a single cycle might not expose it.
; check-sat-order: sat unsat sat unsat sat unsat sat
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(check-sat)
