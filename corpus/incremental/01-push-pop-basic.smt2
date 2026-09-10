; Baseline scoping: assert outside push, contradict inside a push, pop and
; recheck. The final check-sat must NOT see the popped assertion.
; check-sat-order: sat unsat sat
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 5))
(check-sat)
(push 1)
(assert (< x 3))
(check-sat)
(pop 1)
(check-sat)
