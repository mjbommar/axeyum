; (push 2) opens two nested scopes in one command; (pop 2) must close both
; in one command, not just the innermost.
; check-sat-order: sat unsat sat
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 5))
(check-sat)
(push 2)
(assert (< x 3))
(check-sat)
(pop 2)
(check-sat)
