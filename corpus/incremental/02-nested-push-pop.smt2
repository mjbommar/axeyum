; Nested scopes: only the innermost check is contradictory; both pops must
; restore satisfiability in turn.
; check-sat-order: sat unsat sat sat
(set-logic QF_LIA)
(declare-fun x () Int)
(check-sat)
(push 1)
(assert (> x 0))
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
