; reset-assertions issued while a scope is open must clear the open scope
; along with the assertions -- the script never pops afterwards, so any
; leftover scope bookkeeping cannot be masked by a later pop.
; check-sat-order: unsat sat sat
(set-logic QF_LIA)
(declare-fun x () Int)
(push 1)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(reset-assertions)
(check-sat)
(assert (= x 7))
(check-sat)
