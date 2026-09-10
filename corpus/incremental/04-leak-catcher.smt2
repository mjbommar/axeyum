; THE LEAK CATCHER (roadmap item 2.9 exit criterion). An unconstrained
; baseline is sat; a contradictory pair of assertions under one push is
; unsat; popping must restore the unconstrained sat verdict. An
; implementation that fails to drop assertions on `pop` reports the final
; check-sat as unsat instead of sat -- that is exactly the bug this file
; exists to catch.
; check-sat-order: sat unsat sat
(set-logic QF_LIA)
(declare-fun x () Int)
(check-sat)
(push 1)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(pop 1)
(check-sat)
