; reset-assertions clears the whole assertion stack (and any open scopes)
; but keeps declarations -- a subsequent check-sat sees only what was
; asserted after the reset.
; check-sat-order: unsat sat
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
(reset-assertions)
(assert (> x 100))
(check-sat)
