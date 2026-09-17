; ADR-2143: the LRA twin of 13-shadowed-polarity-lia.smt2 — the same
; push / assert / push / assert-negation / pop / assert shape over the reals.
; check-sat-order: unsat unsat sat
(set-logic QF_LRA)
(declare-const x Real)
(push 1)
(assert (>= x 10.0))
(push 1)
(assert (not (>= x 10.0)))
(check-sat)
(pop 1)
(assert (<= x 0.0))
(check-sat)
(pop 1)
(check-sat)
