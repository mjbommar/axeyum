; Push once, check-sat, then assert more in the SAME (still-open) scope and
; check again -- the second check-sat must see the first assertion too.
; check-sat-order: sat unsat
(set-logic QF_LIA)
(declare-fun x () Int)
(push 1)
(assert (> x 0))
(check-sat)
(assert (< x 0))
(check-sat)
(pop 1)
