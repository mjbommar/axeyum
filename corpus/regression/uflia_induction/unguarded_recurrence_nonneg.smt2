; SOUNDNESS PROBE, function form. The recurrence pins f only for k >= 0, so
; f(-1) is unconstrained and may be negative: the set is SATISFIABLE.
; The base and step obligations over N both discharge, so a route that drops
; the Int/Nat distinction reports `unsat` here.
(set-logic UFLIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))
(assert (not (forall ((n Int)) (>= (f n) 0))))
(check-sat)
