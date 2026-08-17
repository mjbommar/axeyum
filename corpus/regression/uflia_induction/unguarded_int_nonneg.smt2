; SOUNDNESS PROBE. The universal ranges over Int, NOT over N: n = -1 refutes
; `forall n. n >= 0`, so the negation is TRUE and this set is SATISFIABLE.
; z3 confirms `sat`; axeyum's own front door confirms `sat`.
; A route that discharges base (0 >= 0) and step (k >= 0 -> k+1 >= 0) and then
; concludes `unsat` has silently reinterpreted `forall n:Int` as `forall n:Nat`.
(set-logic LIA)
(set-info :status sat)
(assert (not (forall ((n Int)) (>= n 0))))
(check-sat)
