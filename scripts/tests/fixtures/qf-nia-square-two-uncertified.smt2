; Mutation control for scripts/check-smt-evidence-certified.py.
;
; This is genuinely unsatisfiable over Int, because 2 is not a square. Axeyum's
; exact single-variable quadratic decider reaches the right verdict, but the
; narrower negative-discriminant certificate deliberately declines: D = 8 is
; positive, so excluding integer roots additionally requires perfect-square and
; divisibility reasoning. The certification gate must observe certified=0 here.
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (= (* x x) 2))
(check-sat)
