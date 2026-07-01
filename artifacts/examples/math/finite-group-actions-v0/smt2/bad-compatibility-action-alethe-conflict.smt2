; QF_UF action-compatibility conflict for finite-group-actions-v0.
;
; A group action must satisfy g.(h.x) = (g*h).x. The malformed table keeps
; e.01 = 01 and s.01 = 10, but sends s.10 to 10, so s.(s.01) conflicts with
; (s*s).01 = e.01 = 01.
(set-logic QF_UF)
(declare-sort G 0)
(declare-sort X 0)
(declare-fun e () G)
(declare-fun s () G)
(declare-fun p () X)
(declare-fun q () X)
(declare-fun mul (G G) G)
(declare-fun act (G X) X)
(assert (= (mul s s) e))
(assert (= (act e p) p))
(assert (= (act s p) q))
(assert (= (act s q) q))
(assert (= (act s (act s p)) (act (mul s s) p)))
(assert (not (= p q)))
(check-sat)
