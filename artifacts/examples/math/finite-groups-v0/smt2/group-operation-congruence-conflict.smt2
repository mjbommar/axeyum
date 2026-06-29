; QF_UF group-operation congruence conflict for finite-groups-v0.
;
; A group operation is a binary function. If both operands are equal pairwise,
; the products must be equal by congruence. The final assertion demands unequal
; products, so the query is unsatisfiable in pure EUF.
(set-logic QF_UF)
(declare-sort G 0)
(declare-fun a () G)
(declare-fun b () G)
(declare-fun c () G)
(declare-fun d () G)
(declare-fun mul (G G) G)
(assert (= a b))
(assert (= c d))
(assert (not (= (mul a c) (mul b d))))
(check-sat)
