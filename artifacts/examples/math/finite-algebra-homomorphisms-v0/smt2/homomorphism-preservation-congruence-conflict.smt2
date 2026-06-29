; QF_UF homomorphism-preservation congruence conflict for
; finite-algebra-homomorphisms-v0.
;
; If phi preserves a binary operation at (a,b), then congruent source elements
; a2=a and b2=b must preserve the same operation application. The final
; assertion demands the opposite, so the query is unsatisfiable by pure EUF
; congruence and transitivity.
(set-logic QF_UF)
(declare-sort G 0)
(declare-sort H 0)
(declare-fun a () G)
(declare-fun b () G)
(declare-fun a2 () G)
(declare-fun b2 () G)
(declare-fun opG (G G) G)
(declare-fun opH (H H) H)
(declare-fun phi (G) H)
(assert (= a a2))
(assert (= b b2))
(assert (= (phi (opG a b)) (opH (phi a) (phi b))))
(assert (not (= (phi (opG a2 b2)) (opH (phi a2) (phi b2)))))
(check-sat)
