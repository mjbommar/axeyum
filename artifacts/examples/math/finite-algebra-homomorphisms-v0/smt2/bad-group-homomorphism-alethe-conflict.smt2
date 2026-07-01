; QF_UF bad group-homomorphism conflict for
; finite-algebra-homomorphisms-v0.
;
; The malformed finite map sends 2 to h1, while 1+1=2 in the source table
; and h1+h1=h0 in the codomain table. Homomorphism preservation for the pair
; (1,1) would require phi(1+1)=phi(1)+phi(1), so the fixed table row is
; refuted by pure EUF congruence and transitivity.
(set-logic QF_UF)
(declare-sort G 0)
(declare-sort H 0)
(declare-fun g1 () G)
(declare-fun g2 () G)
(declare-fun h0 () H)
(declare-fun h1 () H)
(declare-fun opG (G G) G)
(declare-fun opH (H H) H)
(declare-fun phi (G) H)
(assert (not (= h0 h1)))
(assert (= (opG g1 g1) g2))
(assert (= (phi g1) h1))
(assert (= (phi g2) h1))
(assert (= (opH (phi g1) (phi g1)) h0))
(assert (= (phi (opG g1 g1)) (opH (phi g1) (phi g1))))
(check-sat)
