; QF_UF left-additivity conflict for finite-tensor-products-v0.
;
; The malformed bilinear table has beta(11,1)=00, while 10+01=11 and
; beta(10,1)+beta(01,1)=10+01=11. Left additivity would require these two
; target values to agree, so the row is refuted by EUF over fixed table facts.
(set-logic QF_UF)
(declare-sort L 0)
(declare-sort R 0)
(declare-sort T 0)
(declare-fun l10 () L)
(declare-fun l01 () L)
(declare-fun l11 () L)
(declare-fun r1 () R)
(declare-fun t00 () T)
(declare-fun t10 () T)
(declare-fun t01 () T)
(declare-fun t11 () T)
(declare-fun add_l (L L) L)
(declare-fun add_t (T T) T)
(declare-fun beta (L R) T)
(assert (not (= t00 t11)))
(assert (= (add_l l10 l01) l11))
(assert (= (beta l11 r1) t00))
(assert (= (beta l10 r1) t10))
(assert (= (beta l01 r1) t01))
(assert (= (add_t t10 t01) t11))
(assert (= (beta (add_l l10 l01) r1) (add_t (beta l10 r1) (beta l01 r1))))
(check-sat)
