; QF_UF covector-additivity conflict for finite-dual-spaces-v0.
;
; The malformed functional has f(10)=1, f(01)=1, f(11)=1, while 10+01=11
; and 1+1=0 in F2. Additivity would require f(10+01)=f(10)+f(01), so the
; row is refuted by EUF over the fixed table facts.
(set-logic QF_UF)
(declare-sort V 0)
(declare-sort F 0)
(declare-fun zero () F)
(declare-fun one () F)
(declare-fun v10 () V)
(declare-fun v01 () V)
(declare-fun v11 () V)
(declare-fun add_v (V V) V)
(declare-fun add_f (F F) F)
(declare-fun f (V) F)
(assert (not (= zero one)))
(assert (= (add_v v10 v01) v11))
(assert (= (f v10) one))
(assert (= (f v01) one))
(assert (= (f v11) one))
(assert (= (add_f one one) zero))
(assert (= (f (add_v v10 v01)) (add_f (f v10) (f v01))))
(check-sat)
