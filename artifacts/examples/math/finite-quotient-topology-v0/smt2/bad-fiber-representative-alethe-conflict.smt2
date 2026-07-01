; QF_UF quotient-representative conflict for finite-quotient-topology-v0.
;
; The quotient map identifies a and b in the same fiber over p. This artifact
; checks the malformed claim that the two representatives have distinct
; quotient images.
(set-logic QF_UF)
(declare-sort X 0)
(declare-sort Q 0)
(declare-fun a () X)
(declare-fun b () X)
(declare-fun p () Q)
(declare-fun q (X) Q)
(assert (= (q a) p))
(assert (= (q b) p))
(assert (not (= (q a) (q b))))
(check-sat)
