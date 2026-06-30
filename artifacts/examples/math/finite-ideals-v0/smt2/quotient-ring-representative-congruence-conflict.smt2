; QF_UF quotient-ring representative congruence conflict for finite-ideals-v0.
;
; In Z/6Z/(2), representatives 0 and 2 name the same even coset, while
; representatives 1 and 3 name the same odd coset. Quotient addition must be
; independent of representative choice. The final assertion demands the
; opposite, so pure EUF congruence refutes the row.
(set-logic QF_UF)
(declare-sort R 0)
(declare-sort Q 0)
(declare-fun r0 () R)
(declare-fun r1 () R)
(declare-fun r2 () R)
(declare-fun r3 () R)
(declare-fun quotient (R) Q)
(declare-fun qadd (Q Q) Q)
(assert (= (quotient r0) (quotient r2)))
(assert (= (quotient r1) (quotient r3)))
(assert (not (= (qadd (quotient r0) (quotient r1)) (qadd (quotient r2) (quotient r3)))))
(check-sat)
