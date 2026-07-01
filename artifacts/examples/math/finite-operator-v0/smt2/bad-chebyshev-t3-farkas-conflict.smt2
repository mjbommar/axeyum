; QF_LRA Chebyshev-prefix obstruction for finite-operator-v0.
;
; Finite recurrence replay at x=1/2 computes T3=-1 from
; T(n+1)=2*x*T(n)-T(n-1). After shifting by +1, the replayed value is 0 while
; the malformed T3=-1/2 claim requires 1/2.
(set-logic QF_LRA)
(declare-const t3_plus_one Real)
(assert (= t3_plus_one 0))
(assert (= t3_plus_one (/ 1 2)))
(check-sat)
