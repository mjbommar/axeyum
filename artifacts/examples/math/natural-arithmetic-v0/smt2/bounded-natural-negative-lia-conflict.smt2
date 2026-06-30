; QF_LIA bounded-natural obstruction for natural-arithmetic-v0.
;
; The bounded natural domain 0..7 is represented by 0 <= n <= 7. The rejected
; row asks for a negative element of that same domain, encoded as n < 0. Axeyum
; checks the resulting arithmetic contradiction independently of search.
(set-logic QF_LIA)
(declare-fun n () Int)
(assert (>= n 0))
(assert (<= n 7))
(assert (< n 0))
(check-sat)
