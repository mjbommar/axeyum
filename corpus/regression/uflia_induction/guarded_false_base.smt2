; FALSE BASE: f(0) = 0, not 1, so the claimed closed form fails at n = 0.
; Witness: n = 0. The route must decline.
(set-logic UFLIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))
(assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) (+ (* 2 n) 1))))))
(check-sat)
