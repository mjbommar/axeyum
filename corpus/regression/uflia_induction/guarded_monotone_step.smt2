; Monotonicity: g is non-decreasing on N because each step adds k >= 0.
(set-logic UFLIA)
(set-info :status unsat)
(declare-fun g (Int) Int)
(assert (= (g 0) 1))
(assert (forall ((k Int)) (=> (>= k 0) (= (g (+ k 1)) (+ (g k) k)))))
(assert (not (forall ((n Int)) (=> (>= n 0) (>= (g n) 1)))))
(check-sat)
