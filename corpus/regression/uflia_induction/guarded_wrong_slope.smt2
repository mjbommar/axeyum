; Right base, wrong slope: f(n) = n fails at n = 1 (f(1) = 2).
(set-logic UFLIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))
(assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) n)))))
(check-sat)
