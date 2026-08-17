; Monotone lower bound: f(0)=0 and f steps by +2, so f(n)>=0 for all n>=0.
(set-logic UFLIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))
(assert (not (forall ((n Int)) (=> (>= n 0) (>= (f n) 0)))))
(check-sat)
