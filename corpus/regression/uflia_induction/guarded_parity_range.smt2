; Parity: p alternates 0,1,0,1,... so p(n) is always 0 or 1 on N.
(set-logic UFLIA)
(set-info :status unsat)
(declare-fun p (Int) Int)
(assert (= (p 0) 0))
(assert (forall ((k Int)) (=> (>= k 0) (= (p (+ k 1)) (- 1 (p k))))))
(assert (not (forall ((n Int)) (=> (>= n 0) (or (= (p n) 0) (= (p n) 1))))))
(check-sat)
