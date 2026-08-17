; Gauss sum: s(n) = 0+1+...+n, so 2*s(n) = n*(n+1) on N.
; Nonlinear step obligation -- included to measure where the route stops.
(set-logic UFNIA)
(set-info :status unsat)
(declare-fun s (Int) Int)
(assert (= (s 0) 0))
(assert (forall ((k Int)) (=> (>= k 0) (= (s (+ k 1)) (+ (s k) (+ k 1))))))
(assert (not (forall ((n Int)) (=> (>= n 0) (= (* 2 (s n)) (* n (+ n 1)))))))
(check-sat)
