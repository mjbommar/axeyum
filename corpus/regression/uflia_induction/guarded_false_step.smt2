; TRUE BASE, FALSE STEP: f(0)=0 holds but f(1)=2, so f is not identically 0.
; This is the case a base-only check would wrongly accept.
(set-logic UFLIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(assert (= (f 0) 0))
(assert (forall ((k Int)) (=> (>= k 0) (= (f (+ k 1)) (+ (f k) 2)))))
(assert (not (forall ((n Int)) (=> (>= n 0) (= (f n) 0)))))
(check-sat)
