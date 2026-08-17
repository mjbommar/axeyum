; SOUNDNESS PROBE, third shape. `forall n:Int. h(n) >= 0` where h is pinned
; only on N. Base and step hold on N; n = -1 is free, so this is SATISFIABLE.
(set-logic UFLIA)
(set-info :status sat)
(declare-fun h (Int) Int)
(assert (= (h 0) 5))
(assert (forall ((k Int)) (=> (>= k 0) (= (h (+ k 1)) (+ (h k) 3)))))
(assert (not (forall ((n Int)) (>= (h n) 5))))
(check-sat)
