; Source artifact for finite-k-means-clustering-v0.
; Exact replay gives cluster 0 x-coordinate sum -2 over two points,
; so 2*c0x = -2 and the centroid x-coordinate is -1.
; The malformed row claims c0x = -1/2, represented without division as
; 2*c0x = -1.

(set-logic QF_LRA)

(declare-const c0x Real)

(assert (= (+ (* 2 c0x) 2) 0))
(assert (= (+ (* 2 c0x) 1) 0))

(check-sat)
