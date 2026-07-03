; Source artifact for finite-k-nearest-neighbors-v0.
; Exact replay gives the squared Euclidean distance from q1 = (1, 1) to
; t4 = (4, 4) as (4-1)^2 + (4-1)^2 = 18. The malformed row claims the
; squared distance is 16.

(set-logic QF_LRA)

(declare-const knn_distance Real)

(assert (= knn_distance 18))
(assert (= knn_distance 16))

(check-sat)
