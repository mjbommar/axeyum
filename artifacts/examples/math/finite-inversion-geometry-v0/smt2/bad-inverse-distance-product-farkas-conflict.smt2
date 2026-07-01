; QF_LRA/Farkas obstruction for finite-inversion-geometry-v0.
; Exact replay computes |p|^2 * |I(p)|^2 = 1 for inversion of (2,1).
(set-logic QF_LRA)
(declare-const squared_radius_product Real)
(assert (= squared_radius_product 1))
(assert (= squared_radius_product 2))
(check-sat)
