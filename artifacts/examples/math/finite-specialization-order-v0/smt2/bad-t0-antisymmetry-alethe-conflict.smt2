; QF_UF antisymmetry conflict for finite-specialization-order-v0.
;
; In the indiscrete two-point topology, x specializes to y and y specializes
; to x. A false T0/antisymmetry claim collapses those distinct points to x = y.
(set-logic QF_UF)
(declare-sort Point 0)
(declare-sort Rel 0)
(declare-fun present () Rel)
(declare-fun x () Point)
(declare-fun y () Point)
(declare-fun specializes (Point Point) Rel)
(assert (= (specializes x y) present))
(assert (= (specializes y x) present))
(assert (= x y))
(assert (not (= x y)))
(check-sat)
