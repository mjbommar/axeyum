; QF_UF antisymmetry conflict for finite-order-lattices-v0.
;
; The malformed relation contains x <= y and y <= x for distinct elements.
; Antisymmetry on the failing pair would require x = y, contradicting x != y.
(set-logic QF_UF)
(declare-sort O 0)
(declare-sort Rel 0)
(declare-fun present () Rel)
(declare-fun x () O)
(declare-fun y () O)
(declare-fun le (O O) Rel)
(assert (= (le x y) present))
(assert (= (le y x) present))
(assert (= x y))
(assert (not (= x y)))
(check-sat)
