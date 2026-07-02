; QF_LIA edge-position obstruction for finite-dag-topological-order-v0.
;
; In the malformed order, topology appears before algebra. The edge
; algebra -> topology requires algebra_position < topology_position.
(set-logic QF_LIA)
(declare-fun algebra_position () Int)
(declare-fun topology_position () Int)
(assert (= algebra_position 2))
(assert (= topology_position 1))
(assert (< algebra_position topology_position))
(check-sat)
