; QF_BV bit-blast conflict for graph-coloring-v0.
;
; A two-coloring of K3 can be represented by one 1-bit color per vertex. For
; every triangle edge, the endpoint colors must differ. Three pairwise distinct
; values cannot exist in a 1-bit domain.
(set-logic QF_BV)
(declare-fun a () (_ BitVec 1))
(declare-fun b () (_ BitVec 1))
(declare-fun c () (_ BitVec 1))
(assert (not (= a b)))
(assert (not (= b c)))
(assert (not (= a c)))
(check-sat)
