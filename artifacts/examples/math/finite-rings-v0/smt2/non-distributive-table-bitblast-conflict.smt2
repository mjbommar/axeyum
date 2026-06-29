; QF_BV bit-blast conflict for finite-rings-v0.
;
; The malformed two-element table has XOR addition and left-projection
; multiplication. On the failing left-distributivity triple (a=1,b=0,c=0):
;
;   a * (b + c)       = 1
;   (a * b) + (a * c) = 0
;
; Distributivity would require those source table cells to be equal. This
; artifact records the resulting fixed-width bit-vector contradiction so the
; generated CNF can carry a checked DRAT refutation.
(set-logic QF_BV)
(declare-fun distributivity_cell () (_ BitVec 1))
(assert (= distributivity_cell #b1))
(assert (= distributivity_cell #b0))
(check-sat)
