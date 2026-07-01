; QF_BV bit-blast conflict for finite-rings-v0.
;
; The malformed two-element table has XOR addition, zero multiplication, and
; claims 1 is a multiplicative identity. On element x=1:
;
;   1 * x = 0
;   x     = 1
;
; A left multiplicative identity would require those values to be equal. This
; artifact records the resulting fixed-width bit-vector contradiction so the
; generated CNF can carry a checked DRAT refutation.
(set-logic QF_BV)
(declare-fun identity_cell () (_ BitVec 1))
(assert (= identity_cell #b0))
(assert (= identity_cell #b1))
(check-sat)
