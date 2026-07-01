; QF_BV bit-blast conflict for finite-fields-v0.
;
; The prime-field row checks a malformed inverse candidate in F_7:
;
;   element   = 3
;   candidate = 4
;   3 * 4 mod 7 = 5
;
; A multiplicative inverse would require the product to be 1. The product is
; computed at 6-bit width before reducing modulo 7, then constrained to both
; the replayed value and the false inverse target.
(set-logic QF_BV)
(assert
  (= (bvurem (bvmul (_ bv3 6) (_ bv4 6)) (_ bv7 6))
     (_ bv5 6)))
(assert
  (= (bvurem (bvmul (_ bv3 6) (_ bv4 6)) (_ bv7 6))
     (_ bv1 6)))
(check-sat)
