; QF_BV bit-blast conflict for number-theory-v0.
;
; The malformed row claims that 2 is a square root of 2 modulo 7:
;
;   2 * 2 mod 7 = 4
;
; A square-root witness for 2 would require the product to be 2. The product is
; computed at 6-bit width before reducing modulo 7, then constrained to both
; the replayed value and the false target.
(set-logic QF_BV)
(assert
  (= (bvurem (bvmul (_ bv2 6) (_ bv2 6)) (_ bv7 6))
     (_ bv4 6)))
(assert
  (= (bvurem (bvmul (_ bv2 6) (_ bv2 6)) (_ bv7 6))
     (_ bv2 6)))
(check-sat)
