; QF_BV bit-blast conflict for finite-fields-v0.
;
; The composite-modulus row asks whether 2 has an inverse modulo 6. A candidate
; residue is represented by a 3-bit word with `inv < 6`, then zero-extended to
; 6 bits so the product `2 * inv` is exact before taking `bvurem 6`.
; No residue satisfies `(2 * inv) mod 6 = 1`.
(set-logic QF_BV)
(declare-fun inv () (_ BitVec 3))
(assert (bvult inv (_ bv6 3)))
(assert
  (= (bvurem (bvmul (_ bv2 6) ((_ zero_extend 3) inv)) (_ bv6 6))
     (_ bv1 6)))
(check-sat)
