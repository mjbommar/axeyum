; QF_BV bit-blast conflict for modular-arithmetic-v0.
;
; The finite replay row checks that 2 has no inverse modulo 6. This artifact
; asks for a fixed-width residue witness:
;
;   0 <= b < 6
;   (2*b) mod 6 = 1
;
; The candidate residue is a 3-bit word. It is zero-extended to 6 bits before
; multiplication so every candidate product 2*b for b in [0,6) is represented
; exactly before the final bvurem by 6.
(set-logic QF_BV)
(declare-fun b () (_ BitVec 3))
(assert (bvult b (_ bv6 3)))
(assert
  (= (bvurem
       (bvmul (_ bv2 6) ((_ zero_extend 3) b))
       (_ bv6 6))
     (_ bv1 6)))
(check-sat)
