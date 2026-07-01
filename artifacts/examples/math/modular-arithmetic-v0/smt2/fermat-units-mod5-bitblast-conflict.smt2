; QF_BV bit-blast conflict for modular-arithmetic-v0.
;
; The finite replay row checks that every unit a modulo 5 satisfies
; a^4 = 1. This artifact asks for a fixed-width counterexample:
;
;   0 < a < 5
;   a^4 mod 5 != 1
;
; The residue is a 3-bit word. It is zero-extended to 9 bits before the
; multiplications so the largest listed unit, 4^4 = 256, is represented exactly
; before the final bvurem by 5.
(set-logic QF_BV)
(declare-fun a () (_ BitVec 3))
(assert (bvult a (_ bv5 3)))
(assert (not (= a (_ bv0 3))))
(assert
  (not
    (= (bvurem
         (bvmul
           (bvmul ((_ zero_extend 6) a) ((_ zero_extend 6) a))
           (bvmul ((_ zero_extend 6) a) ((_ zero_extend 6) a)))
         (_ bv5 9))
       (_ bv1 9))))
(check-sat)
