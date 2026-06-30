; QF_BV bit-blast conflict for number-theory-v0.
;
; The quadratic-nonresidue row asks whether any residue x modulo 7 satisfies
; x^2 = 3. A candidate residue is represented by a 3-bit word with x < 7, then
; zero-extended to 6 bits so x*x is exact before taking bvurem 7.
; No residue satisfies x^2 mod 7 = 3.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 3))
(assert (bvult x (_ bv7 3)))
(assert
  (= (bvurem
       (bvmul ((_ zero_extend 3) x) ((_ zero_extend 3) x))
       (_ bv7 6))
     (_ bv3 6)))
(check-sat)
