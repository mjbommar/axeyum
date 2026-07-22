; origin: minimized from SMT-LIB 2024 QF_BVFP
;   20170428-Liew-KLEE/imperial_synthetic_fadd_to_exact_zero_klee_float.x86_64/query.26.smt2
; expected: unsat (confirmed by cvc5 1.3.4 and bitwuzla 0.9.1)
; pins: fp.add exact cancellation under RTN produces -0, never +0
(set-info :status unsat)
(set-logic QF_FP)
(assert
  (not
    (fp.isNegative
      (fp.add roundTowardNegative
        ((_ to_fp 8 24) (_ bv1065353216 32))
        ((_ to_fp 8 24) (_ bv3212836864 32))))))
(check-sat)
