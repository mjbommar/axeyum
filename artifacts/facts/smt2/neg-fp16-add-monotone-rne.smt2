; Negation of F:fp16-add-monotone-rne. That fact is `open`: axeyum has not
; settled this file, so it carries NO evidence row, and this file is here as the
; reproducible target rather than as a certificate.
;
; Measured 2026-08-14, same machine, release builds:
;   z3 4.13.3        unsat, 30.6s
;   bitwuzla 0.9.1   unsat,  8.3s
;   axeyum           see F:fp16-add-monotone-rne notes. For calibration, the
;                    strictly smaller fp8 E5M2 analogue
;                    (neg-fp8-add-monotone-rne.smt2, same shape, 8-bit operands)
;                    IS decided by axeyum -- unsat-drat, recheck=ok, 25m46s --
;                    and is decided by NEITHER oracle, which cannot read the
;                    format at all.
;
; `fp.leq` is false whenever either operand is NaN, so the antecedent already
; excludes NaN inputs; the two guards exclude NaN RESULTS, i.e. (+oo) + (-oo).
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 5 11))
(declare-const b (_ FloatingPoint 5 11))
(declare-const c (_ FloatingPoint 5 11))
(assert (not (=> (and (fp.leq a b)
                      (not (fp.isNaN (fp.add RNE a c)))
                      (not (fp.isNaN (fp.add RNE b c))))
                 (fp.leq (fp.add RNE a c) (fp.add RNE b c)))))
(check-sat)
