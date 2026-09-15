(set-logic AUFDTLIRA)
; POSITIVE CONTROL for `nesting-depth.py`.
;
; ADR-2114 reports "0 of 134 files declares a RECURSIVE datatype", and that is
; the claim the whole INEXACT sizing rests on: a recursive nest has no finite
; unrolling, so a depth expansion would still need a cut. An empty result from a
; detector nobody has shown to fire is indistinguishable from a broken detector.
;
; `lst` is recursive through `cdr`, so `nesting-depth.py` must report
; `depth RECURSIVE 1` on this file and not a number.
(declare-datatypes ((lst 0)) (((nil) (cons (car Int) (cdr lst)))))
(declare-const a lst)
(assert ((_ is cons) a))
(check-sat)
