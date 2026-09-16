; POSITIVE CONTROL for the `smt.macro_finder` ablation (ADR-2127).
;
; The ablation in `z3-macro-ablation.sh` reported `same` on every row. That is
; exactly what a VACUOUS control prints, so the reading is worthless until the
; option is shown to change an outcome somewhere.
;
; This file is the somewhere. With BOTH quantifier engines off
; (`smt.ematching=false smt.mbqi=false`) nothing can use the `forall` except
; the macro finder, which recognises `∀x. f(x) = x + 1` as a definition of `f`
; (`macro_util::is_left_simple_macro`, `macro_util.cpp:177-201`), inlines it,
; and refutes the ground goal. With `smt.macro_finder=false` the `forall` is
; inert and z3 cannot refute.
;
; Expected:  macro_finder=true  -> unsat
;            macro_finder=false -> NOT unsat
;
; If both arms agree here, the ablation's `same` rows say nothing about macros
; and must not be reported as a measurement of them.
(set-logic AUFLIRA)
(declare-fun f (Real) Real)
(declare-fun a () Real)
(assert (forall ((x Real)) (= (f x) (+ x 1.0))))
(assert (not (= (f a) (+ a 1.0))))
(check-sat)
