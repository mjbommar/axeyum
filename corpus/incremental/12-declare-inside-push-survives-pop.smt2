; Declarations are global per the documented solve_smtlib_incremental
; lifecycle (ADR-0009): a symbol declared inside a push scope stays declared
; after the matching pop, even though the assertions made in that scope are
; gone. This pins the documented behavior, not a claim about what a
; reference solver would do with the same script.
; check-sat-order: sat unsat sat
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(push 1)
(declare-fun y () Int)
(assert (< y 0))
(assert (= y x))
(check-sat)
(pop 1)
(assert (= x 5))
(check-sat)
