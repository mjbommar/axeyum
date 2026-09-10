; check-sat-assuming binds its assumption literals for exactly one query and
; does not retain them -- the final check-sat must be sat even though the
; immediately preceding query (with the same `q`) was unsat.
; Verdicts pinned against z3 4.13.3 (see
; crates/axeyum-solver/tests/smtlib.rs, incremental_scripts_answer_one_verdict_per_check_sat).
; check-sat-order: sat unsat sat sat
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (=> p (> x 10)))
(assert (=> q (< x 0)))
(check-sat-assuming (p))
(check-sat-assuming (p q))
(check-sat-assuming (q))
(check-sat)
