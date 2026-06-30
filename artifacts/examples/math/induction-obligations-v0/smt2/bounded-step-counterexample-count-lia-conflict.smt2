; QF_LIA bounded-induction obstruction for induction-obligations-v0.
;
; Exact finite replay over k = 0..8 computes zero step counterexamples to
; the prefix-sum implication P(k) -> P(k + 1). The malformed row asks for at
; least one bounded step counterexample in the same finite range.
(set-logic QF_LIA)
(declare-fun bad_step_count () Int)
(assert (= bad_step_count 0))
(assert (>= bad_step_count 1))
(check-sat)
