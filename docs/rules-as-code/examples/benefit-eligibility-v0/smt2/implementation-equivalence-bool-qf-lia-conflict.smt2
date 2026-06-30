; Bool/QF_LIA bounded implementation-equivalence check for
; benefit-eligibility-v0.
;
; The first pack treats the validator's executable interpretation as a small
; implementation of the same formal rule. This fixture encodes both the rule
; model and implementation formula for the active-threshold slice and asks for
; a mismatch. Since both definitions are source-equivalent, the mismatch query
; is unsatisfiable.
(set-logic QF_LIA)
(declare-const age Int)
(declare-const income Int)
(declare-const standard_threshold Int)
(declare-const veteran_bonus Int)
(declare-const resident Bool)
(declare-const veteran Bool)
(declare-const sanctioned Bool)
(declare-const model_eligible Bool)
(declare-const implementation_eligible Bool)
(assert (= standard_threshold 35000))
(assert (= veteran_bonus 10000))
(assert (= model_eligible
  (and resident
       (>= age 18)
       (not sanctioned)
       (or (<= income standard_threshold)
           (and veteran (<= income (+ standard_threshold veteran_bonus)))))))
(assert (= implementation_eligible
  (and resident
       (>= age 18)
       (not sanctioned)
       (or (<= income standard_threshold)
           (and veteran (<= income (+ standard_threshold veteran_bonus)))))))
(assert (not (= model_eligible implementation_eligible)))
(check-sat)
