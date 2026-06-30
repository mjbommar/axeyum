; Bool/QF_LIA bounded implementation-equivalence check for
; tax-benefit-arithmetic-v0.
;
; The executable replay function and the formal model use the same active
; phase-out arithmetic slice. The validator separately replays the full
; piecewise formula over the finite sample. Asking for a mismatch is
; inconsistent.
(set-logic QF_LIA)
(declare-const income Int)
(declare-const household_size Int)
(declare-const phase_start Int)
(declare-const model_base Int)
(declare-const implementation_base Int)
(declare-const model_benefit Int)
(declare-const implementation_benefit Int)

(assert (>= income 0))
(assert (<= income 80))
(assert (>= household_size 1))
(assert (<= household_size 3))
(assert (= phase_start 45))
(assert (> income phase_start))

(assert (= model_base (+ 20 (* 5 (- household_size 1)))))
(assert (= implementation_base (+ 20 (* 5 (- household_size 1)))))
(assert (= model_benefit (- model_base (* 2 (- income phase_start)))))
(assert (= implementation_benefit (- implementation_base (* 2 (- income phase_start)))))
(assert (>= model_benefit 0))
(assert (>= implementation_benefit 0))

(assert (not (= model_benefit implementation_benefit)))
(check-sat)
