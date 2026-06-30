; Bool/QF_LIA phase-out monotonicity check for tax-benefit-arithmetic-v0.
;
; Source clauses:
; - Rule 3(a): household size stays fixed.
; - Rule 3(c): inside the active phase-out band, each income unit above the
;   threshold reduces benefit by 2 units.
; - Rule 3(d): the active threshold stays fixed for this check.
;
; This compact regression checks the linear phase-out slice. The validator
; separately replays the full piecewise formula over the finite sample.
; The bad pattern asks for income2 >= income1 but benefit2 > benefit1.
(set-logic QF_LIA)
(declare-const income1 Int)
(declare-const income2 Int)
(declare-const household_size Int)
(declare-const phase_start Int)
(declare-const base Int)
(declare-const benefit1 Int)
(declare-const benefit2 Int)

(assert (>= income1 0))
(assert (<= income1 80))
(assert (>= income2 0))
(assert (<= income2 80))
(assert (>= income2 income1))
(assert (>= household_size 1))
(assert (<= household_size 3))
(assert (= phase_start 45))
(assert (= base (+ 20 (* 5 (- household_size 1)))))
(assert (> income1 phase_start))
(assert (= benefit1 (- base (* 2 (- income1 phase_start)))))
(assert (= benefit2 (- base (* 2 (- income2 phase_start)))))
(assert (>= benefit1 0))
(assert (>= benefit2 0))

(assert (> benefit2 benefit1))
(check-sat)
