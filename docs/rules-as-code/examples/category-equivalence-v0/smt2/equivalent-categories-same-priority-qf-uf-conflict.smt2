; QF_UF category-equivalence check for category-equivalence-v0.
;
; The source rule treats resident and in_state as the same category for the
; same program. Asking one to receive priority and the other not to receive
; priority is a congruence conflict.
(set-logic QF_UF)
(declare-sort Category 0)
(declare-sort Program 0)
(declare-const resident Category)
(declare-const in_state Category)
(declare-const emergency_housing Program)
(declare-fun priority_review (Category Program) Bool)
(assert (= resident in_state))
(assert (priority_review resident emergency_housing))
(assert (not (priority_review in_state emergency_housing)))
(check-sat)
