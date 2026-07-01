; QF_UF category-equivalence check for category-equivalence-v0.
;
; The source rule treats resident and in_state as the same category for the
; same program. Asking one to receive priority and the other not to receive
; priority is a congruence conflict.
(set-logic QF_UF)
(declare-sort Category 0)
(declare-sort Program 0)
(declare-sort PriorityStatus 0)
(declare-const resident Category)
(declare-const in_state Category)
(declare-const emergency_housing Program)
(declare-const priority PriorityStatus)
(declare-const no_priority PriorityStatus)
(declare-fun priority_review (Category Program) PriorityStatus)
(assert (= resident in_state))
(assert (= (priority_review resident emergency_housing) priority))
(assert (= (priority_review in_state emergency_housing) no_priority))
(assert (not (= priority no_priority)))
(check-sat)
