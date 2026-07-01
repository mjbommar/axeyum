; QF_UF implementation-equivalence gap for category-equivalence-v0.
;
; The model and implementation both respect the same category equivalence. A
; mismatch across equivalent categories for the same program is inconsistent by
; congruence, but this rules/law row is still a proof-gap until the harness
; checks QF_UF/Alethe evidence for rule packs.
(set-logic QF_UF)
(declare-sort Category 0)
(declare-sort Program 0)
(declare-const resident Category)
(declare-const in_state Category)
(declare-const emergency_housing Program)
(declare-fun model_priority (Category Program) Bool)
(declare-fun implementation_priority (Category Program) Bool)
(assert (= resident in_state))
(assert (= (implementation_priority resident emergency_housing)
           (model_priority resident emergency_housing)))
(assert (= (implementation_priority in_state emergency_housing)
           (model_priority in_state emergency_housing)))
(assert (not (= (implementation_priority resident emergency_housing)
                (implementation_priority in_state emergency_housing))))
(check-sat)
