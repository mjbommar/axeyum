; Bool/QF_LIA bounded implementation-equivalence check for
; authorization-policy-v0.
;
; The executable replay function and the formal model use the same bounded
; role/action policy for tenant isolation, explicit deny, admin permits, and
; policy-versioned analyst export. Asking for a mismatch is inconsistent.
(set-logic QF_LIA)
(declare-const user_tenant Int)
(declare-const resource_tenant Int)
(declare-const policy_version Int)
(declare-const same_tenant Bool)
(declare-const explicit_deny Bool)
(declare-const analyst_role Bool)
(declare-const admin_role Bool)
(declare-const read_action Bool)
(declare-const export_action Bool)
(declare-const analyst_export_enabled Bool)
(declare-const model_permit Bool)
(declare-const implementation_permit Bool)
(declare-const model_allow Bool)
(declare-const implementation_allow Bool)
(assert (= same_tenant (= user_tenant resource_tenant)))
(assert (= analyst_export_enabled (>= policy_version 2)))
(assert (= model_permit
  (or (and analyst_role read_action)
      (and analyst_role export_action analyst_export_enabled)
      (and admin_role (or read_action export_action)))))
(assert (= implementation_permit
  (or (and analyst_role read_action)
      (and analyst_role export_action analyst_export_enabled)
      (and admin_role (or read_action export_action)))))
(assert (= model_allow (and same_tenant model_permit (not explicit_deny))))
(assert (= implementation_allow (and same_tenant implementation_permit (not explicit_deny))))
(assert (not (= model_allow implementation_allow)))
(check-sat)
