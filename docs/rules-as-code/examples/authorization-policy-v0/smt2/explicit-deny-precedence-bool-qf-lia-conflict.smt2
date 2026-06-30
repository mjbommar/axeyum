; Bool/QF_LIA explicit-deny precedence check for authorization-policy-v0.
;
; Source clauses:
; - Policy 2(b): admin may export same-tenant resources.
; - Policy 2(c): explicit deny overrides any role permit.
; - Policy 2(d): admin override does not override explicit deny.
;
; The fixed request has same-tenant admin export and an explicit deny. Asking
; for allow is inconsistent.
(set-logic QF_LIA)
(declare-const user_tenant Int)
(declare-const resource_tenant Int)
(declare-const same_tenant Bool)
(declare-const admin_export_permit Bool)
(declare-const explicit_deny Bool)
(declare-const allow Bool)
(assert (= user_tenant 1))
(assert (= resource_tenant 1))
(assert (= same_tenant (= user_tenant resource_tenant)))
(assert admin_export_permit)
(assert explicit_deny)
(assert (= allow (and same_tenant admin_export_permit (not explicit_deny))))
(assert allow)
(check-sat)
