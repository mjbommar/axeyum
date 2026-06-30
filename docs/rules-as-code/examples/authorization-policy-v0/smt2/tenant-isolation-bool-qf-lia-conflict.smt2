; Bool/QF_LIA tenant-isolation check for authorization-policy-v0.
;
; Source clauses:
; - Policy 2(a): requests may be allowed only across equal tenants.
; - Policy 2(d): admin override does not bypass tenant isolation.
;
; The fixed request below gives the user admin status but puts the user and
; resource in different tenants. Asking for allow is inconsistent.
(set-logic QF_LIA)
(declare-const user_tenant Int)
(declare-const resource_tenant Int)
(declare-const same_tenant Bool)
(declare-const admin_role Bool)
(declare-const explicit_deny Bool)
(declare-const role_permits Bool)
(declare-const allow Bool)
(assert (= user_tenant 1))
(assert (= resource_tenant 2))
(assert admin_role)
(assert (not explicit_deny))
(assert (= same_tenant (= user_tenant resource_tenant)))
(assert (= role_permits admin_role))
(assert (= allow (and same_tenant role_permits (not explicit_deny))))
(assert allow)
(check-sat)
