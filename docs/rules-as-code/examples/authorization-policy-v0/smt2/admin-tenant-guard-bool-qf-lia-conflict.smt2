; Bool/QF_LIA admin-tenant-guard check for authorization-policy-v0.
;
; Source clauses:
; - Policy 2(a): requests may be allowed only across equal tenants.
; - Policy 2(d): admin override does not bypass tenant isolation.
;
; This is the explicit admin-override guard row: admin can read/export only
; inside the tenant boundary.
(set-logic QF_LIA)
(declare-const user_tenant Int)
(declare-const resource_tenant Int)
(declare-const same_tenant Bool)
(declare-const admin_role Bool)
(declare-const read_or_export Bool)
(declare-const explicit_deny Bool)
(declare-const allow Bool)
(assert (= user_tenant 1))
(assert (= resource_tenant 2))
(assert (= same_tenant (= user_tenant resource_tenant)))
(assert admin_role)
(assert read_or_export)
(assert (not explicit_deny))
(assert (= allow (and same_tenant admin_role read_or_export (not explicit_deny))))
(assert allow)
(check-sat)
