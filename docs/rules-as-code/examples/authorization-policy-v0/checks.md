# Checks

## Tenant Isolation

Query: can a cross-tenant request be allowed, even with the admin role?

Expected: `unsat`.

Evidence: checked Bool/QF_LIA fixture
[`tenant-isolation-bool-qf-lia-conflict.smt2`](smt2/tenant-isolation-bool-qf-lia-conflict.smt2).

## Explicit Deny Precedence

Query: can a same-tenant admin export be allowed when an explicit deny is
present?

Expected: `unsat`.

Evidence: checked Bool/QF_LIA fixture
[`explicit-deny-precedence-bool-qf-lia-conflict.smt2`](smt2/explicit-deny-precedence-bool-qf-lia-conflict.smt2).

## Admin Tenant Guard

Query: can the admin override bypass tenant isolation?

Expected: `unsat`.

Evidence: checked Bool/QF_LIA fixture
[`admin-tenant-guard-bool-qf-lia-conflict.smt2`](smt2/admin-tenant-guard-bool-qf-lia-conflict.smt2).

## Version Delta

Query: does policy version 2 intentionally add analyst export for same-tenant
resources?

Expected: `sat`, with replayed witnesses
`analyst_export_v1_denied` and `analyst_export_v2_allowed`.

## Implementation Equivalence

Query: can the formal policy model and executable interpretation disagree on
the bounded role/action slice?

Expected: `unsat`.

Evidence: checked Bool/QF_LIA fixture
[`implementation-equivalence-bool-qf-lia-conflict.smt2`](smt2/implementation-equivalence-bool-qf-lia-conflict.smt2).
