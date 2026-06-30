# Expected Results

| Check | Expected | Evidence |
|---|---|---|
| `tenant_isolation` | `unsat` | checked Bool/QF_LIA evidence |
| `explicit_deny_precedence` | `unsat` | checked Bool/QF_LIA evidence |
| `admin_tenant_guard` | `unsat` | checked Bool/QF_LIA evidence |
| `version_delta` | `sat` | replayed witnesses |
| `implementation_equivalence` | `unsat` | checked Bool/QF_LIA evidence |

The checked rows use source-linked SMT-LIB fixtures and the
`rules_as_code_examples` regression. The satisfiable version-delta row stays
on replay because it is an intended policy change, not a proof obligation.
