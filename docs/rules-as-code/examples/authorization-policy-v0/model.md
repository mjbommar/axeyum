# Model

The model is a finite authorization table:

```text
allow =
  same_tenant
  and not explicit_deny
  and role_permits(action, role, policy_version)
```

The finite domains are:

| Dimension | Values |
|---|---|
| tenant | `1`, `2` |
| role | `analyst`, `admin` |
| action | `read`, `export`, `delete` |
| policy version | `1`, `2` |
| explicit deny | `false`, `true` |

Role permits:

| Role | Version | Action | Permit |
|---|---:|---|---|
| analyst | 1 | read | yes |
| analyst | 1 | export | no |
| analyst | 2 | read | yes |
| analyst | 2 | export | yes |
| admin | 1 or 2 | read | yes |
| admin | 1 or 2 | export | yes |
| any | any | delete | no |

The executable replay function in
[`validate-rules-as-code.py`](../../../../scripts/validate-rules-as-code.py)
recomputes the `allow` bit for every witness and every finite sample row.
Checked `unsat` rows additionally use source-linked SMT-LIB fixtures under
[`smt2/`](smt2/).
