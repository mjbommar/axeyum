# Authorization Policy V0

This pack is a bounded rules-as-code example for authorization policies. It
models tenant isolation, role permits, explicit deny precedence, an admin
override, and one intentional policy-version change.

It reuses the math-resource patterns from:

- finite predicates and Boolean replay;
- finite relations/functions for user-role-resource tables;
- finite order/lattice precedence for explicit deny over permit;
- graph/reachability-style policy isolation boundaries;
- Bool/QF_LIA checked evidence for small unsatisfiable policy obligations.

The source policy is in [source.md](source.md), the formal model is in
[model.md](model.md), checks are described in [checks.md](checks.md), and
machine-readable expectations are in [expected.json](expected.json).

## Trust Boundary

```text
human-authored source policy -> formal finite model -> untrusted solver search
trusted small checking -> witness replay or checked Bool/QF_LIA evidence
```

This pack does not parse Cedar, OPA/Rego, LegalRuleML, Akoma Ntoso, or natural
language law. It demonstrates the shape of a tiny authorization model that can
be audited end to end.

## Validate

From the repository root:

```sh
python3 scripts/validate-rules-as-code.py
cargo test -p axeyum-solver --test rules_as_code_examples authorization_policy
```
