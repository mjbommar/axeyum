# Lane 150: Fix allowlist validator for logic prelude

## Status: IN PROGRESS

### Findings

All six quarantined facts are real kernel declarations, confirmed from `kernel.environment()`:
1. `Or.resolve_right` - real dotted theorem name
2. `Eq.symm` - real dotted theorem name  
3. `not_not_imp` - real logic prelude declaration (undotted)
4. `not_not_not_intro` - real logic prelude declaration (undotted)
5. `demorgan_or_not_and` - real logic prelude declaration (undotted)
6. `congrFun'` - real logic prelude declaration (undotted)

### Allowlist deficiencies

Missing namespaces in `KERNEL_THEOREM_RE`:
- `And` (And.left, And.right, etc.)
- `Decidable` (Decidable.decide_eq_true_iff, etc.)
- `Eq` (Eq.symm, etc.)
- `Iff` (Iff.mp, Iff.mpr, etc.)
- `Or` (Or.elim, Or.resolve_left, Or.resolve_right, etc.)

Unused in allowlist:
- `Str` - matches no kernel declarations (verified)

Undotted logic prelude names needing decision:
- congrFun', demorgan_or_not_and, demorgan_not_or, demorgan_not_or_converse
- dne_of_em, em_of_dne, em_of_peirce
- mt, noncontradiction, not_not_and, not_not_em, not_not_imp
- not_not_intro, not_not_not, not_not_not_intro
- peirce_of_em

### Next steps

1. Derive namespace list programmatically from kernel
2. Decide on undotted names policy
3. Implement fix with mutation testing
