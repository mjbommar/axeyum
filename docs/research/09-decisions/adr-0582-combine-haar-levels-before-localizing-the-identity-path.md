# ADR-0582: Combine Haar levels before localizing the identity path

Status: accepted
Date: 2026-08-21
Index-summary: Replace separate levelwise localization by one sharply priced Haar-weighted identity path

## Context

ADR-0581 factors the sufficient levelwise premise

```text
16 ell^2 F_j(1) <= F_j(global)                         (PL2)
```

along a nested identity path for every retained Haar level `j`.  That route is
valid but unnecessarily separates the retained levels.  The conditional
variance used by the sharp implication to `(REL)` is already their weighted
sum, and every summand is nonnegative.

Put `c=c_0`.  For `0<=i<=c`, define

```text
A_i = sum_(j=c+1)^ell 2^(j-c-1) M_(i,j),               (AP)
```

where `M_(0,j)=F_j(global)` and `M_(i,j)` is the same level-`j`
sibling-difference square mass restricted to parents projecting to the
identity in `E_i`.  Then

```text
A_0 >= A_1 >= ... >= A_c,
A_c = R V_id = R sum_(e above 1) (x_e-S/R)^2.          (AP-END)
```

Thus `A_c` is exactly the ordinary conditional-variance numerator already
reconstructed by the native Haar report.  No triangle inequality across
retained levels is needed.

## Decision

Make `(AP)` the selected positive-square bridge beneath the paper's minimal
one-sided lemma `(REL)`.  Let `U_(ell,n)` be the individual-character Weil
envelope

```text
U_(ell,n) = sum_(j=c+1)^ell 2^(j-c-1) (j-1)^2 2^n.
```

Let `T_(ell,n)` be the largest integral `A_c` allowed by the sharp zero-sum
point-versus-variance comparison.  If `R=2^(ell-c)` and `B_(ell,n)` is the
negative allowance in `(REL)`, this is computed without floating point as

```text
Y_max = floor((R B_(ell,n)^2 - 1)/(2^(2c)(R-1))),
T_(ell,n) = floor(Y_max/R).                             (AP-T)
```

The subtraction of one preserves the strict inequality required by `(REL)`.
Consequently, if at least the least `r` satisfying

```text
2^r T_(ell,n) >= U_(ell,n)                             (AP-HB)
```

of the aggregate path steps obey `2A_i<=A_(i-1)`, then `(REL)` follows.
The analogous three-quarter count is the least `r` satisfying

```text
3^r U_(ell,n) <= 4^r T_(ell,n).                        (AP-3Q)
```

The native `identity_cylinder_aggregate_path_implication` operation computes
both least counts, checks available path depth through `ell=1024`, and spends
the exact translation split at level `2^v_2(n)`.  The exact conditional-
variance report combines the already reconstructed level paths with the Haar
weights, rejects any loss of nesting, and requires its terminal aggregate mass
to equal the direct conditional-variance numerator.

At the first uncovered endpoint the new sharp prices are:

```text
n=401: 18 half steps or 43 three-quarter steps; translation leaves 17.
n=402: 19 half steps or 45 three-quarter steps; translation leaves 18.
```

This strictly improves ADR-0581's stronger price of 20 half steps or 47
three-quarter steps separately on every retained Haar level.

## Evidence

- `one_aggregate_identity_path_is_sufficient_for_rel` checks the exact least
  counts, strict allowance arithmetic, and path-depth availability for both
  endpoint parities through `ell=1024`.
- `exact_identity_energy_paths_are_nested_and_reconstruct_local_mass` requires
  the aggregate terminal mass to equal the independently computed conditional-
  variance numerator on every exact control row.
- `translation_forces_the_first_odd_binomial_identity_split` requires the
  translation-forced equality on the aggregate path as well as on every
  separate retained level.
- The CLI emits the symbolic envelope, sharp terminal allowance, required and
  residual counts, every exact aggregate parent/child mass, and whether either
  finite count closes its row.
- Exact-source fleet controls at commit `e046d1d05` cover both endpoint
  degrees for every `19<=ell<=23`.  All 140 aggregate parent/child comparisons
  satisfy `4A_i<=3A_(i-1)`, while only 69 satisfy the stronger
  `2A_i<=A_(i-1)`.  The odd `ell=23` row has 11 half-balanced steps and thereby
  closes its finite `(REL)` implication; the other nine rows do not close from
  the symbolic Weil envelope.  These are falsification controls only, not
  evidence for a uniform contraction theorem.
- The fact ledger records `(AP-HB)` as conjectured with no proof evidence or
  Autogenesis registration.

## Consequences

- A future theorem may trade energy freely among the retained Haar levels.  It
  no longer needs to prove `(PL2)` or select the same number of contractions on
  each level separately.
- The remaining theorem is still a fixed-cylinder localization statement.
  Neither the exact controls nor the implication checker proves the required
  aggregate contractions.
- The paper continues to state only `(REL)`.  `(AP-HB)` is the current
  strongest internal positive-square route to that lemma, not a replacement
  proof of it.
