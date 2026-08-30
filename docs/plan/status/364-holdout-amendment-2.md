# Lane 364 — holdout amendment 2 (`natural-parity`, `fermat-numbers`)

<!-- plan-section: lane-status -->

## Status

DONE. Two more held-out families amended out under ADR-0542, both verified
independently before anything was written; both of today's contamination shapes
made detectable; ADR-0695 resolves the evaluation-test tension.

**Blind population: 116 held-out rows across 12 families**, out of 300 rows in
`nursery-v2-extension.json` plus 214 in `nursery-v1.json`. Composition 16 in
v1, 100 in the extension.

```
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1109|settled=0|
  references=0|verdict=PASS                                       REAL EXIT=0
HOLDOUT_CLOSED_EVALUATION|held_out=116|closed_shaped=0|violations=0|
  snapshot_declarations=2383|fixtures=10|verdict=PASS             REAL EXIT=0
```

## Both findings, re-derived

`git log -1 -S` gives the NEWEST commit touching a string, so every date is
from `git log --reverse -S` with the order confirmed by
`git merge-base --is-ancestor`.

**`natural-parity`, all 10 rows, never blind.** Preregistered held-out at
2026-08-29 17:22:14 (`94b3e61ee`). `Nat.even_iff_mod_two_eq_zero` —
`∀ n, Iff (Even n) (Eq (mod n 2) 0)`, which is `F:ml430-nat-even-iff-024826e9`
verbatim, over the `Even n := ∃ k, n = k + k` that is Mathlib's own definition
— admitted 2026-08-29 12:10:13 (`414eef0a2`). Five hours twelve minutes.

*Correction to the brief*: it dated the preregistration 2026-08-30 00:57. That
commit (`6f4b1e62b`) only ADDED the duplicate `preregistered_family_partitions`
block, which is why a `-S` search reports it. The preregistration is
`94b3e61ee`, matching the audit.

The audit's claim about the other nine holds. Seven have an admitted Int
sibling one carrier transport away — `Int.odd_of_mul_left`,
`Int.odd_of_mul_right`, `Int.ediv_two_mul_two_of_even`,
`Int.ediv_two_mul_two_add_one_of_odd`, `Int.even_add`, `Int.even_add_prime`,
`Int.even_add_one` — all wired into `int_prelude.rs:1903-1918`, plus the bridge
`Int.even_iff_nat_abs_even`. Only `add_one_lt_of_even` and `even_div` have
none. And `int_prelude/parity.rs:199-202` states in its own module doc that it
builds the **Nat-level** content of the two `odd_of_mul` rows inline from
`right_distrib`/`left_distrib` "since neither has a home in `nat_prelude` yet"
— hiding place 2, invisible to any name index.

Detail moved to [`../notes/364-holdout-amendment-2.md`](../notes/364-holdout-amendment-2.md).

